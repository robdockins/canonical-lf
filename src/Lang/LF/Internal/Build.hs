module Lang.LF.Internal.Build where

import           Control.Monad (join)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))


import Lang.LF.Internal.Basics
import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Solve
import Lang.LF.Internal.Weak


type family CtxAppend γ γ' :: Ctx * where
  CtxAppend γ E = γ
  CtxAppend γ (γ' ::> b) = (CtxAppend γ γ') ::> b

type family CtxDiff γ γ' :: Ctx * where
  CtxDiff γ γ = E
  CtxDiff γ (γ' ::> b) = (CtxDiff γ γ') ::> b

class AutoWeaken γ diff γ' where
  autoweakening :: Proxy diff -> Weakening γ γ'

instance AutoWeaken γ E γ where
  autoweakening _ = WeakRefl
instance AutoWeaken γ diff γ' => AutoWeaken γ (diff ::> b) (γ' ::> b) where
  autoweakening _ = WeakLeft (autoweakening (Proxy :: Proxy diff))

type CtxSub γ γ' = (CtxAppend γ (CtxDiff γ γ') ~ γ', AutoWeaken γ (CtxDiff γ γ') γ')

autoweaken :: forall m f s γ γ'. (CtxSub γ γ', LFModel f m) => f γ s -> f γ' s
autoweaken = weaken (autoweakening (Proxy :: Proxy (CtxDiff γ γ')))


lf_type :: (LFModel f m) => m (f γ KIND)
lf_type = foldLF Type

kPi :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ ::> ()) KIND) -> m (f γ KIND)
kPi nm a k = foldLF =<< (KPi nm <$> a <*> k)

tyPi :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ ::> ()) TYPE) -> m (f γ TYPE)
tyPi nm a1 a2 = foldLF =<< (TyPi nm <$> a1 <*> a2)

infixr 5 ==>
infixl 2 @@

mkVar :: LFModel f m => Var γ -> m (f γ TERM)
mkVar v = aterm <$> var0 v WeakRefl

var :: forall f m γ γ'
     . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ', CtxSub γ γ')
    => Var γ
    -> m (f γ' TERM)
var v = do
  var' $ weakenVar (autoweakening (Proxy :: Proxy (CtxDiff γ γ'))) $ v

var' :: forall f m γ
      . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
     => Var γ
     -> m (f γ TERM)
var' v = do
  let (_,_,t) = lookupHyp ?hyps v WeakRefl
  eta_expand WeakRefl t =<< var0 v WeakRefl

uvar :: (LFModel f m, LiftClosed γ)
     => LFUVar f -> m (f γ TERM)
uvar u = do
   t <- uvarType u
   liftClosed <$> inEmptyCtx (eta_expand WeakRefl t =<< foldLF (UVar u))

eta_expand
   :: (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
   => Weakening γ γ'
   -> f γ TYPE
   -> f γ' ATERM
   -> m (f γ' TERM)
eta_expand w ty r =
  case unfoldLF ty of
    Weak w' x ->
      eta_expand (weakCompose w w') x r
    AType _ -> return $ aterm $ r

    TyPi nm t1 t2 ->
      extendCtx nm QPi (weaken w t1) $ do
        v  <- eta_expand (WeakLeft w) t1 =<< foldLF Var
        r' <- foldLF (App (weak r) v)
        z  <- eta_expand (WeakSkip w) t2 r'
        foldLF (Lam nm (weaken w t1) z)

    TyRecord row ->
      eta_expand_record w row r

    -- NB no eta-expansion necessary for rows
    TyRow _ -> return $ aterm r


eta_expand_record
   :: (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
   => Weakening γ γ'
   -> f γ TERM -- row term
   -> f γ' ATERM
   -> m (f γ' TERM)
eta_expand_record w row r =
  case unfoldLF row of
    Weak w' x -> eta_expand_record (weakCompose w w') x r
    Row flds  -> do
      flds' <- Map.traverseWithKey (\k _ -> atomicProject WeakRefl r k) flds
      foldLF (Record flds')
    RowModify _ del ins -> do
      ins' <- Map.traverseWithKey (\k _ -> atomicProject WeakRefl r k) ins
      let del' = Set.union del (Map.keysSet ins)
      foldLF (RecordModify r del' ins')
    ATerm _ -> return $ aterm $ r
    Lam{} -> fail "eta_expand_term : expected row value"
    Record{} -> fail "eta_expand_term : expected row value"
    RecordModify{} -> fail "eta_expand_term : expected row value"


λ :: (LFModel f m
   , ?nms :: Set String
   , ?hyps :: Hyps f γ)
  => String
  -> m (f γ TYPE)
  -> (forall b.
         ( ?nms :: Set String
         , ?hyps :: Hyps f (γ::>b)
         )
         => Var (γ ::> b) -> m (f (γ::>b) TERM))
  -> m (f γ TERM)
λ nm tp f = do
  tp' <- tp
  m   <- extendCtx nm QLam tp' $ f B
  foldLF (Lam nm tp' m)

class LFPi (s::SORT) where
  pi :: ( LFModel f m
        , ?nms :: Set String
        , ?hyps :: Hyps f γ
        )
     => String
     -> m (f γ TYPE)
     -> (forall b. ( ?nms :: Set String
                   , ?hyps :: Hyps f (γ::>b)
                   )
          => Var (γ::>b) -> m (f (γ::>b) s))
     -> m (f γ s)

instance LFPi KIND where
  pi nm tp f = do
    tp' <- tp
    k   <- extendCtx nm QPi tp' $ f B
    foldLF (KPi nm tp' k)

instance LFPi TYPE where
  pi nm tp f = do
    tp' <- tp
    a   <- extendCtx nm QPi tp' $ f B
    foldLF (TyPi nm tp' a)

class LFFunc (s::SORT) where
  (==>) :: (LFModel f m) => m (f γ TYPE) -> m (f γ s) -> m (f γ s)

instance LFFunc KIND where
  (==>) = kArrow
instance LFFunc TYPE where
  (==>) = tyArrow

class LFApplication (s::SORT) where
  (@@) :: (LFModel f m) => m (f γ s) -> m (f γ TERM) -> m (f γ s)

instance LFApplication TYPE where
  (@@) = tyApp
instance LFApplication TERM where
  (@@) = app

tyArrow :: (LFModel f m) => m (f γ TYPE) -> m (f γ TYPE) -> m (f γ TYPE)
tyArrow a1 a2 = do
   a1' <- a1
   a2' <- weak <$> a2
   foldLF (TyPi "x" a1' a2')

kArrow :: (LFModel f m) => m (f γ TYPE) -> m (f γ KIND) -> m (f γ KIND)
kArrow a k = do
   a' <- a
   k' <- weak <$> k
   foldLF (KPi "x" a' k')

tyConst :: (LiftClosed γ, LFModel f m) => LFTypeConst f -> m (f γ TYPE)
tyConst x = liftClosed <$> (foldLF . AType =<< foldLF (TyConst x))

tyApp :: forall f m γ. (LFModel f m) => m (f γ TYPE) -> m (f γ TERM) -> m (f γ TYPE)
tyApp a m = join (go WeakRefl WeakRefl <$> a <*> m)
 where
  go :: forall γ₁ γ₂
      . Weakening γ₁ γ -> Weakening γ₂ γ -> f γ₁ TYPE -> f γ₂ TERM -> m (f γ TYPE)
  go w1 w2 a' m' =
   case (unfoldLF a', unfoldLF m') of
     (Weak w1' a'', _) -> go (weakCompose w1 w1') w2 a'' m'
     (_, Weak w2' m'') -> go w1 (weakCompose w2 w2') a' m''
     (AType p, _) ->
       mergeWeak (weakNormalize w1) (weakNormalize w2) $ \wcommon w1' w2' ->
         weaken wcommon . atype <$> foldLF (TyApp (weaken w1' p) (weaken w2' m'))
     (TyRecord _, _) ->
        fail $ unwords ["Cannot apply terms to record Types"]
     (TyPi _ _ _, _) ->
        fail $ unwords ["Cannot apply terms to Pi Types"]
     (TyRow _ , _) ->
        fail $ unwords ["Cannot apply terms to row Types"]

mkLam :: LFModel f m => String -> Var (γ::>()) -> f γ TYPE -> f (γ::>()) TERM -> m (f γ TERM)
mkLam nm B a m = do
  foldLF (Lam nm a m)
mkLam _nm (F _) _a _m =
  fail "mkLam: Attempting to bind a variable not at the end of the context!"

mkSigma :: LFModel f m => String -> f γ TYPE -> f (γ::>()) GOAL -> m (f γ GOAL)
mkSigma nm a g = do
  foldLF (Sigma nm a g)

tmConst :: (LiftClosed γ, LFModel f m) => LFConst f -> m (f γ TERM)
tmConst x = do
  t <- constType x
  liftClosed <$> inEmptyCtx (eta_expand WeakRefl t =<< foldLF (Const x))

mkRecord :: LFModel f m
         => Map (LFRecordIndex f) (f γ TERM)
         -> m (f γ TERM)
mkRecord flds = foldLF (Record flds)

record :: LFModel f m
       => [(LFRecordIndex f, m (f γ TERM))]
       -> m (f γ TERM)
record = go Map.empty
  where go flds [] = mkRecord flds
        go flds ((nm,m):xs) = do
             x <- m
             case Map.lookup nm flds of
                Nothing -> go (Map.insert nm x flds) xs
                Just _ -> fail $ "Record field referenced more than once: " ++ (show (pretty nm))

extendRecord :: LFModel f m
          => m (f γ TERM)
          -> LFRecordIndex f
          -> m (f γ TERM)
          -> m (f γ TERM)
extendRecord r fld m = do
  r' <- r
  m' <- m
  recordModify r' WeakRefl Set.empty (Map.singleton fld m')

restrictRecord :: LFModel f m
          => m (f γ TERM)
          -> LFRecordIndex f
          -> m (f γ TERM)
restrictRecord r fld = do
  r' <- r
  recordModify r' WeakRefl (Set.singleton fld) Map.empty

updateRecord :: LFModel f m
          => m (f γ TERM)
          -> LFRecordIndex f
          -> m (f γ TERM)
          -> m (f γ TERM)
updateRecord r fld m = do
  r' <- r
  m' <- m
  recordModify r' WeakRefl (Set.singleton fld) (Map.singleton fld m')


rowTy :: LFModel f m
      => [LFRecordIndex f]
      -> m (f γ TYPE)
rowTy = go Set.empty
 where go flds [] = foldLF (TyRow (NegFieldSet flds))
       go flds (nm:xs) =
          if Set.member nm flds then
            fail $ "Record field reverenced more than once: " ++ show (pretty nm)
          else
            go (Set.insert nm flds) xs

recordTy :: LFModel f m
           => m (f γ TERM)
           -> m (f γ TYPE)
recordTy row = foldLF . TyRecord =<< row

row :: LFModel f m
       => [(LFRecordIndex f, m (f γ TYPE))]
       -> m (f γ TERM)
row = go Map.empty
  where go flds [] = foldLF (Row flds)
        go flds ((nm,m):xs) = do
             x <- m
             case Map.lookup nm flds of
                Nothing -> go (Map.insert nm x flds) xs
                Just _ -> fail $ "Record field referenced more than once: " ++ (show (pretty nm))

extendRow :: LFModel f m
          => m (f γ TERM)
          -> LFRecordIndex f
          -> m (f γ TYPE)
          -> m (f γ TERM)
extendRow row fld ty = do
  row' <- row
  ty' <- ty
  rowModify row' WeakRefl Set.empty (Map.singleton fld ty')

restrictRow :: LFModel f m
          => m (f γ TERM)
          -> LFRecordIndex f
          -> m (f γ TERM)
restrictRow row fld = do
  row' <- row
  rowModify row' WeakRefl (Set.singleton fld) Map.empty

updateRow :: LFModel f m
          => m (f γ TERM)
          -> LFRecordIndex f
          -> m (f γ TYPE)
          -> m (f γ TERM)
updateRow row fld ty = do
  row' <- row
  ty' <- ty
  rowModify row' WeakRefl (Set.singleton fld) (Map.singleton fld ty')


atomicProject
    :: forall m f γ γ'
     . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
    => Weakening γ' γ
    -> f γ' ATERM
    -> LFRecordIndex f
    -> m (f γ TERM)
atomicProject w r fld = do
  prj <- foldLF (Project r fld)
  t <- withCurrentSolution $ inferAType w prj
  eta_expand WeakRefl t (weaken w prj)


project :: forall m f γ
         . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
        => m (f γ TERM)
        -> LFRecordIndex f
        -> m (f γ TERM)
project x0 fld = join (go WeakRefl <$> x0)
 where
   go :: forall γ'
       . Weakening γ' γ
      -> f γ' TERM
      -> m (f γ TERM)
   go w x =
     case unfoldLF x of
       Weak w' x' -> go (weakCompose w w') x'
       ATerm r -> atomicProject w r fld
       Lam _ _ _  ->
         fail "Cannot project from lambda terms"
       Row{} ->
         fail "Cannot project from row terms"
       RowModify{} ->
         fail "Cannot project from row terms"

       Record flds ->
         case Map.lookup fld flds of
           Just m -> return (weaken w m)
           Nothing ->
             fail $ "missing record field: " ++ show (pretty fld)
       RecordModify _ _ insMap ->
         case Map.lookup fld insMap of
           Just m -> return (weaken w m)
           Nothing ->
             fail $ "possibly missing record field: " ++ show (pretty fld)

cExists :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. Var (γ::>b) -> m (f (γ::>b) CON))
        -> m (f γ CON)
cExists nm tp f = do
    tp' <- tp
    k   <- f B
    foldLF (Exists nm tp' k)

cForall :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. Var (γ::>b) -> m (f (γ::>b) CON))
        -> m (f γ CON)
cForall nm tp f = do
    tp' <- tp
    k   <- f B
    foldLF (Forall nm tp' k)

sigma   :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. Var (γ::>b) -> m (f (γ::>b) GOAL))
        -> m (f γ GOAL)
sigma nm tp f = do
    tp' <- tp
    g   <- f B
    foldLF (Sigma nm tp' g)

cTrue :: LFModel f m
      => m (f γ CON)
cTrue = foldLF (And [])

conj :: forall f m γ
      . (LFModel f m)
     => [m (f γ CON)]
     -> m (f γ CON)
conj cs = do
   x <- fmap concat . sequence <$> (mapM f =<< sequence cs)
   case x of
     Nothing -> foldLF Fail
     Just xs -> foldLF (And xs)
 where f :: forall γ. f γ CON -> m (Maybe [f γ CON])
       f (unfoldLF -> And xs) = (fmap concat . sequence) <$> mapM f xs
       f (unfoldLF -> Weak w x) = fmap (map (weaken w)) <$> f x
       f (unfoldLF -> Fail)   = return Nothing
       f x = return (Just [x])

goal :: LFModel f m
     => m (f γ TERM)
     -> m (f γ CON)
     -> m (f γ GOAL)
goal m c = foldLF =<< (Goal <$> m <*> c)

goal' :: LFModel f m
     => f γ TERM
     -> f γ CON
     -> m (f γ GOAL)
goal' m c = foldLF (Goal m c)

unify :: forall f m γ
       . (LFModel f m, ?soln :: LFSoln f)
      => m (f γ TERM)
      -> m (f γ TERM)
      -> m (f γ CON)
unify x y = join (unifyTm WeakRefl WeakRefl <$> x <*> y)
