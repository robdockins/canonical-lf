module Lang.LF.Internal.Build where

import Control.Monad (join)
import Data.Proxy
import Data.Set (Set)

import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps

type family CtxAppend γ γ' :: Ctx * where
  CtxAppend γ E = γ
  CtxAppend γ (γ' ::> b) = CtxAppend γ γ' ::> b

type family CtxDiff γ γ' :: Ctx * where
  CtxDiff γ γ = E
  CtxDiff γ (γ' ::> b) = CtxDiff γ γ' ::> b

class (CtxAppend γ diff ~ γ') => AutoWeaken γ diff γ' where
  autoweaken' :: LFModel f m => Proxy diff -> f γ s -> f γ' s

type CtxSub γ γ' = (CtxAppend γ (CtxDiff γ γ') ~ γ', AutoWeaken γ (CtxDiff γ γ') γ')

autoweaken :: forall m f s γ γ'. (CtxSub γ γ', LFModel f m) => f γ s -> f γ' s
autoweaken = autoweaken' (Proxy :: Proxy (CtxDiff γ γ'))

instance AutoWeaken γ E γ where
  autoweaken' _ = id
instance AutoWeaken γ diff γ' => AutoWeaken γ (diff ::> b) (γ' ::> b) where
  autoweaken' _ = weaken . autoweaken' (Proxy :: Proxy diff)



lf_type :: (WFContext γ, LFModel f m) => m (f γ KIND)
lf_type = liftClosed <$> foldLF Type

kPi :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ ::> ()) KIND) -> m (f γ KIND)
kPi nm a k = foldLF =<< (KPi nm <$> a <*> k)

tyPi :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ ::> ()) TYPE) -> m (f γ TYPE)
tyPi nm a1 a2 = foldLF =<< (TyPi nm <$> a1 <*> a2)

infixr 5 ==>
infixl 2 @@

var0 :: LFModel f m => Var γ -> (f γ ATERM -> f γ' ATERM) -> m (f γ' ATERM)
var0 (F x) w = var0 x (w . weaken)
var0 (B b) w = w <$> foldLF (Var b)

var :: (CtxSub γ γ', LFModel f m) => Var γ -> m (f γ' TERM)
var v = autoweaken <$> (foldLF . ATerm =<< var0 v id)

uvar :: LFModel f m => LFUVar f -> m (f E TERM)
uvar u = foldLF . ATerm =<< foldLF (UVar u)

λ :: (LFModel f m)
  => String
  -> m (f γ TYPE)
  -> (forall b. IsBoundVar b => Var (γ ::> b) -> m (f (γ::>b) TERM))
  -> m (f γ TERM)
λ nm tp f = do
  tp' <- tp
  m   <- f (B ())
  foldLF (Lam nm tp' m)

class LFPi (s::SORT) where
  pi :: LFModel f m
     => String
     -> m (f γ TYPE)
     -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) s))
     -> m (f γ s)

instance LFPi KIND where
  pi nm tp f = do
    tp' <- tp
    k   <- f (B ())
    foldLF (KPi nm tp' k)

instance LFPi TYPE where
  pi nm tp f = do
    tp' <- tp
    a   <- f (B ())
    foldLF (TyPi nm tp' a)

class LFFunc (s::SORT) where
  (==>) :: LFModel f m => m (f γ TYPE) -> m (f γ s) -> m (f γ s)

instance LFFunc KIND where
  (==>) = kArrow
instance LFFunc TYPE where
  (==>) = tyArrow

class LFApplication (s::SORT) where
  (@@) :: (WFContext γ, LFModel f m) => m (f γ s) -> m (f γ TERM) -> m (f γ s)

instance LFApplication TYPE where
  (@@) = tyApp
instance LFApplication TERM where
  (@@) = app

tyArrow :: LFModel f m => m (f γ TYPE) -> m (f γ TYPE) -> m (f γ TYPE)
tyArrow a1 a2 = do
   a1' <- a1
   a2' <- weaken <$> a2
   foldLF (TyPi "_" a1' a2')

kArrow :: LFModel f m => m (f γ TYPE) -> m (f γ KIND) -> m (f γ KIND)
kArrow a k = do
   a' <- a
   k' <- weaken <$> k
   foldLF (KPi "_" a' k')

tyConst :: (WFContext γ, LFModel f m) => LFTypeConst f -> m (f γ TYPE)
tyConst x = liftClosed <$> (foldLF . AType =<< foldLF (TyConst x))

tyApp :: forall f m γ. LFModel f m => m (f γ TYPE) -> m (f γ TERM) -> m (f γ TYPE)
tyApp a m = join (go1 <$> a <*> m)
 where
  go1 :: forall γ. f γ TYPE -> f γ TERM -> m (f γ TYPE)
  go1 a' m' =
   case (unfoldLF a', unfoldLF m') of
     (Weak a'', Weak m'') -> weaken <$> go1 a'' m''
     _ -> go2 a' m' id

  go2 :: forall γ γ'. f γ TYPE -> f γ' TERM -> (f γ ATYPE -> f γ' ATYPE) -> m (f γ' TYPE)
  go2 a' m' w =
   case unfoldLF a' of
     Weak a'' -> go2 a'' m' (w . weaken)
     AType p -> foldLF . AType =<< foldLF (TyApp (w p) m')
     TyPi _ _ _ -> do
        fail $ unwords ["Cannot apply terms to Pi Types"]


mkLam :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ::>()) TERM) -> m (f γ TERM)
mkLam nm a m = do
  a' <- a
  m' <- m
  foldLF (Lam nm a' m')

mkSigma :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ::>()) GOAL) -> m (f γ GOAL)
mkSigma nm a g = do
  a' <- a
  g' <- g
  foldLF (Sigma nm a' g')

tmConst :: (WFContext γ, LFModel f m) => LFConst f -> m (f γ TERM)
tmConst x = liftClosed <$> (foldLF . ATerm =<< foldLF (Const x))


app :: forall m f γ. (WFContext γ, LFModel f m)
    => m (f γ TERM)
    -> m (f γ TERM)
    -> m (f γ TERM)
app x y = join (go1 <$> x <*> y)
 where
  go1 :: forall γ. WFContext γ => f γ TERM -> f γ TERM -> m (f γ TERM)
  go1 x' y' =
   case (unfoldLF x', unfoldLF y') of
     (Weak x'', Weak y'') -> weaken <$> go1 x'' y''
     _ -> go2 x' y' id SubstRefl

  go2 :: forall γ γ'. WFContext γ'
                   => f γ TERM
                   -> f γ' TERM
                   -> (forall s. f γ s -> f γ' s)
                   -> (Subst m f γ γ')
                   -> m (f γ' TERM)
  go2 x' y' w s =
   case unfoldLF x' of
     Weak x''  -> go2 x'' y' (w . weaken) (SubstWeak s)
     ATerm r   -> foldLF . ATerm =<< foldLF (App (w r) y')
     Lam _ _ m -> withCurrentSolution (hsubst (SubstApply s (\_ -> return y')) m)

cExists :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) CON))
        -> m (f γ CON)
cExists nm tp f = do
    tp' <- tp
    k   <- f (B ())
    foldLF (Exists nm tp' k)

cForall :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) CON))
        -> m (f γ CON)
cForall nm tp f = do
    tp' <- tp
    k   <- f (B ())
    foldLF (Forall nm tp' k)

sigma   :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) GOAL))
        -> m (f γ GOAL)
sigma nm tp f = do
    tp' <- tp
    g   <- f (B ())
    foldLF (Sigma nm tp' g)

cTrue :: LFModel f m
      => m (f γ CON)
cTrue = foldLF (And [])

conj :: forall f m γ
      . (WFContext γ, LFModel f m)
     => [m (f γ CON)]
     -> m (f γ CON)
conj cs = do
   x <- fmap concat . sequence <$> (mapM f =<< sequence cs)
   case x of
     Nothing -> liftClosed <$> foldLF Fail
     Just xs -> foldLF (And xs)
 where f :: forall γ. f γ CON -> m (Maybe [f γ CON])
       f (unfoldLF -> And xs) = (fmap concat . sequence) <$> mapM f xs
       f (unfoldLF -> Weak x) = fmap (map weaken) <$> f x
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
       . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
      => m (f γ TERM)
      -> m (f γ TERM)
      -> m (f γ CON)
unify x y = join (unifyTm SubstRefl SubstRefl <$> x <*> y)


unifyTm :: forall f m γ₁ γ₂ γ
      . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
     => (Subst m f γ₁ γ)
     -> (Subst m f γ₂ γ)
     -> f γ₁ TERM
     -> f γ₂ TERM
     -> m (f γ CON)
unifyTm s₁ s₂ x y =
   case (unfoldLF x, unfoldLF y) of
     (Weak x', _) -> unifyTm (SubstWeak s₁) s₂ x' y
     (_, Weak y') -> unifyTm s₁ (SubstWeak s₂) x y'
     (ATerm r1, ATerm r2) -> do
         let res = unifyATm s₁ s₂ r1 r2
         case res of
           UnifyDecompose m -> do
             x <- m
             case x of
               Nothing -> liftClosed <$> foldLF Fail
               Just cs -> foldLF (And cs)
           UnifyDefault ->
             foldLF =<< Unify <$> hsubst s₁ r1 <*> hsubst s₂ r2
           UnifySolve u m ->
             foldLF =<< Unify <$> (liftClosed <$> foldLF (UVar u)) <*> m

     (Lam nm a1 m1, Lam _ a2 m2) -> do
        cty <- unifyTy s₁ s₂ a1 a2
        c <- unifyTm (SubstSkip s₁) (SubstSkip s₂) m1 m2
        c' <- foldLF =<< Forall nm <$> hsubst s₁ a1 <*> return c
        conj [return cty, return c']
     _ -> fail "Attempting to unify LF terms with unequal types"

unifyTy :: forall f m γ₁ γ₂ γ
      . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
     => (Subst m f γ₁ γ)
     -> (Subst m f γ₂ γ)
     -> f γ₁ TYPE
     -> f γ₂ TYPE
     -> m (f γ CON)
unifyTy s₁ s₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak x', _) -> unifyTy (SubstWeak s₁) s₂ x' y
    (_, Weak y') -> unifyTy s₁ (SubstWeak s₂) x y'
    (TyPi nm a1 a2, TyPi _ a1' a2') -> do
      conj [ unifyTy s₁ s₂ a1 a1'
           , do c <- unifyTy (SubstSkip s₁) (SubstSkip s₂) a2 a2'
                a1' <- hsubst s₁ a1
                foldLF (Forall nm a1' c)
           ]
    (AType p1, AType p2) -> unifyATy s₁ s₂ p1 p2
    _ -> fail "Attempting to unify LF types of different kinds"

unifyATy :: forall f m γ₁ γ₂ γ
      . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
     => (Subst m f γ₁ γ)
     -> (Subst m f γ₂ γ)
     -> f γ₁ ATYPE
     -> f γ₂ ATYPE
     -> m (f γ CON)
unifyATy s₁ s₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak x', _) -> unifyATy (SubstWeak s₁) s₂ x' y
    (_, Weak y') -> unifyATy s₁ (SubstWeak s₂) x y'
    (TyConst c1, TyConst c2)
      | c1 == c2  -> foldLF (And [])
    (TyApp p1 m1, TyApp p2 m2) -> do
      conj [ unifyATy s₁ s₂ p1 p2
           , unifyTm  s₁ s₂ m1 m2
           ]
    _ -> liftClosed <$> foldLF Fail

cAnd' :: LFModel f m
      => f γ CON
      -> m (Maybe [f γ CON])
      -> m (Maybe [f γ CON])
cAnd' c cs =
  case unfoldLF c of
    Fail   -> return Nothing
    And xs -> fmap (fmap (xs++)) cs
    _      -> fmap (fmap (c:)) cs

data UnifyResult f m γ
  = UnifyDefault
  | UnifyDecompose (m (Maybe [f γ CON]))
  | UnifySolve (LFUVar f) (m (f γ ATERM))

unifyATm :: forall f m γ₁ γ₂ γ
      . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
     => (Subst m f γ₁ γ)
     -> (Subst m f γ₂ γ)
     -> f γ₁ ATERM
     -> f γ₂ ATERM
     -> UnifyResult f m γ
unifyATm s₁ s₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak x', _) -> unifyATm (SubstWeak s₁) s₂ x' y
    (_, Weak y') -> unifyATm s₁ (SubstWeak s₂) x y'
    (Const c₁, Const c₂)
       | c₁ == c₂  -> UnifyDecompose (return (Just []))
       | otherwise -> UnifyDecompose (return Nothing)
    (UVar u, UVar v)
       | u == v -> UnifyDecompose (return (Just []))
    (UVar u, _)
       | Just x' <- lookupUVar Proxy u ?soln -> UnifyDecompose $ do
           c <- unifyTm s₁ s₂ x' (aterm y)
           return (Just [c])
    (_, UVar u)
       | Just y' <- lookupUVar Proxy u ?soln -> UnifyDecompose $ do
           c <- unifyTm s₁ s₂ (aterm x) y'
           return (Just [c])
    (UVar u, _) -> do
       UnifySolve u (hsubst s₂ y)
    (_, UVar u) -> do
       UnifySolve u (hsubst s₁ x)
    (App r₁ m₁, App r₂ m₂) ->
       let res = unifyATm s₁ s₂ r₁ r₂ in
       case res of
         UnifyDefault      -> UnifyDefault
         UnifyDecompose xs -> UnifyDecompose $ do
             cm <- unifyTm s₁ s₂ m₁ m₂
             cAnd' cm xs
         UnifySolve _ _ ->
           error "unifyATm: higher-order unification not yet implemented"

    _ -> UnifyDefault


underGoal :: forall f m γ
           . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ, WFContext γ, ?soln :: LFSoln f)
          => f γ GOAL
          -> (forall γ'
              . (?nms :: Set String, ?hyps :: Hyps f γ', WFContext γ')
             => (forall s. f γ s -> f γ' s)
             -> f γ' TERM
             -> f γ' CON
             -> m (f γ' GOAL))
          -> m (f γ GOAL)
underGoal g0 cont = go id SubstRefl g0
 where
   go :: forall γ₁ γ₂
       . (?nms :: Set String, ?hyps :: Hyps f γ₂, WFContext γ₂)
      => (forall s. f γ s -> f γ₂ s)
      -> Subst m f γ₁ γ₂
      -> f γ₁ GOAL
      -> m (f γ₂ GOAL)
   go w sub g =
     case unfoldLF g of
       Weak x -> go w (SubstWeak sub) x
       Goal m c -> join (cont w <$> hsubst sub m <*> hsubst sub c)
       Sigma nm a g' -> do
         a'  <- hsubst sub a
         g'' <- extendCtx nm QSigma a' $
                    go (weaken . w) (SubstSkip sub) g'
         foldLF (Sigma nm a' g'')


underGoal' :: forall f m γ
           . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ, WFContext γ)
          => f γ GOAL
          -> (forall γ'
              . (?nms :: Set String, ?hyps :: Hyps f γ', WFContext γ')
             => f γ' TERM
             -> f γ' CON
             -> m (f γ' GOAL))
          -> m (f γ GOAL)
underGoal' g0 cont = go g0
 where
   go :: forall γ'
       . (?nms :: Set String, ?hyps :: Hyps f γ', WFContext γ')
      => f γ' GOAL
      -> m (f γ' GOAL)
   go g =
     case unfoldLF g of
       Weak x -> weaken <$> (weakenCtx $ go x)
       Goal m c -> cont m c
       Sigma nm a g' -> do
         g'' <- extendCtx nm QSigma a $ go g'
         foldLF (Sigma nm a g'')
