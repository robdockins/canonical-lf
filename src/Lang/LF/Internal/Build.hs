module Lang.LF.Internal.Build where

import Control.Monad (join)
import Data.Proxy
import Data.Set (Set)

import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Solve


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
  autoweakening _ = WeakR (autoweakening (Proxy :: Proxy diff))

type CtxSub γ γ' = (CtxAppend γ (CtxDiff γ γ') ~ γ', AutoWeaken γ (CtxDiff γ γ') γ')

autoweaken :: forall m f s γ γ'. (WFContext γ, CtxSub γ γ', LFModel f m) => f γ s -> f γ' s
autoweaken = weaken (autoweakening (Proxy :: Proxy (CtxDiff γ γ')))


lf_type :: (WFContext γ, LFModel f m) => m (f γ KIND)
lf_type = liftClosed <$> foldLF Type

kPi :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ ::> ()) KIND) -> m (f γ KIND)
kPi nm a k = foldLF =<< (KPi nm <$> a <*> k)

tyPi :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ ::> ()) TYPE) -> m (f γ TYPE)
tyPi nm a1 a2 = foldLF =<< (TyPi nm <$> a1 <*> a2)

infixr 5 ==>
infixl 2 @@

var0 :: (WFContext γ, LFModel f m) => Var γ -> Weakening γ γ' -> m (f γ' ATERM)
var0 (F x) w = var0 x (WeakL w)
var0 B w = weaken w <$> foldLF Var

var :: (WFContext γ, CtxSub γ γ', LFModel f m) => Var γ -> m (f γ' TERM)
var v = autoweaken <$> (foldLF . ATerm =<< var0 v WeakRefl)

uvar :: LFModel f m => LFUVar f -> m (f E TERM)
uvar u = foldLF . ATerm =<< foldLF (UVar u)

λ :: (LFModel f m
   , WFContext γ
   , ?nms :: Set String
   , ?hyps :: Hyps f γ)
  => String
  -> m (f γ TYPE)
  -> (forall b.
         (IsBoundVar b
         , WFContext (γ ::> b)
         , ?nms :: Set String
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
        , WFContext γ
        , ?nms :: Set String
        , ?hyps :: Hyps f γ
        )
     => String
     -> m (f γ TYPE)
     -> (forall b. ( IsBoundVar b
                   , WFContext (γ ::> b)
                   , ?nms :: Set String
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
  (==>) :: (WFContext γ, LFModel f m) => m (f γ TYPE) -> m (f γ s) -> m (f γ s)

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

tyArrow :: (WFContext γ, LFModel f m) => m (f γ TYPE) -> m (f γ TYPE) -> m (f γ TYPE)
tyArrow a1 a2 = do
   a1' <- a1
   a2' <- weaken (WeakL WeakRefl) <$> a2
   foldLF (TyPi "_" a1' a2')

kArrow :: (WFContext γ, LFModel f m) => m (f γ TYPE) -> m (f γ KIND) -> m (f γ KIND)
kArrow a k = do
   a' <- a
   k' <- weaken (WeakL WeakRefl) <$> k
   foldLF (KPi "_" a' k')

tyConst :: (WFContext γ, LFModel f m) => LFTypeConst f -> m (f γ TYPE)
tyConst x = liftClosed <$> (foldLF . AType =<< foldLF (TyConst x))

tyApp :: forall f m γ. (LFModel f m) => m (f γ TYPE) -> m (f γ TERM) -> m (f γ TYPE)
tyApp a m = join (go WeakRefl WeakRefl <$> a <*> m)
 where
  go :: forall γ₁ γ₂
      . Weakening γ₁ γ -> Weakening γ₂ γ -> f γ₁ TYPE -> f γ₂ TERM -> m (f γ TYPE)
  go w1 w2 a' m' =
   case (unfoldLF a', unfoldLF m') of
     (Weak w1' a'', _) -> go (weakTrans w1' w1) w2 a'' m'
     (_, Weak w2' m'') -> go w1 (weakTrans w2' w2) a' m''
     (AType p, _) ->
       mergeWeak (weakNormalize w1) (weakNormalize w2) $ \wcommon w1' w2' ->
         weaken wcommon . atype <$> foldLF (TyApp (weaken w1' p) (weaken w2' m'))
     (TyPi _ _ _, _) ->
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


app :: forall m f γ. (LFModel f m)
    => m (f γ TERM)
    -> m (f γ TERM)
    -> m (f γ TERM)
app x y = join (go WeakRefl WeakRefl <$> x <*> y)
 where
  go :: forall γ₁ γ₂
      . Weakening γ₁ γ -> Weakening γ₂ γ -> f γ₁ TERM -> f γ₂ TERM -> m (f γ TERM)
  go w1 w2 x' y' =
   case (unfoldLF x', unfoldLF y') of
     (Weak w1' x'', _) -> go (weakTrans w1' w1) w2 x'' y'
     (_, Weak w2' y'') -> go w1 (weakTrans w2' w2) x' y''
     (ATerm r, _) ->
        mergeWeak (weakNormalize w1) (weakNormalize w2) $ \wcommon w1' w2' ->
          weaken wcommon . aterm <$> foldLF (App (weaken w1' r) (weaken w2' y'))
     (Lam _ _ m, _) ->
        mergeWeak (weakNormalize w1) (weakNormalize w2) $ \wcommon w1' w2' ->
          weaken wcommon <$>
            let sub = (SubstApply (SubstWeak w1' SubstRefl) (weaken w2' y')) in
            withCurrentSolution (hsubst sub m)

cExists :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) CON))
        -> m (f γ CON)
cExists nm tp f = do
    tp' <- tp
    k   <- f B
    foldLF (Exists nm tp' k)

cForall :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) CON))
        -> m (f γ CON)
cForall nm tp f = do
    tp' <- tp
    k   <- f B
    foldLF (Forall nm tp' k)

sigma   :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) GOAL))
        -> m (f γ GOAL)
sigma nm tp f = do
    tp' <- tp
    g   <- f B
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
       . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
      => m (f γ TERM)
      -> m (f γ TERM)
      -> m (f γ CON)
unify x y = join (unifyTm SubstRefl SubstRefl <$> x <*> y)

{-
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
-}