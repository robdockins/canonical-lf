module Lang.LF.Internal.Basics where

import Lang.LF.Internal.Model
import Lang.LF.Internal.Weak

alphaEqLF :: LFModel f m
          => Weakening γ₁ γ
          -> Weakening γ₂ γ
          -> f γ₁ s
          -> f γ₂ s
          -> Bool
alphaEqLF w₁ w₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak w x'   , _)              -> alphaEqLF (weakTrans w w₁) w₂ x' y
    (_           , Weak w y')      -> alphaEqLF w₁ (weakTrans w w₂) x y'
    (Type        , Type)           -> True
    (KPi _ a k   , KPi _ a' k')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) k k')
    (AType x     , AType x')       -> alphaEqLF w₁ w₂ x x'
    (TyPi _ a1 a2, TyPi _ a1' a2') -> (&&) (alphaEqLF w₁ w₂ a1 a1') (alphaEqLF (weakSkip w₁) (weakSkip w₂) a2 a2')
    (TyConst x   , TyConst x')     -> x == x'
    (TyApp a m   , TyApp a' m')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF w₁ w₂ m m')
    (ATerm x     , ATerm x')       -> alphaEqLF w₁ w₂ x x'
    (Lam _ a m   , Lam _ a' m')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) m m')
    (Var         , Var)            -> weakenVar w₁ B == weakenVar w₂ B
    (UVar u      , UVar u')        -> u == u'
    (Const x     , Const x')       -> x == x'
    (App r m     , App r' m')      -> (&&) (alphaEqLF w₁ w₂ r r') (alphaEqLF w₁ w₂ m m')
    (Unify r1 r2 , Unify r1' r2')  -> (&&) (alphaEqLF w₁ w₂ r1 r1') (alphaEqLF w₁ w₂ r2 r2')
    (And cs      , And cs')        -> and (zipWith (alphaEqLF w₁ w₂) cs cs')
    (Forall _ a c, Forall _ a' c') -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) c c')
    (Exists _ a c, Exists _ a' c') -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) c c')
    (Sigma _ a g , Sigma _ a' g')  -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) g g')
    (Goal m c    , Goal m' c')     -> (&&) (alphaEqLF w₁ w₂ m m') (alphaEqLF w₁ w₂ c c')
    _ -> False


data VarSet :: Ctx * -> * where
  VarSetEmpty :: VarSet γ
  VarSetCons  :: VarSet γ -> !Int -> VarSet (γ ::> b)

mergeVarSet :: VarSet γ -> VarSet γ -> VarSet γ
mergeVarSet VarSetEmpty y = y
mergeVarSet x VarSetEmpty = x
mergeVarSet (VarSetCons v b) (VarSetCons v' b') =
   VarSetCons (mergeVarSet v v') (b + b')

singleVarSet :: Var γ -> VarSet γ
singleVarSet (F f) = VarSetCons (singleVarSet f) 0
singleVarSet B     = VarSetCons VarSetEmpty 1

emptyVarSet :: VarSet γ
emptyVarSet = VarSetEmpty

inVarSet :: VarSet γ -> Var γ -> Bool
inVarSet s v = lookupVarSet s v > 0

lookupVarSet :: VarSet γ -> Var γ -> Int
lookupVarSet VarSetEmpty _ = 0
lookupVarSet (VarSetCons s _) (F v) = lookupVarSet s v
lookupVarSet (VarSetCons _ x) B = x

varCensusLF :: LFModel f m => Var γ -> f γ s -> Int
varCensusLF v tm = lookupVarSet (countCensus tm) v

freeVarLF :: LFModel f m => Var γ -> f γ s -> Bool
freeVarLF v tm = inVarSet (countCensus tm) v

countCensus :: LFModel f m
         => f γ s
         -> VarSet γ
countCensus = foldFree mergeVarSet emptyVarSet singleVarSet

foldFree :: forall f m γ a s
          . LFModel f m
         => (a -> a -> a)
         -> a
         -> (Var γ -> a)
         -> f γ s
         -> a
foldFree merge z = go
 where
  go :: forall γ s. (Var γ -> a) -> f γ s -> a
  go f tm =
    let f' :: forall b. (Var (γ ::> b) -> a)
        f' B     = z
        f' (F x) = f x
     in
    case unfoldLF tm of
      Weak w x -> go (f . weakenVar w) x
      Type -> z
      KPi _ a k -> go f a `merge` go f' k
      AType x -> go f x
      TyPi _ a1 a2 -> go f a1 `merge` go f' a2
      TyConst _ -> z
      TyApp p a -> go f p `merge` go f a
      Lam _ a m -> go f a `merge` go f' m
      Const _ -> z
      ATerm x -> go f x
      App r m -> go f r `merge` go f m
      Var -> f B
      Unify r1 r2 -> go f r1 `merge` go f r2
      UnifyVar _v r -> go f r
      And cs -> foldr merge z $ map (go f) cs
      Forall _ a c -> go f a `merge` go f' c
      Exists _ a c -> go f a `merge` go f' c
      Sigma _ a g -> go f a `merge` go f' g
      Goal m c -> go f m `merge` go f c
      Fail -> z
      UVar _ -> z