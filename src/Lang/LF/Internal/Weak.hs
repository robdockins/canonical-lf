module Lang.LF.Internal.Weak where

import Lang.LF.Internal.Model


weak :: LFModel f m
     => f γ s
     -> f (γ::>b) s
weak = weaken (WeakR WeakRefl)

mapF :: (Var γ -> Var γ') -> Var (γ ::> b) -> Var (γ' ::> b)
mapF _ B = B
mapF f (F x) = F (f x)

weakenVar :: Weakening γ γ'
          -> Var γ
          -> Var γ'
weakenVar WeakRefl  = id
weakenVar (WeakR w) = F . weakenVar w
weakenVar (WeakL w) = weakenVar w . F
weakenVar (WeakSkip w) = mapF (weakenVar w)

-- Smart constructor.  Replaces (WeakSkip WeakRefl) with WeakRefl
-- Correctness follows from functor/identity law:
--    mapF 1 = 1
weakSkip :: Weakening γ γ' -> Weakening (γ::>b) (γ'::>b)
weakSkip WeakRefl = WeakRefl
weakSkip w        = WeakSkip w

weakTrans :: Weakening γ₁ γ₂
          -> Weakening γ₂ γ₃
          -> Weakening γ₁ γ₃

weakTrans w₁ WeakRefl = w₁
 -- by identity
 --    w₁ ∘ 1 = w₁

weakTrans w₁ (WeakR w₂) = WeakR (weakTrans w₁ w₂)
 -- by associativity
 --    w₁ ∘ (w₂ ∘ weak) = (w₁ ∘ w₂) ∘ weak

weakTrans w₁ (WeakL w₂) = weakTrans (WeakR w₁) w₂
 -- by associativity
 --    w₁ ∘ (weak ∘ w₂) = (w₁ ∘ weak) ∘ w₂
 --
 -- Note: This is the only recursive rule that does not decrease both
 --       arguments.  Termination can be proved via lexicographic
 --       order that decreases w₂ then w₁.

weakTrans WeakRefl w₂ = w₂
 -- by identity
 --    1 ∘ w₂ = w₂

weakTrans (WeakL w₁) w₂ = WeakL (weakTrans w₁ w₂)
 -- by associativity
 --  (weak ∘ w₁) ∘ w₂ = weak ∘ (w₁ ∘ w₂)

weakTrans (WeakR w₁) (WeakSkip w₂) = WeakR (weakTrans w₁ w₂)
 -- by naturality of one-step weakening and assocativity
 --   (w₁ ∘ weak) ∘ mapF w₂
 --    = w₁ ∘ (weak ∘ mapF w₂)
 --    = w₁ ∘ (w₂ ∘ weak)
 --    = (w₁ ∘ w₂) ∘ weak

weakTrans (WeakSkip w₁) (WeakSkip w₂) = WeakSkip (weakTrans w₁ w₂)
 -- by functor law for mapF
 --     mapF w₁ ∘ mapF w₂ = mapF (w₁ ∘ w₂)


weakNormalize :: Weakening γ γ'
              -> Weakening γ γ'
weakNormalize WeakRefl             = WeakRefl
weakNormalize (WeakR w)            = WeakR (weakNormalize w)
weakNormalize (WeakSkip w)         = weakSkip (weakNormalize w)
weakNormalize (WeakL WeakRefl)     = WeakR WeakRefl
weakNormalize (WeakL (WeakR w))    = WeakR (weakNormalize (WeakL w))
weakNormalize (WeakL (WeakSkip w)) = WeakR (weakNormalize w)
weakNormalize (WeakL (WeakL w))    = weakNormalize (WeakL (weakNormalize (WeakL w)))

mergeWeak :: Weakening γ₁ γ
          -> Weakening γ₂ γ
          -> (forall γ'. Weakening γ' γ -> Weakening γ₁ γ' -> Weakening γ₂ γ' -> x)
          -> x
mergeWeak WeakRefl w₂ k = k WeakRefl WeakRefl w₂
mergeWeak w₁ WeakRefl k = k WeakRefl w₁ WeakRefl

mergeWeak (WeakR w₁) (WeakR w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k (WeakR w) w₁' w₂'

mergeWeak (WeakSkip w₁) (WeakSkip w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k (weakSkip w) (weakSkip w₁') (weakSkip w₂')

mergeWeak (WeakL w₁) (WeakL w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k w (WeakL w₁') (WeakL w₂')

mergeWeak w₁ w₂ k =
  k WeakRefl w₁ w₂


substWeak :: Subst f γ₂ γ₃
         -> Weakening γ₁ γ₂
         -> (forall γ'
              . Weakening γ' γ₃
             -> Subst f γ₁ γ'
             -> x)
         -> x
substWeak s WeakRefl k = k WeakRefl s
substWeak SubstRefl w k = k w SubstRefl

substWeak s (WeakL w) k =
  substWeak s w $ \w' s' ->
    substWeak s' (WeakR WeakRefl) $ \w'' s'' ->
      k (weakTrans w'' w') s''

substWeak (SubstWeak w s) w' k =
  substWeak s (weakTrans w' w) k

substWeak (SubstSkip s) (WeakR w) k =
  substWeak s w $ \w' s' ->
    k (WeakR w') s'
substWeak (SubstSkip s) (WeakSkip w) k =
  substWeak s w $ \w' s' ->
    k (WeakSkip w') (SubstSkip s')

substWeak (SubstApply s _f) (WeakR w) k =
  substWeak s w k
substWeak (SubstApply s f) (WeakSkip w) k =
  k WeakRefl (SubstApply (SubstWeak w s) f)
