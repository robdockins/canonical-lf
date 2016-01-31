module Lang.LF.Internal.Weak where

import Lang.LF.Internal.Model


mapF :: (Var γ -> Var γ') -> Var (γ ::> b) -> Var (γ' ::> b)
mapF _ B = B
mapF f (F x) = F (f x)

weakenVar :: Weakening γ γ'
          -> Var γ
          -> Var γ'
weakenVar WeakRefl  = id
weakenVar (WeakLeft w) = F . weakenVar w
weakenVar (WeakRight w) = weakenVar w . F
weakenVar (WeakSkip w) = mapF (weakenVar w)

-- Smart constructor.  Replaces (WeakSkip WeakRefl) with WeakRefl
-- Correctness follows from functor/identity law:
--    mapF 1 = 1
weakSkip :: Weakening γ γ' -> Weakening (γ::>b) (γ'::>b)
weakSkip WeakRefl = WeakRefl
weakSkip w        = WeakSkip w


weakCompose
  :: Weakening γ₂ γ₃
  -> Weakening γ₁ γ₂
  -> Weakening γ₁ γ₃

weakCompose WeakRefl w₁ = w₁
 -- by identity
 --    1 ∘ w₁ = w₁

weakCompose (WeakLeft w₂) w₁ = WeakLeft (weakCompose w₂ w₁)
 -- by associativity
 --    (weak ∘ w₂) ∘ w₁ = weak ∘ (w₂ ∘ w₁)

weakCompose (WeakRight w₂) w₁ = weakCompose w₂ (WeakLeft w₁)
 -- by associativity
 --    (w₂ ∘ weak) ∘ w₁ = w₂ ∘ (weak ∘ w₁)
 --
 -- Note: This is the only recursive rule that does not decrease both
 --       arguments.  Termination can be proved via lexicographic
 --       order that decreases w₂ then w₁.

weakCompose w₂ WeakRefl = w₂
 -- by identity
 --    w₂ ∘ 1 = w₂

weakCompose w₂ (WeakRight w₁) = WeakRight (weakCompose w₂ w₁)
 -- by associativity
 --  w₂ ∘ (w₁ ∘ weak) = (w₂ ∘ w₁) ∘ weak

weakCompose (WeakSkip w₂) (WeakLeft w₁) = WeakLeft (weakCompose w₂ w₁)
 -- by naturality of one-step weakening and assocativity
 --   mapF w₂ ∘ (weak ∘ w₁)
 --    = (mapF w₂ ∘ weak) ∘ w₁
 --    = (weak ∘ w₂) ∘ w₁
 --    = weak ∘ (w₂ ∘ w₁)

weakCompose (WeakSkip w₂) (WeakSkip w₁) = WeakSkip (weakCompose w₂ w₁)
 -- by functor law for mapF
 --     mapF w₂ ∘ mapF w₁ = mapF (w₂ ∘ w₁)


-- A very restricted form of weakening used inside
-- the normalization procedure
data Wk γ γ' where
  WkRefl  :: Wk γ γ
  WkL     :: Wk γ γ' -> Wk γ (γ'::>b)

weakNormalize :: Weakening γ γ'
               -> Weakening γ γ'
weakNormalize w0 = go w0 WkRefl
 where
   wk2weak :: Wk γ γ' -> Weakening γ γ'
   wk2weak WkRefl  = WeakRefl
   wk2weak (WkL w) = WeakLeft (wk2weak w)

   go :: Weakening γ2 γ3
      -> Wk γ1 γ2
      -> Weakening γ1 γ3
   go WeakRefl      wk       = wk2weak wk
   go (WeakLeft w)  wk       = WeakLeft (go w wk)
   go (WeakRight w) wk       = go w (WkL wk)
   go (WeakSkip w)  (WkL wk) = WeakLeft (go w wk)
   go (WeakSkip w)  WkRefl   = weakSkip (go w WkRefl)


mergeWeak :: Weakening γ₁ γ
          -> Weakening γ₂ γ
          -> (forall γ'. Weakening γ' γ -> Weakening γ₁ γ' -> Weakening γ₂ γ' -> x)
          -> x
mergeWeak (WeakLeft w₁) (WeakLeft w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k (WeakLeft w) w₁' w₂'

mergeWeak (WeakSkip w₁) (WeakSkip w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k (weakSkip w) (weakSkip w₁') (weakSkip w₂')

mergeWeak (WeakSkip w₁) (WeakLeft w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k (weakSkip w) (weakSkip w₁') (WeakLeft w₂')

mergeWeak (WeakLeft w₁) (WeakSkip w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k (weakSkip w) (WeakLeft w₁') (weakSkip w₂')

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

substWeak (SubstWeak w0 s) w k =
  substWeak s w $ \w' s' ->
    k (weakCompose w0 w') s'

substWeak (SubstSkip s) (WeakLeft w) k =
  substWeak s w $ \w' s' ->
    k (WeakLeft w') s'
substWeak (SubstSkip s) (WeakSkip w) k =
  substWeak s w $ \w' s' ->
    k (WeakSkip w') (SubstSkip s')

substWeak (SubstApply s _f) (WeakLeft w) k =
  substWeak s w k
substWeak (SubstApply s f) (WeakSkip w) k =
  substWeak s w $ \w' s' ->
    k WeakRefl (SubstApply (SubstWeak w' s') f)

substWeak s (WeakRight w) k =
  substWeak s w $ \w' s' ->
    substWeak s' (WeakLeft WeakRefl) $ \w'' s'' ->
      k (weakCompose w' w'') s''

abstractWeak :: Abstraction f γ₂ γ₃
             -> Weakening γ₁ γ₂
             -> (forall γ'
                  . Weakening γ' γ₃
                 -> Abstraction f γ₁ γ'
                 -> x)
             -> x
abstractWeak AbstractRefl w k = k w AbstractRefl
abstractWeak a WeakRefl k = k WeakRefl a

abstractWeak (AbstractApply a u) w k =
  abstractWeak a w $ \w' a' ->
    k (WeakSkip w') (AbstractApply a' u)

abstractWeak (AbstractSkip a) (WeakSkip w) k =
  abstractWeak a w $ \w' a' ->
    k (WeakSkip w') (AbstractSkip a')

abstractWeak (AbstractSkip a) (WeakLeft w) k =
  abstractWeak a w $ \w' a' ->
    k (WeakLeft w') a'

abstractWeak a (WeakRight w) k =
  abstractWeak a w $ \w' a' ->
    abstractWeak a' (WeakLeft WeakRefl) $ \w'' a'' ->
      k (weakCompose w' w'') a''

absWeaken :: Abstraction f γ γ'
          -> Weakening γ γ'
absWeaken AbstractRefl = WeakRefl
absWeaken (AbstractApply a _) = WeakLeft (absWeaken a)
absWeaken (AbstractSkip a) = WeakSkip (absWeaken a)
