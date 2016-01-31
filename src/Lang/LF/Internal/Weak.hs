module Lang.LF.Internal.Weak where

import Lang.LF.Internal.Model


mapF :: (Var γ -> Var γ') -> Var (γ ::> b) -> Var (γ' ::> b)
mapF _ B = B
mapF f (F x) = F (f x)


-- Any weakening that weakens into the empty context
-- must necessarily be the identity weakening, and thus
-- γ is the empty context.
weakenClosed :: forall γ x
              . Weakening γ E
             -> ((γ ~ E) => x)
             -> x
weakenClosed WeakRefl k = k
weakenClosed (WeakRight w) _ = weakenImpossible w


weakenImpossible :: forall γ b x
                  . Weakening (γ ::> b) E
                 -> x
weakenImpossible (WeakRight w) = weakenImpossible w


-- | 'weakenVar' gives the denotation of weakenings
--   as a function on variables.
weakenVar :: Weakening γ γ'
          -> Var γ -> Var γ'
weakenVar WeakRefl      = id
weakenVar (WeakLeft w)  = F . weakenVar w
weakenVar (WeakRight w) = weakenVar w . F
weakenVar (WeakSkip w)  = mapF (weakenVar w)


-- | Smart constructor.  Replaces (WeakSkip WeakRefl) with WeakRefl
--   Correctness follows from functor/identity law:
--    mapF 1 = 1
weakSkip :: Weakening γ γ' -> Weakening (γ::>b) (γ'::>b)
weakSkip WeakRefl = WeakRefl
weakSkip w        = WeakSkip w


-- | 'weakCompose' defines the result of composing two weakenings.
--   [[ weakCompose w₂ w₁ ]] = [[ w₂ ]] ∘ [[ w₁ ]]
weakCompose
  :: Weakening γ₂ γ₃
  -> Weakening γ₁ γ₂
  -> Weakening γ₁ γ₃

weakCompose WeakRefl w₁ = w₁
 -- by identity
 --    1 ∘ w₁ = w₁

weakCompose w₂ WeakRefl = w₂
 -- by identity
 --    w₂ ∘ 1 = w₂

weakCompose (WeakLeft w₂) w₁ = WeakLeft (weakCompose w₂ w₁)
 -- by associativity
 --    (weak ∘ w₂) ∘ w₁ = weak ∘ (w₂ ∘ w₁)

weakCompose (WeakRight w₂) w₁ = weakCompose w₂ (WeakLeft w₁)
 -- by associativity
 --    (w₂ ∘ weak) ∘ w₁ = w₂ ∘ (weak ∘ w₁)
 --
 -- Note: This is the only recursive rule that increases one of the arguments.
 --       Termination can be proved via a lexicographic order that first
 --       decreases w₂ then w₁.

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


-- | A restricted form of weakening used inside
--   the normalization procedure
data Wk γ γ' where
  WkRefl  :: Wk γ γ
  WkL     :: Wk γ γ' -> Wk γ (γ'::>b)

-- | `weakNormalize` computes an equivalant weakening
--    in which `WeakRight` constructors never appear.
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


-- | Compute the longest common prefix of two weakenings.
--   This operation is used to hoist weakenings "outside" as
--   far as possible when computing the result of applications.
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


-- | Given a substituion `s` and a weakening `w`
--   compute a new substition `s'` and new
--   weakening `w'` such that:
--
--      [[ s ]] ∘ [[ w ]] == [[ w' ]] ∘ [[ s' ]]
--
--   The resulting substition and weakening will
--   generally be simpler than the ones you started with.
--
--   This function is written in a continuaion-passing
--   style so that the new intermediate context can be
--   calculated.
substWeak :: Subst f γ₂ γ₃
         -> Weakening γ₁ γ₂
         -> (forall γ'
              . Weakening γ' γ₃
             -> Subst f γ₁ γ'
             -> x)
         -> x
substWeak s WeakRefl k = k WeakRefl s
-- By reflexivity:
--   s ∘ 1 == 1 ∘ s

substWeak SubstRefl w k = k w SubstRefl
-- By reflexivity:
--   1 ∘ w == w ∘ 1

substWeak (SubstWeak w0 s) w k =
  substWeak s w $ \w' s' ->
    k (weakCompose w0 w') s'
-- By associativity:
--   (w0 ∘ s) ∘ w
--   == w0 ∘ (s ∘ w)
--   == w0 ∘ (w' ∘ s')
--   == (w0 ∘ w') ∘ s'

substWeak (SubstSkip s) (WeakLeft w) k =
  substWeak s w $ \w' s' ->
    k (WeakLeft w') s'
-- By naturality of weak:
--   mapF s ∘ (weak ∘ w)
--   == (mapF s ∘ weak) ∘ w
--   == (weak ∘ s) ∘ w
--   == weak ∘ (s ∘ w)
--   == weak ∘ (w' ∘ s')
--   == (weak ∘ w') ∘ s'

substWeak (SubstSkip s) (WeakSkip w) k =
  substWeak s w $ \w' s' ->
    k (WeakSkip w') (SubstSkip s')
-- By functor laws:
--   mapF s ∘ mapF w
--   == mapF (s ∘ w)
--   == mapF (w' ∘ s')
--   == mapF w' ∘ mapF s'

substWeak (SubstApply s _f) (WeakLeft w) k =
  substWeak s w k
-- By subst/weak law:
--   apply s f ∘ (weak ∘ w)
--   == (apply s f ∘ weak) ∘ w
--   == s ∘ w

substWeak (SubstApply s f) (WeakSkip w) k =
  substWeak s w $ \w' s' ->
    k WeakRefl (SubstApply (SubstWeak w' s') f)
-- By subst/mapF law:
--   apply s f ∘ mapF w
--   == apply (s ∘ w) f
--   == apply (w' ∘ s') f

substWeak s (WeakRight w) k =
  substWeak s w $ \w' s' ->
    substWeak s' (WeakLeft WeakRefl) $ \w'' s'' ->
      k (weakCompose w' w'') s''
-- By assocativity and induction
--   s ∘ (w ∘ weak)
--   == (s ∘ w) ∘ weak
--   == (w' ∘ s') ∘ weak
--   == w' ∘ (s' ∘ weak)
--   == w' ∘ (w'' ∘ s'')
--   == (w' ∘ w'') ∘ s''


-- | Given an abstraction `a` and a weakening `w`
--   compute a new abstraction `a'` and new
--   weakening `w'` such that:
--
--      [[ a ]] ∘ [[ w ]] == [[ w' ]] ∘ [[ a' ]]
--
--   The resulting abstraction will be mildly
--   mildly simpler than the one you started with.
--
--   This function is written in a continuaion-passing
--   style so that the new intermediate context can be
--   calculated.
abstractWeak :: Abstraction f γ₂ γ₃
             -> Weakening γ₁ γ₂
             -> (forall γ'
                  . Weakening γ' γ₃
                 -> Abstraction f γ₁ γ'
                 -> x)
             -> x
abstractWeak AbstractRefl w k = k w AbstractRefl
-- By identity:
--    1 ∘ w = w ∘ 1

abstractWeak a WeakRefl k = k WeakRefl a
-- By identity:
--    a ∘ 1 = 1 ∘ a

abstractWeak (AbstractApply a u) w k =
  abstractWeak a w $ \w' a' ->
    k (WeakSkip w') (AbstractApply a' u)
-- By naturality of abs
--   (abs u ∘ a) ∘ w
--   == abs u ∘ (a ∘ w)
--   == abs u ∘ (w' ∘ a')
--   == (abs u ∘ w') ∘ a'
--   == (mapF w' ∘ abs u) ∘ a'
--   == mapF w' ∘ (abs u ∘ a')

abstractWeak (AbstractSkip a) (WeakSkip w) k =
  abstractWeak a w $ \w' a' ->
    k (WeakSkip w') (AbstractSkip a')
-- By functor laws:
--  mapF a ∘ mapF w
--  == mapF (a ∘ w)
--  == mapF (w' ∘ a')
--  == mapF w' ∘ mapF a'

abstractWeak (AbstractSkip a) (WeakLeft w) k =
  abstractWeak a w $ \w' a' ->
    k (WeakLeft w') a'
-- By naturality of weak
--  mapF a ∘ (weak ∘ w)
--  == (mapF a ∘ weak) ∘ w
--  == (weak ∘ a) ∘ w
--  == weak ∘ (a ∘ w)
--  == weak ∘ (w' ∘ a')
--  == (weak ∘ w') ∘ a'

abstractWeak a (WeakRight w) k =
  abstractWeak a w $ \w' a' ->
    abstractWeak a' (WeakLeft WeakRefl) $ \w'' a'' ->
      k (weakCompose w' w'') a''
-- By associativity
--   a ∘ (w ∘ weak)
--   (a ∘ w) ∘ weak
--   (w' ∘ a') ∘ weak
--   w' ∘ (a' ∘ weak)
--   w' ∘ (w'' ∘ a'')
--   (w' ∘ w'') ∘ a''


-- Given an abstraction, compute a corresponding weakening.
--    [[ a ]](x) == [[ absWeaken a ]](x)
--
-- Provided none of the unification variables in `a` appear in
-- `x`.
absWeaken :: Abstraction f γ γ'
          -> Weakening γ γ'
absWeaken AbstractRefl = WeakRefl
absWeaken (AbstractApply a _) = WeakLeft (absWeaken a)
absWeaken (AbstractSkip a) = WeakSkip (absWeaken a)
