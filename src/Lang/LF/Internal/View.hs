module Lang.LF.Internal.View where

import Data.Set (Set)

import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Subst

kindViewLF :: forall f m γ γ'
            . (WFContext γ', LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
           => (forall s. f γ' s -> f γ s)
           -> f γ' KIND
           -> KindView f m γ
kindViewLF w k =
  case unfoldLF k of
    Weak x -> weakenCtx $ kindViewLF (w . weaken) x
    Type -> VType
    KPi nm a k -> VKPi $ \cont -> do
       extendCtx nm QPi a $ cont w nm (B ()) a k


typeViewLF :: forall f m γ γ'
            . (WFContext γ', LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
           => (forall s. f γ' s -> f γ s)
           -> f γ' TYPE
           -> TypeView f m γ
typeViewLF w a =
  case unfoldLF a of
    Weak x -> weakenCtx $ typeViewLF (w . weaken) x
    AType p -> go w [] p
    TyPi nm a1 a2 -> VTyPi $ \cont ->
       extendCtx nm QPi a1 $ cont w nm (B ()) a1 a2

  where go :: forall γ γ'
            . WFContext γ'
           => (forall s. f γ' s -> f γ s)
           -> [f γ TERM]
           -> f γ' ATYPE
           -> TypeView f m γ
        go w args x =
          case unfoldLF x of
            Weak x -> go (w . weaken) args x
            TyConst a -> VTyConst a args
            TyApp p m -> go w (w m : args) p


termViewLF :: forall f m γ γ'
            . (WFContext γ', LFModel f m, ?nms :: Set String
              , ?hyps :: Hyps f γ', ?soln :: LFSoln f)
           => Weakening γ' γ
           -> (Var γ' -> Var γ)
           -> f γ' TERM
           -> TermView f m γ
termViewLF w wv m =
  case unfoldLF m of
    Weak x -> weakenCtx $ termViewLF (WeakL w) (wv . F) x
    ATerm r -> go w wv [] r
    Lam nm a m' -> VLam nm $ \cont -> do
       extendCtx nm QLam a $ cont w (B ()) a m'

 where go :: forall γ γ'
            . WFContext γ'
           => Weakening γ' γ
           -> (Var γ' -> Var γ)
           -> [f γ TERM]
           -> f γ' ATERM
           -> TermView f m γ
       go w wv args r =
         case unfoldLF r of
           Weak x   -> go (WeakL w) (wv . F) args x
           Var v    -> VVar (wv (B v)) args
           Const c  -> VConst c args
           UVar u   -> VUVar u args
           App r' m -> go w wv (weakening w m : args) r'

constraintViewLF :: forall f m γ γ'
            . (WFContext γ', LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
           => Weakening γ' γ
           -> f γ' CON
           -> ConstraintView f m γ
constraintViewLF w c =
  case unfoldLF c of
    Weak x -> weakenCtx $ constraintViewLF (WeakL w) x
    Fail -> VFail
    Unify r1 r2 -> VUnify (aterm (weakening w r1)) (aterm (weakening w r2))
    And cs -> VAnd (map (weakening w) cs)
    Forall nm a c -> VForall nm $ \cont -> do
       extendCtx nm QForall a $ cont w (B ()) a c
    Exists nm a c -> VExists nm $ \cont -> do
       extendCtx nm QExists a $ cont w (B ()) a c

goalViewLF :: forall f m γ γ'
            . (WFContext γ', LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
           => Weakening γ' γ
           -> f γ' GOAL
           -> GoalView f m γ
goalViewLF w g =
  case unfoldLF g of
    Weak x -> weakenCtx $ goalViewLF (WeakL w) x
    Goal m c -> VGoal (weakening w m) (weakening w c)
    Sigma nm a g -> VSigma $ \cont ->
       extendCtx nm QSigma a $ cont w nm (B ()) a g
