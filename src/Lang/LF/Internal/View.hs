module Lang.LF.Internal.View where

import Data.Set (Set)

import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Weak

kindViewLF :: forall f m γ γ'
            . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
           => Weakening γ' γ
           -> f γ' KIND
           -> KindView f m γ
kindViewLF w k =
  case unfoldLF k of
    Weak w' x ->
       kindViewLF (weakTrans w' w) x
    Type -> VType
    KPi nm a k ->
       let a' = weaken w a in
       let k' = weaken (WeakSkip w) k in
       extendCtx nm QPi a' $ VKPi nm B a' k'

typeViewLF :: forall f m γ γ'
            . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
           => Weakening γ' γ
           -> f γ' TYPE
           -> TypeView f m γ
typeViewLF w a =
  case unfoldLF a of
    Weak w' x ->
      typeViewLF (weakTrans w' w) x
    AType p ->
      go w [] p
    TyPi nm a1 a2 ->
      let a1' = weaken w a1 in
      let a2' = weaken (WeakSkip w) a2 in
      extendCtx nm QPi a1' $
        VTyPi nm B a1' a2'

  where go :: forall γ γ'
            . Weakening γ' γ
           -> [f γ TERM]
           -> f γ' ATYPE
           -> TypeView f m γ
        go w args x =
          case unfoldLF x of
            Weak w' x -> go (weakTrans w' w) args x
            TyConst a -> VTyConst a args
            TyApp p m -> go w (weaken w m : args) p

termViewLF :: forall f m γ γ'
            . (LFModel f m, ?nms :: Set String
              , ?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => Weakening γ' γ
           -> f γ' TERM
           -> TermView f m γ
termViewLF w m =
  case unfoldLF m of
    Weak w' x ->
      termViewLF (weakTrans w' w) x
    ATerm r ->
      go w [] r
    Lam nm a body ->
      let a' = weaken w a in
      let body' = weaken (WeakSkip w) body in
      extendCtx nm QLam a' $
        VLam nm B a' body'

 where go :: forall γ γ'
           . Weakening γ' γ
           -> [f γ TERM]
           -> f γ' ATERM
           -> TermView f m γ
       go w args r =
         case unfoldLF r of
           Weak w' x -> go (weakTrans w' w) args x
           Var       -> VVar (weakenVar w B) args
           Const c   -> VConst c args
           UVar u    -> VUVar u args
           App r' m  -> go w (weaken w m : args) r'


constraintViewLF :: forall f m γ γ'
            . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
           => Weakening γ' γ
           -> f γ' CON
           -> ConstraintView f m γ
constraintViewLF w c =
  case unfoldLF c of
    Weak w' x -> constraintViewLF (weakTrans w' w) x
    Fail -> VFail
    Unify r1 r2 -> VUnify (aterm (weaken w r1)) (aterm (weaken w r2))
    And cs -> VAnd (map (weaken w) cs)
    Forall nm a c ->
       let a' = weaken w a in
       let c' = weaken (WeakSkip w) c in
       extendCtx nm QForall a' $
         VForall nm B a' c'
    Exists nm a c ->
       let a' = weaken w a in
       let c' = weaken (WeakSkip w) c in
       extendCtx nm QExists a' $
         VExists nm B a' c'

goalViewLF :: forall f m γ γ'
            . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
           => Weakening γ' γ
           -> f γ' GOAL
           -> GoalView f m γ
goalViewLF w g =
  case unfoldLF g of
    Weak w' x -> goalViewLF (weakTrans w' w) x
    Goal m c -> VGoal (weaken w m) (weaken w c)
    Sigma nm a g ->
       let a' = weaken w a in
       let g' = weaken (WeakSkip w) g in
       extendCtx nm QSigma a' $
         VSigma nm B a' g'
