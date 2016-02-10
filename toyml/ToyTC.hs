module ToyTC where

import           Control.Monad.Trans.Class
import           Control.Monad.State
import           Data.Set (Set)
import qualified Data.Set as Set
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF
import           Lang.LF.ChangeT

import           Terms

import qualified Debug.Trace as Debug

runTC :: LF E TERM -> M (LF E GOAL)
runTC tm = withCurrentSolution $ inEmptyCtx $ do
  (ty, cs) <- flip runStateT [] $ tc SubstRefl tm
  (cs', soln) <- solve =<< conj (map return cs)
  commitSolution soln
  let ?soln = soln
  ty' <- runChangeT $ instantiate ty
  goal (return ty') (return cs')


addConstraint
   :: M (LF E CON)
   -> StateT [LF E CON] M ()
addConstraint c = do
   x <- lift c
   modify (x:)


-- | instantiateScheme replaces all the bound variables in a type scheme
--   with fresh unification variables.
instantiateScheme
   :: ( ?hyps :: H γ
      , ?soln :: LFSoln LF
      )
   => Subst LF γ E
   -> LF γ TERM
   -> M (LF E TERM)
instantiateScheme sub (termView -> VConst "sch_ty" [t]) =
  hsubst sub t

instantiateScheme sub (termView -> VConst "sch_forall"
                                     [termView -> VLam _nm _x _t m]) = do
  newty <- uvar =<< freshUVar =<< ty
  let sub' = SubstApply sub newty
  instantiateScheme sub' m

instantiateScheme _ m = do
  mdoc <- ppLF TopPrec WeakRefl m
  fail $ unlines [ "Unexpected term in instantiate:"
                 , show $ indent 2 mdoc
                 ]

subFreeUVars :: LFModel f m
              => Subst f γ γ'
              -> Set (LFUVar f)
subFreeUVars SubstRefl        = Set.empty
subFreeUVars (SubstSkip s)    = subFreeUVars s
subFreeUVars (SubstWeak _ s)  = subFreeUVars s
subFreeUVars (SubstApply s a) = Set.union (subFreeUVars s) (freeUVars a)

generalize
   :: ( ?hyps :: H γ
      , ?soln :: LFSoln LF
      )
   => Subst LF γ E
   -> LF E TERM
   -> StateT [LF E CON] M (LF E TERM, LFSoln LF)
{-
generalize _ t = do
    x <- lift ("sch_ty" @@ return t)
    Debug.trace "no generalization" $
      return (x, ?soln)
-}
generalize sub t = do
  cs <- get
  (c',soln') <- lift (solve =<< conj (map return cs))
  put [c']
  lift $ do
    commitSolution soln'
    let ?soln = soln'
    t' <- runChangeT $ instantiate t
    let fvt   = freeUVars t'
    let fvsub = subFreeUVars sub
    let fvc   = freeUVars c'
    let gvars = (fvt Set.\\ fvsub) Set.\\ fvc
    t'' <- go t' AbstractRefl (Set.toList gvars)
    tdoc <- inEmptyCtx $ ppLF TopPrec WeakRefl t''
    Debug.trace ("Generalized type: " ++ show tdoc) $
      return (t'', soln')

 where go :: LiftClosed γ'
          => LF γ TERM
          -> Abstraction LF γ γ'
          -> [LFUVar LF]
          -> M (LF γ' TERM)
       go t abs [] = do
          t' <- abstractUVars abs t
          "sch_ty" @@ return t'
       go t abs (u:us) = do
          t' <- go t (AbstractApply abs u) us
          ty' <- ty
          "sch_forall" @@ mkLam "u" B ty' t'


tc :: ( LiftClosed γ
      , ?hyps :: H γ
      , ?soln :: LFSoln LF
      )
   => Subst LF γ E
   -> LF γ TERM
   -> StateT [LF E CON] M (LF E TERM)

tc sub (termView -> VConst "ml_var" [termView -> VVar v []]) = lift $ do
  sch <- lookupSubst v sub
  inEmptyCtx $
    instantiateScheme SubstRefl sch

tc sub (termView -> VConst "ml_app" [a,b]) = do
  tfun <- tc sub a
  targ <- tc sub b
  tres <- lift (uvar =<< freshUVar =<< ty)
  addConstraint $
    unify (return tfun) ("arr" @@ return targ @@ return tres)
  return tres

tc sub (termView -> VConst "ml_lam" [termView -> VLam _nm _x _t m]) = do
  targ <- lift (uvar =<< freshUVar =<< ty)
  sub' <- lift (SubstApply sub <$> ("sch_ty" @@ (return $ liftClosed targ)))
  tres <- tc sub' m
  lift ("arr" @@ return targ @@ return tres)

tc sub (termView -> VConst "ml_pair" [a,b]) = do
  aty <- tc sub a
  bty <- tc sub b
  lift ("prod" @@ return aty @@ return bty)

tc sub (termView -> VConst "ml_fst" [m]) = do
  aty <- lift (uvar =<< freshUVar =<< ty)
  bty <- lift (uvar =<< freshUVar =<< ty)
  mty <- tc sub m
  addConstraint $
    unify (return mty) ("prod" @@ return aty @@ return bty)
  return aty

tc sub (termView -> VConst "ml_snd" [m]) = do
  aty <- lift (uvar =<< freshUVar =<< ty)
  bty <- lift (uvar =<< freshUVar =<< ty)
  mty <- tc sub m
  addConstraint $
    unify (return mty) ("prod" @@ return aty @@ return bty)
  return bty

tc _sub (termView -> VConst "ml_tt" []) = do
  lift "unit"

tc sub (termView -> VConst "ml_inl" [a]) = do
  aty <- tc sub a
  bty <- lift (uvar =<< freshUVar =<< ty)
  lift ("sum" @@ return aty @@ return bty)

tc sub (termView -> VConst "ml_inr" [b]) = do
  aty <- lift (uvar =<< freshUVar =<< ty)
  bty <- tc sub b
  lift ("sum" @@ return aty @@ return bty)

tc sub (termView -> VConst "ml_letval" [e,m]) = do
  ety <- tc sub e
  (sch,soln') <- generalize sub ety
  let ?soln = soln'
  let sub' = SubstApply sub sch
  case termView m of
    VLam _nm _x _t m' -> tc sub' m'
    _ -> fail "Expected lambda in letval body"

tc sub (termView -> VConst "ml_case" [e,l,r]) = do
  lty <- lift (uvar =<< freshUVar =<< ty)
  rty <- lift (uvar =<< freshUVar =<< ty)
  ety <- tc sub e
  addConstraint $
    unify (return ety) ("sum" @@ return lty @@ return rty)
  subl <- lift (SubstApply sub <$> ("sch_ty" @@ (return $ liftClosed lty)))
  subr <- lift (SubstApply sub <$> ("sch_ty" @@ (return $ liftClosed rty)))

  xl <- case termView l of
          VLam _nm _x _t lm -> tc subl lm
          _ -> fail "Expected lambda in left case branch"
  xr <- case termView r of
          VLam _nm _x _t rm -> tc subr rm
          _ -> fail "Expected lambda in right case branch"
  addConstraint $
    unify (return xl) (return xr)
  return xl

tc _ m = do
  mdoc <- lift $ ppLF TopPrec WeakRefl m
  fail $ unlines
    [ "Unexpected term while typechecking:"
    , show $ indent 2 mdoc
    ]
