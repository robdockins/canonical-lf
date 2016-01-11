module Lang.LF
( -- * LF Sorts
  type SORT
, KIND
, TYPE
, TERM
, CON
, GOAL
, type Ctx(..)

  -- * LF Models
, LFModel
, LFTypeConst
, LFConst
, LFUVar
, LFSoln

, Var(..)
, Hyps(..)
, Quant(..)
, WFContext
, WFContextRec
, IsBoundVar
, LiftClosed(..)
, AutoWeaken
, autoweaken
, CtxDiff
, CtxAppend
, CtxSub
, Subst(..)
, hsubst
, Weakening(..)
, weakening
, weakSubst
, withCurrentSolution
, commitSolution
, lookupSubst

  -- * Term views
, KindView(..)
, TypeView(..)
, TermView(..)
, ConstraintView(..)
, GoalView(..)
, kindView
, typeView
, termView
, constraintView
, goalView
, extendCtx
, weakenCtx
, inEmptyCtx
, extendHyps
, freshUVar

  -- * LF type system
, validateKind
, validateType
, inferType
, checkType
, alphaEq

  -- * Printing terms
, ppLF
, Prec(..)
, displayLF

  -- * Term Construction
, weaken
, lf_type
, kPi
, kArrow
, tyPi
, tyConst
, tyApp
, tyArrow
, λ
, var
, uvar
, tmConst
, mkLam
, mkSigma
, unify
, conj
, cTrue
, cForall
, cExists
, sigma
, goal
, goal'
, LFApplication (..)
, LFFunc(..)
, LFPi(..)
, underGoal
, underGoal'
, strengthen
, solve
, instantiate
{-
, dumpContext
-}
) where

import Lang.LF.Internal.Build
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Model
import Lang.LF.Internal.Print
import Lang.LF.Internal.Subst
import Lang.LF.Internal.Typecheck
