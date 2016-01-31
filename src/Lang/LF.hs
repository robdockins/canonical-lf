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
, LiftClosed(..)
, AutoWeaken
, autoweaken
, CtxDiff
, CtxAppend
, CtxSub
, Subst(..)
, hsubst
, Weakening(..)
, weakenVar
, weakSubst
, withCurrentSolution
, commitSolution
, lookupSubst
, mapF
, freeVar
, varCensus
, freeUVars
, Abstraction(..)
, abstractUVars

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
, weak
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
, mkRecord
, mkTyRecord
, record
, tyRecord
, project
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
, strengthen
, solve
, instantiate
) where

import Lang.LF.Internal.Build
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Model
import Lang.LF.Internal.Print
import Lang.LF.Internal.Subst
import Lang.LF.Internal.Typecheck
import Lang.LF.Internal.Weak
