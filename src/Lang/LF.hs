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
, Var(..)
, Hyps(..)
, Quant(..)
, WFContext
, WFContextRec
, IsBoundVar
, LiftClosed(..)
, AutoWeaken(..)
, CtxDiff
, CtxAppend
, CtxSub
, Subst(..)
, hsubst
, Weakening(..)
, weakening
, weakSubst

  -- * Term views
, KindView(..)
, TypeView(..)
, TermView(..)
, GoalView(..)
, kindView
, typeView
, termView
, goalView
, extendCtx
, weakenCtx
, inEmptyCtx
, extendHyps

  -- * LF type system
, validateKind
, validateType
, inferType
, checkType
, alphaEq

  -- * Printing terms
, ppLF
, Prec(..)

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
, LFApplication (..)
, LFFunc(..)
, LFPi(..)
, underGoal
, underGoal'
, strengthen

{-
, underLambda
, underGoal
, solve
, dumpContext
, strengthen
-}
) where

import Lang.LF.Model
