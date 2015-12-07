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
, WFContext
, WFContextRec
, IsBoundVar

{-
, KindView(..)
, TypeView(..)
, TermView(..)
, kindView
, typeView
, termView
, validateKind
, validateType
, inferType
, checkType
, alphaEq
, headConstant
-}
, ppLF
, Prec(..)
, Hyps(..)

  -- * Term Construction
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
, LFApplication (..)
, LFFunc(..)
, LFPi(..)

{-
, underLambda
, lookupVariable
, lookupVariableName
, unify
, conj
, cTrue
, cForall
, cExists
, sigma
, goal
, underGoal
, solve
, dumpContext
, autoweaken
, weaken
, strengthen
, LFVar
-}
) where

import Lang.LF.Model
