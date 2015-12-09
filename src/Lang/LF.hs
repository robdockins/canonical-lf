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
, Hyps(..)
, WFContext
, WFContextRec
, IsBoundVar
, LiftClosed(..)
, AutoWeaken(..)
, CtxDiff
, CtxAppend
, CtxSub

  -- * Term views
, KindView(..)
, TypeView(..)
, TermView(..)
, kindView
, typeView
, termView

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


{-
, underLambda
, underGoal
, solve
, dumpContext
, strengthen
-}
) where

import Lang.LF.Model
