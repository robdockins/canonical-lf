module Lang.LF
( LFModel
, type SORT
, KIND
, TYPE
, TERM
, validateKind
, validateType
, inferType
, checkType
, alphaEq
, headConstant
, ppLF
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
, Prec(..)
) where

import Lang.LF.Model
