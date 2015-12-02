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
, lam
, var
, tmConst
, app
, LFApplication (..)
, LFFunc(..)
) where

import Lang.LF.Model
