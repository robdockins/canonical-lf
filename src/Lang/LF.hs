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
, typ
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
, (==>)
, LFApplication (..)
) where

import Lang.LF.Model
