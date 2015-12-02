{-# OPTIONS_GHC -Wwarn #-}
module Main where

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import           Lang.LF
import           Lang.LF.Tree


type LF = LFTree String String
type Sig = Signature String String
type M = ReaderT Sig (Except String)

sig :: Sig
sig = buildSignature
  [ TypeDecl "tm" lf_type
  , TypeDecl "tp" lf_type

  , TermDecl "arrow" $ tp ==> tp ==> tp
  , TermDecl "nat" $ tp

  , TermDecl "app" $ tm ==> tm ==> tm
  , TermDecl "abs" $ tp ==> (tm ==> tm) ==> tm
  , TermDecl "S" $ tm ==> tm
  , TermDecl "Z" $ tm

  , TypeDecl "typeof" $ tm ==> tp ==> lf_type
  , TermDecl "of_Z" $ typeof zero nat
  , TermDecl "of_S" $ tyPi "n" tm $ typeof (var 0) nat
                                ==> typeof (suc (var 0)) nat
  , TermDecl "of_app" $ tyPi "e₁" tm $ tyPi "e₂" tm $ tyPi "t₂" tp $ tyPi "t" tp $
                            typeof (var 3) (arrow (var 1) (var 0)) ==>
                            typeof (var 2) (var 1) ==>
                            typeof (obApp (var 3) (var 2)) (var 0)
  , TermDecl "of_lam" $ tyPi "t₂" tp $ tyPi "t" tp $ tyPi "f" (tm ==> tm) $
                          (tyPi "x" tm $ typeof (var 0) (var 3)
                                     ==> typeof (var 1 @@ var 0) (var 2))
                          ==>
                          typeof (obAbs (var 2) (lam "x" tm (var 1 @@ var 0))) (arrow (var 2) (var 1))

  , TypeDecl "is_value" $ tm ==> lf_type
  , TermDecl "value_Z" $ is_value zero
  , TermDecl "value_S" $ tyPi "n" tm $ is_value (var 0) ==> is_value (suc (var 0))
  , TermDecl "value_lam" $ tyPi "t" tp $ tyPi "f" (tm ==> tm) $
                              is_value (obAbs (var 1) (lam "x" tm (var 1 @@ var 0)))

  , TypeDecl "step" $ tm ==> tm ==> lf_type

  , TermDecl "step_app1" $ tyPi "e₁" tm $ tyPi "e₂" tm $ tyPi "e₁'" tm $
                              step (var 2) (var 0) ==>
                              step (obApp (var 2) (var 1)) (obApp (var 0) (var 1))

  , TermDecl "step_app2" $ tyPi "e₁" tm $ tyPi "e₂" tm $ tyPi "e₂'" tm $
                              is_value (var 2) ==>
                              step (var 1) (var 0) ==>
                              step (obApp (var 2) (var 1)) (obApp (var 2) (var 0))

  , TermDecl "step_beta" $ tyPi "e₂" tm $ tyPi "f" (tm ==> tm) $ tyPi "t₂" tp $
                              is_value (var 2) ==>
                              step (obApp (obAbs (var 0) (lam "x" tm (var 2 @@ var 0))) (var 2))
                                   (var 1 @@ var 2)
  ]


tm :: M (LF TYPE)
tm = tyConst "tm"

tp :: M (LF TYPE)
tp = tyConst "tp"

ctx :: M (LF TYPE)
ctx = tyConst "ctx"

zero :: M (LF TERM)
zero = tmConst "Z"

is_value :: M (LF TERM) -> M (LF TYPE)
is_value v = tyConst "is_value" @@ v

step :: M (LF TERM) -> M (LF TERM) -> M (LF TYPE)
step x x' = tyConst "step" @@ x @@ x'

typeof :: M (LF TERM) -> M (LF TERM) -> M (LF TYPE)
typeof t p = tyConst "typeof" @@ t @@ p

suc :: M (LF TERM) -> M (LF TERM)
suc x = tmConst "S" @@ x

nat :: M (LF TERM)
nat = tmConst "nat"

obApp :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
obApp x y = tmConst "app" @@ x @@ y

obAbs :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
obAbs t f = tmConst "abs" @@ t @@ f

arrow :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
arrow x y = tmConst "arrow" @@ x @@ y

of_S :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
of_S n prf = tmConst "of_S" @@ n @@ prf

of_Z :: M (LF TERM)
of_Z = tmConst "of_Z"

--testTerm :: LF TYPE
testTerm = runM sig $ (tmConst "of_lam" :: M (LF TERM))

  --obAbs nat (lam "x" tm (suc (var 0)))

typing :: LF TERM
typing = runM sig $
  tmConst "of_lam" @@ nat @@ nat @@ lam "x" tm (suc (var 0)) @@
     (lam "x" tm $ lam "prf" (typeof (var 0) nat) $ of_S (var 1) (var 0))

--(tmConst "of_lam" :: M (LF TERM))

--of_S zero of_Z

--

--   lam "x" prop (por (var 0) (pand (tmConst "False") (var 0)))
--   lam "x" nat (app (suc (var 0)) (suc (var 0)))
--   nat_iter_type


main = sig `seq` do
   let x :: LF TERM
       x = typing
       -- x = runM sig $ tmConst "step_app2"
   putStrLn $ show $ runM sig $ ppLF Set.empty Seq.empty x
   putStrLn $ show $ runM sig (ppLF Set.empty Seq.empty =<< inferType Seq.empty x)
