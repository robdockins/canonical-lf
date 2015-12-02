{-# OPTIONS_GHC -Wwarn #-}
module Main where

import Prelude hiding (pi, abs)

import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF
import           Lang.LF.Tree hiding (M)
import qualified Lang.LF.Tree as Tree

type LF = Tree.LFTree String String
type Sig = Tree.Signature String String
type M = Tree.M String String

sig :: Sig
sig = buildSignature
  [ -- STLC type formers
    "tp"      ::. lf_type
  , "arrow"    :. tp ==> tp ==> tp
  , "nat"      :. tp

    -- STLC term formers
  , "tm"      ::. lf_type
  , "zero"     :. tm
  , "suc"      :. tm ==> tm
  , "app"      :. tm ==> tm ==> tm
  , "lam"      :. tp ==> (tm ==> tm) ==> tm
  , "nat_elim" :. tp ==> tm ==> tm ==> tm ==> tm

    -- STLC typing judgements
  , "typeof" ::. tm ==> tp ==> lf_type
  , "of_zero" :.
         typeof zero nat
  , "of_suc" :.
         pi "n" tm $ \n ->
           typeof n nat ==>
           typeof (suc n) nat
  , "of_app" :.
         pi "e₁" tm $ \e1 ->
         pi "e₂" tm $ \e2 ->
         pi "t₂" tp $ \t2 ->
         pi "t"  tp $ \t ->
           typeof e1 (arrow t2 t) ==>
           typeof e2 t2 ==>
           typeof (app e1 e2) t
  , "of_lam" :.
         pi "t₂" tp $ \t2 ->
         pi "t"  tp $ \t ->
         pi "f" (tm ==> tm) $ \f ->
           (pi "x" tm $ \x ->
              typeof x t2 ==> typeof (f @@ x) t)
           ==>
           typeof (lam t2 (λ"x" tm (\x -> f @@ x))) (arrow t2 t)
  , "of_nat_elim" :.
         pi "t" tp $ \t ->
         pi "z" tm $ \z ->
         pi "s" tm $ \s ->
         pi "n" tm $ \n ->
           typeof z t ==>
           typeof s (arrow t t) ==>
           typeof n nat ==>
           typeof (nat_elim t z s n) t

    -- STLC value judgements
  , "is_value" ::. tm ==> lf_type
  , "value_Z" :.
         is_value zero
  , "value_S" :.
         pi "n" tm $ \n ->
           is_value n ==> is_value (suc n)
  , "value_lam" :.
         pi "t" tp $ \t ->
         pi "f" (tm ==> tm) $ \f ->
           is_value (lam t (λ "x" tm (\x -> f @@ x)))

    -- STLC small-step CBV semantics
  , "step" ::. tm ==> tm ==> lf_type
  , "step_app1" :.
         pi "e₁" tm $ \e1 ->
         pi "e₂" tm $ \e2 ->
         pi "e₁'" tm $ \e1' ->
            step e1 e1' ==>
            step (app e1 e2) (app e1' e2)
  , "step_app2" :.
         pi "e₁" tm $ \e1 ->
         pi "e₂" tm $ \e2 ->
         pi "e₂'" tm $ \e2' ->
            is_value e1 ==>
            step e2 e2' ==>
            step (app e1 e2) (app e1 e2')
  , "step_beta" :.
         pi "e₂" tm $ \e2 ->
         pi "f" (tm ==> tm) $ \f ->
         pi "t₂" tp $ \t2 ->
            is_value e2 ==>
            step (app (lam t2 (λ "x" tm (\x -> f @@ x))) e2) (f @@ e2)
  , "step_nat_zero" :.
         pi "t" tp $ \t ->
         pi "z" tm $ \z ->
         pi "s" tm $ \s ->
           step (nat_elim t z s zero) z
  , "step_nat_succ" :.
         pi "t" tp $ \t ->
         pi "z" tm $ \z ->
         pi "s" tm $ \s ->
         pi "n" tm $ \n ->
           step (nat_elim t z s (suc n)) (app s (nat_elim t z s n))
  ]

tp :: M (LF TYPE)
tp = tyConst "tp"

nat :: M (LF TERM)
nat = tmConst "nat"

arrow :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
arrow x y = tmConst "arrow" @@ x @@ y


tm :: M (LF TYPE)
tm = tyConst "tm"

zero :: M (LF TERM)
zero = tmConst "zero"

suc :: M (LF TERM) -> M (LF TERM)
suc x = tmConst "suc" @@ x

app :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
app x y = tmConst "app" @@ x @@ y

lam :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
lam t f = tmConst "lam" @@ t @@ f

nat_elim :: M (LF TERM) -> M (LF TERM) -> M (LF TERM) -> M (LF TERM) -> M (LF TERM)
nat_elim t z s n = tmConst "nat_elim" @@ t @@ z @@ s @@ n

typeof :: M (LF TERM) -> M (LF TERM) -> M (LF TYPE)
typeof t p = tyConst "typeof" @@ t @@ p

of_suc :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
of_suc n prf = tmConst "of_suc" @@ n @@ prf

of_zero :: M (LF TERM)
of_zero = tmConst "of_zero"

is_value :: M (LF TERM) -> M (LF TYPE)
is_value v = tyConst "is_value" @@ v

step :: M (LF TERM) -> M (LF TERM) -> M (LF TYPE)
step x x' = tyConst "step" @@ x @@ x'

--testTerm :: LF TYPE
testTerm = runM sig $ (tmConst "of_lam" :: M (LF TERM))

  --abs nat (lam "x" tm (suc (var 0)))

typing :: LF TERM
typing = runM sig $
  tmConst "of_lam" @@ nat @@ nat @@ λ"x" tm (\x -> suc x) @@
     (λ"x" tm $ \x ->
       λ"prf" (typeof x nat) $ \prf ->
         of_suc x prf)

typing2 :: LF TERM
typing2 = runM sig $
  tmConst "of_lam" @@ nat @@ (arrow nat nat) @@
      (λ"x" tm (\x -> lam nat (λ"y" tm $ \y -> nat_elim nat x (lam nat (λ"n" tm (\n -> suc n))) y))) @@
      (λ"x" tm $ \x ->
        λ"prf_x" (typeof x nat) $ \prf_x ->
          tmConst "of_lam" @@ nat @@ nat @@
            (λ"y" tm $ \y -> nat_elim nat x (lam nat (λ"n" tm (\n -> suc n))) y) @@
            (λ"y" tm $ \y ->
              λ"prf_y" (typeof y nat) $ \prf_y ->
                tmConst "of_nat_elim" @@ nat @@ x @@ (lam nat (λ"n" tm (\n -> suc n))) @@ y @@
                  prf_x @@
                  (tmConst "of_lam" @@ nat @@ nat @@ (λ"n" tm (\n -> suc n)) @@
                    (λ"n" tm $ \n -> λ"prf_n" (typeof n nat) $ \prf_n -> of_suc n prf_n)) @@
                  prf_y
            )
      )

--(tmConst "of_lam" :: M (LF TERM))

--of_S zero of_Z

--

--   lam "x" prop (por (var 0) (pand (tmConst "False") (var 0)))
--   lam "x" nat (app (suc (var 0)) (suc (var 0)))
--   nat_iter_type


main = sig `seq` do
   let x :: LF TERM
       -- x = typing
       x = runM sig $ tmConst "step_beta"
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec x
   putStrLn ""
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec =<< inferType x
   putStrLn ""
