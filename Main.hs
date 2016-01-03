{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wwarn #-}
module Main where

import Prelude hiding (pi, abs)

import Control.Monad.Trans.Class
import Control.Monad.State
--import           Data.Sequence (Seq, (|>))
--import qualified Data.Sequence as Seq
import           Data.Set (Set)
--import qualified Data.Set as Set
--import           Data.Map (Map)
--import qualified Data.Map as Map
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF
import           Lang.LF.ChangeT
import           Lang.LF.Tree hiding (M)
import qualified Lang.LF.Tree as Tree

import qualified Debug.Trace as Debug

type LF = Tree.LFTree String String
type Sig = Tree.Signature String String
type M = Tree.M String String
type H = Hyps LF

sig :: Sig
sig = buildSignature
  [ -- STLC type formers
    "tp"      ::. lf_type
  , "arrow"    :. tp ==> tp ==> tp
  , "nat"      :. tp
  , "unit"     :. tp

    -- STLC term formers
  , "tm"      ::. tp ==> lf_type
  , "zero"     :. tm nat
  , "suc"      :. tm nat ==> tm nat
  , "app"      :. pi "a" tp $ \a ->
                  pi "b" tp $ \b ->
                     tm (arrow (var a) (var b)) ==> tm (var a) ==> tm (var b)
  , "lam"      :. pi "a" tp $ \a ->
                  pi "b" tp $ \b ->
                     (tm (var a) ==> tm (var b)) ==> tm (arrow (var a) (var b))
  , "nat_elim" :. pi "a" tp $ \a ->
                    tm (var a) ==> tm (arrow (var a) (var a)) ==> tm nat ==> tm (var a)
  , "tt"       :. tm unit

    -- STLC value judgements
  , "is_value" ::. pi "a" tp $ \a -> tm (var a) ==> lf_type
  , "value_tt" :.
         is_value unit tt
  , "value_zero" :.
         is_value nat zero
  , "value_suc" :.
         pi "n" (tm nat) $ \n ->
           is_value nat (var n) ==> is_value nat (suc (var n))
  , "value_lam" :.
         pi "a" tp $ \a ->
         pi "b" tp $ \b ->
         pi "f" (tm (var a) ==> tm (var b)) $ \f ->
           is_value (arrow (var a) (var b)) (lam (var a) (var b) "x" (\x -> var f @@ var x))

    -- STLC small-step CBV semantics
  , "step" ::. pi "a" tp $ \a ->
                  tm (var a) ==> tm (var a) ==> lf_type
  , "step_app1" :.
         pi "a" tp $ \a ->
         pi "b" tp $ \b ->
         pi "e₁" (tm (arrow (var a) (var b))) $ \e1 ->
         pi "e₂" (tm (var a)) $ \e2 ->
         pi "e₁'" (tm (arrow (var a) (var b))) $ \e1' ->
            step (arrow (var a) (var b)) (var e1) (var e1') ==>
            step (var b) (app (var a) (var b) (var e1) (var e2))
                         (app (var a) (var b) (var e1') (var e2))
  , "step_app2" :.
         pi "a" tp $ \a ->
         pi "b" tp $ \b ->
         pi "e₁" (tm (arrow (var a) (var b))) $ \e1 ->
         pi "e₂" (tm (var a)) $ \e2 ->
         pi "e₂'" (tm (var a)) $ \e2' ->
            is_value (arrow (var a) (var b)) (var e1) ==>
            step (var a) (var e2) (var e2') ==>
            step (var b)
                 (app (var a) (var b) (var e1) (var e2))
                 (app (var a) (var b) (var e1) (var e2'))
  , "step_beta" :.
         pi "a" tp $ \a ->
         pi "b" tp $ \b ->
         pi "e₂" (tm (var a)) $ \e2 ->
         pi "f" (tm (var a) ==> tm (var b)) $ \f ->
            is_value (var a) (var e2) ==>
            step (var b)
                 (app (var a) (var b) (lam (var a) (var b) "x" (\x -> var f @@ var x)) (var e2))
                 (var f @@ var e2)
  , "step_nat_zero" :.
         pi "a" tp $ \a ->
         pi "z" (tm (var a)) $ \z ->
         pi "s" (tm (arrow (var a) (var a))) $ \s ->
           step (var a)
                (nat_elim (var a) (var z) (var s) zero)
                (var z)
  , "step_nat_succ" :.
         pi "a" tp $ \a ->
         pi "z" (tm (var a)) $ \z ->
         pi "s" (tm (arrow (var a) (var a))) $ \s ->
         pi "n" (tm nat) $ \n ->
           step (var a)
                (nat_elim (var a) (var z) (var s) (suc (var n)))
                (app (var a) (var a) (var s) (nat_elim (var a) (var z) (var s) (var n)))

  , "F" :. tm (arrow unit unit)
  ]


tp :: WFContext γ => M (LF γ TYPE)
tp = tyConst "tp"

unit :: WFContext γ => M (LF γ TERM)
unit = tmConst "unit"

nat :: WFContext γ => M (LF γ TERM)
nat = tmConst "nat"

arrow :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM)
arrow x y = tmConst "arrow" @@ x @@ y

tm :: WFContext γ => M (LF γ TERM) -> M (LF γ TYPE)
tm a = tyConst "tm" @@ a

tt :: WFContext γ => M (LF γ TERM)
tt = tmConst "tt"

zero :: WFContext γ => M (LF γ TERM)
zero = tmConst "zero"

suc :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM)
suc x = tmConst "suc" @@ x

infixl 5 `app`
app :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM)
app a b x y = tmConst "app" @@ a @@ b @@ x @@ y

lam :: WFContext γ
   => M (LF γ TERM)
   -> M (LF γ TERM)
   -> String
   -> (forall b. IsBoundVar b => Var (γ::>b) -> M (LF (γ::>b) TERM))
   -> M (LF γ TERM)
lam a b nm f = tmConst "lam" @@ a @@ b @@ (λ nm (tm a) f)

nat_elim :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM)
nat_elim a z s n = tmConst "nat_elim" @@ a @@ z @@ s @@ n

typeof :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TYPE)
typeof a t p = tyConst "typeof" @@ a @@ t @@ p

is_value :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TYPE)
is_value a v = tyConst "is_value" @@ a @@ v

step :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TYPE)
step a x x' = tyConst "step" @@ a @@ x @@ x'


pattern VarP v <-
  (termView -> VVar v [])
pattern AppP a b m1 m2 <-
  (termView -> VConst "app" [a, b, m1, m2])
pattern LamP a b m <-
  (termView -> VConst "lam" [a, b, m])
pattern NatElimP a z s n <-
  (termView -> VConst "nat_elim" [a,z,s,n])
pattern ZeroP <-
  (termView -> VConst "zero" [])
pattern SucP n <-
  (termView -> VConst "suc" [n])
pattern ArrowP t1 t2 <-
  (termView -> VConst "arrow" [t1,t2])

addConstraint 
   :: M (LF E CON)
   -> StateT [LF E CON] M ()
addConstraint c = do
   x <- lift c
   modify (x:)


-- CBV reduction to head-normal form
eval :: (?nms :: Set String, ?hyps :: H γ, WFContext γ, ?soln :: LFSoln LF)
     => LF γ TERM
     -> ChangeT M (LF γ TERM)

-- β reduction
eval (AppP _ _ (LamP _ _ body) arg) = do
    arg' <- eval arg
    eval =<< Changed (return body @@ return arg')

-- structural evaluation under application
eval tm@(AppP a b m1 m2) = do
    case eval m1 of
      Unchanged _ ->
        case eval m2 of
          Unchanged _ -> Unchanged tm
          Changed m2' -> eval =<< Changed (app (return a) (return b) (return m1) m2')
      Changed m1' ->
        eval =<< Changed (app (return a) (return b) m1' (return m2))

-- evaluation under lambdas
eval tm@(LamP a b (termView -> VLam nm wk _var tp body)) = do
    case eval body of
      Changed body' -> do
        Changed (tmConst "lam" @@ return a @@ return b @@ (weakening wk <$> mkLam nm (return tp) body'))
      _ -> Unchanged tm

-- nat recursor: zero case
eval (NatElimP _a z _s ZeroP) =
    Changed (return z)

-- nat recursor: successor case
eval (NatElimP a z s (SucP n)) =
    eval =<< Changed (app (return a) (return a)
                          (return s)
                          (nat_elim (return a) (return z) (return s) (return n)))

eval t = Unchanged t


five :: M (LF E TERM)
five = suc $ suc $ suc $ suc $ suc $ zero

three :: M (LF E TERM)
three = suc $ suc $ suc $ zero

add :: M (LF E TERM)
add = lam nat (arrow nat nat) "x" $ \x ->
      lam nat nat "y" $ \y ->
        nat_elim nat (var x) (lam nat nat "n" $ \n -> suc (var n)) (var y)

composeN :: M (LF E TERM) -> M (LF E TERM)
composeN a = do
  lam (arrow a a) (arrow nat (arrow a a))  "f" $ \f ->
    lam nat (autoweaken <$> (arrow a a)) "n" $ \n ->
      nat_elim (autoweaken <$> (arrow a a))
               (lam (autoweaken <$> a) (autoweaken <$> a) "q" $ \q -> var q)
               (lam (autoweaken <$> (arrow a a)) (autoweaken <$> (arrow a a)) "g" $ \g ->
                  lam (autoweaken <$> a) (autoweaken <$> a) "q" $ \q ->
                    app (autoweaken <$> a) (autoweaken <$> a)
                     (var f)
                     (app (autoweaken <$> a) (autoweaken <$> a) (var g) (var q)))
               (var n)

testTerm :: LF E TERM
testTerm =
  --mkTerm sig $ add `app` three `app` five
  mkTerm sig $
        app unit unit
          (app nat (arrow unit unit)
              (app (arrow unit unit) (arrow nat (arrow unit unit))
                   (composeN unit)
                   (lam unit unit "q" $ \q -> app unit unit (tmConst "F") (var q)))
              three)
          tt

evalTerm :: LF E TERM
evalTerm = inEmptyCtx $
   mkTerm sig $ runChangeT $ eval testTerm

main = inEmptyCtx $ do
   let x :: LF E TERM
       x = evalTerm
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec x
   putStrLn ""
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ (ppLF TopPrec =<< inferType x)
   putStrLn ""

