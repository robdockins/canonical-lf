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
  , "tm"      ::. lf_type
  , "zero"     :. tm
  , "suc"      :. tm ==> tm
  , "app"      :. tm ==> tm ==> tm
  , "lam"      :. (tm ==> tm) ==> tm
  , "nat_elim" :. tm ==> tm ==> tm ==> tm
  , "tt"       :. tm

    -- STLC typing judgements
  , "typeof" ::. tm ==> tp ==> lf_type
  , "of_unit" :.
         typeof tt unit
  , "of_zero" :.
         typeof zero nat
  , "of_suc" :.
         pi "n" tm $ \n ->
           typeof (var n) nat ==>
           typeof (suc (var n)) nat
  , "of_app" :.
         pi "e₁" tm $ \e1 ->
         pi "e₂" tm $ \e2 ->
         pi "t₂" tp $ \t2 ->
         pi "t"  tp $ \t ->
           typeof (var e1) (arrow (var t2) (var t)) ==>
           typeof (var e2) (var t2) ==>
           typeof (app (var e1) (var e2)) (var t)
  , "of_lam" :.
         pi "t₂" tp $ \t2 ->
         pi "t"  tp $ \t ->
         pi "f" (tm ==> tm) $ \f ->
           (pi "x" tm $ \x ->
              typeof (var x) (var t2) ==> typeof (var f @@ var x) (var t))
           ==>
           typeof (lam "x" (\x -> var f @@ var x)) (arrow (var t2) (var t))
  , "of_nat_elim" :.
         pi "t" tp $ \t ->
         pi "z" tm $ \z ->
         pi "s" tm $ \s ->
         pi "n" tm $ \n ->
           typeof (var z) (var t) ==>
           typeof (var s)  (arrow (var t) (var t)) ==>
           typeof (var n) nat ==>
           typeof (nat_elim (var z) (var s) (var n)) (var t)

    -- STLC value judgements
  , "is_value" ::. tm ==> lf_type
  , "value_tt" :.
         is_value tt
  , "value_zero" :.
         is_value zero
  , "value_suc" :.
         pi "n" tm $ \n ->
           is_value (var n) ==> is_value (suc (var n))
  , "value_lam" :.
         pi "f" (tm ==> tm) $ \f ->
           is_value (lam "x" (\x -> var f @@ var x))

    -- STLC small-step CBV semantics
  , "step" ::. tm ==> tm ==> lf_type
  , "step_app1" :.
         pi "e₁" tm $ \e1 ->
         pi "e₂" tm $ \e2 ->
         pi "e₁'" tm $ \e1' ->
            step (var e1) (var e1') ==>
            step (app (var e1) (var e2)) (app (var e1') (var e2))
  , "step_app2" :.
         pi "e₁" tm $ \e1 ->
         pi "e₂" tm $ \e2 ->
         pi "e₂'" tm $ \e2' ->
            is_value (var e1) ==>
            step (var e2) (var e2') ==>
            step (app (var e1) (var e2)) (app (var e1) (var e2'))
  , "step_beta" :.
         pi "e₂" tm $ \e2 ->
         pi "f" (tm ==> tm) $ \f ->
            is_value (var e2) ==>
            step (app (lam "x" (\x -> var f @@ var x)) (var e2)) (var f @@ var e2)
  , "step_nat_zero" :.
         pi "z" tm $ \z ->
         pi "s" tm $ \s ->
           step (nat_elim (var z) (var s) zero) (var z)
  , "step_nat_succ" :.
         pi "z" tm $ \z ->
         pi "s" tm $ \s ->
         pi "n" tm $ \n ->
           step (nat_elim (var z) (var s) (suc (var n))) (app (var s) (nat_elim (var z) (var s) (var n)))

  , "F" :. tm

  , "f" :. tm --   A -> B -> C
  , "g" :. tm --   C -> B
  , "h" :. tm --   A -> C

  , "f'" :. tm --   A -> (B -> C)#
               --   A -> ((B -> C)* -> X) -> X
               --   A -> ((B -> (C -> X) -> X) -> X) -> X

  , "g'" :. tm --   C -> (B -> X) -> X
  , "h'" :. tm --   A -> (C -> X) -> X

  , "A" :. tp
  , "B" :. tp
  , "C" :. tp
  , "X" :. tp
  ]


tp :: WFContext γ => M (LF γ TYPE)
tp = tyConst "tp"

unit :: WFContext γ => M (LF γ TERM)
unit = tmConst "unit"

nat :: WFContext γ => M (LF γ TERM)
nat = tmConst "nat"

arrow :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM)
arrow x y = tmConst "arrow" @@ x @@ y

tm :: WFContext γ => M (LF γ TYPE)
tm = tyConst "tm"

tt :: WFContext γ => M (LF γ TERM)
tt = tmConst "tt"

zero :: WFContext γ => M (LF γ TERM)
zero = tmConst "zero"

suc :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM)
suc x = tmConst "suc" @@ x

infixl 5 `app`
app :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM)
app x y = tmConst "app" @@ x @@ y

lam :: (WFContext γ
       , ?nms :: Set String
       , ?hyps :: Hyps LF γ
       )
   => String
   -> (forall b. ( IsBoundVar b
                 , ?nms :: Set String
                 , ?hyps :: Hyps LF (γ ::> b)
                 )
         => Var (γ::>b) -> M (LF (γ::>b) TERM))
   -> M (LF γ TERM)
lam nm f = tmConst "lam" @@ (λ nm tm f)

nat_elim :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM)
nat_elim z s n = tmConst "nat_elim" @@ z @@ s @@ n

typeof :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TYPE)
typeof t p = tyConst "typeof" @@ t @@ p

of_suc :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TERM)
of_suc n prf = tmConst "of_suc" @@ n @@ prf

of_zero :: WFContext γ => M (LF γ TERM)
of_zero = tmConst "of_zero"

is_value :: WFContext γ => M (LF γ TERM) -> M (LF γ TYPE)
is_value v = tyConst "is_value" @@ v

step :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM) -> M (LF γ TYPE)
step x x' = tyConst "step" @@ x @@ x'


typing :: LF E TERM
typing = mkTerm sig $
  tmConst "of_lam" @@ nat @@ nat @@ λ"x" tm (\x -> suc (var x)) @@
     (λ"x" tm $ \x ->
       λ"prf" (typeof (var x) nat) $ \prf ->
         of_suc (var x) (var prf))

typing2 :: LF E TERM
typing2 = mkTerm sig $
  tmConst "of_lam" @@ nat @@ (arrow nat nat) @@
      (λ"x" tm (\x -> lam "y" $ \y -> nat_elim (var x) (lam "n" (\n -> suc (var n))) (var y))) @@
      (λ"x" tm $ \x ->
        λ"prf_x" (typeof (var x) nat) $ \prf_x ->
          tmConst "of_lam" @@ nat @@ nat @@
            (λ"y" tm $ \y -> nat_elim (var x) (lam "n" (\n -> suc (var n))) (var y)) @@
            (λ"y" tm $ \y ->
              λ"prf_y" (typeof (var y) nat) $ \prf_y ->
                tmConst "of_nat_elim" @@ nat @@ (var x) @@ (lam "n" (\n -> suc (var n))) @@ var y @@
                  var prf_x @@
                  (tmConst "of_lam" @@ nat @@ nat @@ (λ"n" tm (\n -> suc (var n))) @@
                    (λ"n" tm $ \n -> λ"prf_n" (typeof (var n) nat) $ \prf_n -> of_suc (var n) (var prf_n))) @@
                  var prf_y
            )
      )

pattern VarP v <-
  (termView -> VVar v [])
pattern AppP m1 m2 <-
  (termView -> VConst "app" [m1, m2])
pattern LamP m <-
  (termView -> VConst "lam" [m])
pattern NatElimP z s n <-
  (termView -> VConst "nat_elim" [z,s,n])
pattern ZeroP <-
  (termView -> VConst "zero" [])
pattern SucP n <-
  (termView -> VConst "suc" [n])
pattern ArrowP t1 t2 <-
  (termView -> VConst "arrow" [t1,t2])


cps :: ( WFContext γ, ?soln :: LFSoln LF
      , ?hyps :: H γ, ?nms :: Set String)
    => LF γ TERM
    -> M (LF γ TERM)

cps (LamP body) =
  λ "klam" (tm ==> tm) $ \k -> (var k) @@
     (lam "x" $ \x ->
       lam "k" $ \k ->
           (cps =<< ((return $ weaken $ weaken $ weaken body) @@
             (weaken <$> var x))) @@
             (λ "m" tm $ \m -> app (weaken <$> var k) (var m)))

cps (AppP x y) =
  λ "k" (tm ==> tm) $ \k ->
      cps (weaken x) @@ (λ "m" tm $ \m ->
        cps (weaken $ weaken $ y) @@ (λ "n" tm $ \n ->
          (weaken <$> var m) `app`
          (var n) `app`
          (lam "q" $ \q -> (weaken . weaken . weaken <$> var k) @@ var q)))

cps (SucP x) =
  λ "k" (tm ==> tm) $ \k ->
    cps (weaken x) @@ (λ "n" tm $ \n -> (weaken <$> var k) @@ suc (var n))

cps (termView -> VConst "f" []) =
  λ "k" (tm ==> tm) $ \k ->
    var k @@ (liftClosed <$> tmConst "f'")

cps (termView -> VConst "g" []) =
  λ "k" (tm ==> tm) $ \k ->
    var k @@ (liftClosed <$> tmConst "g'")

cps (termView -> VConst "h" []) =
  λ "k" (tm ==> tm) $ \k ->
    var k @@ (liftClosed <$> tmConst "h'")

cps x =
  λ "k" (tm ==> tm) $ \k ->
    var k @@ (return $ weaken x)




addConstraint
   :: M (LF E CON)
   -> StateT [LF E CON] M ()
addConstraint c = do
   x <- lift c
   modify (x:)

tc :: ( WFContext γ, ?soln :: LFSoln LF
      , ?hyps :: H γ, ?nms :: Set String)
   => Subst M LF γ E
   -> LF γ TERM
   -> StateT [LF E CON] M (LF E TERM)

tc sub (VarP v) =
  lift (lookupSubst v sub)

tc _ ZeroP =
  lift nat

tc sub (SucP n) = do
  t <- tc sub n
  addConstraint $
     unify (return t) nat
  return t

tc sub (LamP (termView -> VLam _nm w _v _t m)) = do
  t1 <- lift (uvar =<< freshUVar =<< tp)
  let sub' = SubstApply (weakSubst w sub)
                        (\_ -> return $ liftClosed t1)
  t2 <- tc sub' m
  lift (arrow (return t1) (return t2))

tc sub (AppP m1 m2) = do
  tf    <- tc sub m1
  targ  <- tc sub m2
  tres  <- lift (uvar =<< freshUVar =<< tp)
  addConstraint $
     unify (return tf) (arrow (return targ) (return tres))
  return tres

tc sub (NatElimP z s n) = do
  tyz <- tc sub z
  tys <- tc sub s
  tyn <- tc sub n
  addConstraint $
     unify (return tys) (arrow (return tyz) (return tyz))
  addConstraint $
     unify (return tyn) nat
  return tyz

tc _ (termView -> VConst "f" []) = do
  lift $ arrow (tmConst "A") (arrow (tmConst "B") (tmConst "C"))
tc _ (termView -> VConst "g" []) = do
  lift $ arrow (tmConst "C") (tmConst "B")
tc _ (termView -> VConst "h" []) = do
  lift $ arrow (tmConst "A") (tmConst "C")


tc _ (termView -> VConst "f'" []) = do
  tans  <- lift (uvar =<< freshUVar =<< tp)
  lift $ arrow (tmConst "A")
          (arrow (arrow (arrow (tmConst "B")
                          (arrow (arrow (tmConst "C") (return tans)) (return tans)))
                   (return tans)
                )
           (return tans))

tc _ (termView -> VConst "g'" []) = do
  tans  <- lift (uvar =<< freshUVar =<< tp)
  lift $ arrow (tmConst "C") (arrow (arrow (tmConst "B") (return tans)) (return tans))
tc _ (termView -> VConst "h'" []) = do
  tans  <- lift (uvar =<< freshUVar =<< tp)
  lift $ arrow (tmConst "A") (arrow (arrow (tmConst "C") (return tans)) (return tans))

tc _sub m = do
  doc <- lift $ ppLF TopPrec m
  fail $ unlines ["Typechecking failed, unrecognized term:"
                 , show (indent 2 doc)
                 ]


runTC :: LF E TERM -> M (LF E GOAL)
runTC tm = withCurrentSolution $ inEmptyCtx $ do
  (ty, cs) <- flip runStateT [] $ tc SubstRefl tm
  (cs', soln) <- solve =<< conj (map return cs)
  commitSolution soln
  let ?soln = soln
  ty' <- runChangeT $ instantiate ty
  goal (return ty') (return cs')




-- CBV reduction to head-normal form
eval :: (?nms :: Set String, ?hyps :: H γ, WFContext γ, ?soln :: LFSoln LF)
     => LF γ TERM
     -> ChangeT M (LF γ TERM)

-- β reduction
eval (AppP (LamP body) arg) = do
    arg' <- eval arg
    eval =<< Changed (return body @@ return arg')

-- structural evaluation under application
eval tm@(AppP m1 m2) = do
    case eval m1 of
      Unchanged _ ->
        case eval m2 of
          Unchanged _ -> Unchanged tm
          Changed m2' -> eval =<< Changed (app (return m1) m2')
      Changed m1' ->
        eval =<< Changed (app m1' (return m2))

-- evaluation under lambdas
eval tm@(LamP (termView -> VLam nm wk _var tp body)) = do
    case eval body of
      Changed body' -> do
        Changed (tmConst "lam" @@ (weakening wk <$> mkLam nm (return tp) body'))
      _ -> Unchanged tm

-- nat recursor: zero case
eval (NatElimP z _s ZeroP) =
    Changed (return z)

-- nat recursor: successor case
eval (NatElimP z s (SucP n)) =
    eval =<< Changed (return s `app` (nat_elim (return z) (return s) (return n)))

eval t = Unchanged t


five :: M (LF E TERM)
five = inEmptyCtx $ suc $ suc $ suc $ suc $ suc $ zero

three :: M (LF E TERM)
three = inEmptyCtx $ suc $ suc $ suc $ zero

add :: M (LF E TERM)
add = inEmptyCtx $
  lam "x" $ \x ->
  lam "y" $ \y ->
    nat_elim (var x) (lam "n" $ \n -> suc (var n)) (var y)

composeN :: M (LF E TERM)
composeN = inEmptyCtx $
  lam "f" $ \f ->
    lam "n" $ \n ->
      nat_elim (lam "q" $ \q -> var q)
               (lam "g" $ \g ->
                  lam "q" $ \q ->
                    var f `app` (var g `app` var q))
               (var n)

f :: WFContext γ => M (LF γ TERM)
f = liftClosed <$> tmConst "f"

g :: WFContext γ => M (LF γ TERM)
g = liftClosed <$> tmConst "g"

h :: WFContext γ => M (LF γ TERM)
h = liftClosed <$> tmConst "h"

testTerm :: LF E TERM
testTerm = mkTerm sig $
  lam "x" $ \x -> (f `app` var x) `app` (g `app` (h `app` var x))

  --lam "x" $ \x -> g `app` (h `app` var x)

  --mkTerm sig $ add `app` three
  --mkTerm sig $ composeN `app` (lam "q" $ \q -> tmConst "F" `app` var q) `app` three --`app` tt


evalTerm :: LF E TERM
evalTerm = mkTerm sig $ runChangeT $ eval testTerm

cpsTerm :: LF E TERM
cpsTerm = mkTerm sig $ do
      x <- cps testTerm @@ (λ "z" tm $ \z -> var z)
      return x
      --runChangeT $ eval x

main = inEmptyCtx $ do
   let x :: LF E TERM
       x = cpsTerm
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec x
   putStrLn ""
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ (ppLF TopPrec =<< inferType x)
   putStrLn ""

   let g :: LF E GOAL
       g = runM sig $ runTC x
       --g = runM sig $ (runTC =<< composeN)
       --g = runM sig $ (runTC =<< add)
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec g
   putStrLn ""
