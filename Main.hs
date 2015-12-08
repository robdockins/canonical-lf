{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wwarn #-}
module Main where

import Prelude hiding (pi, abs)

--import           Data.Sequence (Seq, (|>))
--import qualified Data.Sequence as Seq
import qualified Data.Set as Set
--import           Data.Map (Map)
--import qualified Data.Map as Map
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF
--import           Lang.LF.ChangeT
import           Lang.LF.Tree hiding (M)
import qualified Lang.LF.Tree as Tree

--import qualified Debug.Trace as Debug

type LF = Tree.LFTree String String
type Sig = Tree.Signature String String
type M = Tree.M String String


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
           typeof (lam (λ"x" tm (\x -> var f @@ var x))) (arrow (var t2) (var t))
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
           is_value (lam (λ "x" tm (\x -> var f @@ var x)))

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
            step (app (lam (λ "x" tm (\x -> var f @@ var x))) (var e2)) (var f @@ var e2)
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

lam :: WFContext γ => M (LF γ TERM) -> M (LF γ TERM)
lam f = tmConst "lam" @@ f

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
      (λ"x" tm (\x -> lam (λ"y" tm $ \y -> nat_elim (var x) (lam (λ"n" tm (\n -> suc (var n)))) (var y)))) @@
      (λ"x" tm $ \x ->
        λ"prf_x" (typeof (var x) nat) $ \prf_x ->
          tmConst "of_lam" @@ nat @@ nat @@
            (λ"y" tm $ \y -> nat_elim (var x) (lam (λ"n" tm (\n -> suc (var n)))) (var y)) @@
            (λ"y" tm $ \y ->
              λ"prf_y" (typeof (var y) nat) $ \prf_y ->
                tmConst "of_nat_elim" @@ nat @@ (var x) @@ (lam (λ"n" tm (\n -> suc (var n)))) @@ var y @@
                  var prf_x @@
                  (tmConst "of_lam" @@ nat @@ nat @@ (λ"n" tm (\n -> suc (var n))) @@
                    (λ"n" tm $ \n -> λ"prf_n" (typeof (var n) nat) $ \prf_n -> of_suc (var n) (var prf_n))) @@
                  var prf_y
            )
      )

{-
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

typecheck, typecheck' :: Map (LFVar LF) (M (LF TERM)) -> LF TERM -> M (LF GOAL)

typecheck γ x = do
  ctx <- dumpContext
  tm  <- ppLF TopPrec x
  g <- Debug.trace (unlines ["Typechecking:"
                       , show ctx
                       , "----------"
                       , show tm
                       ]) $ typecheck' γ x
  gdoc <- ppLF TopPrec g
  Debug.trace (unlines ["Typecheck goal:"
                       , show ctx
                       , "----------"
                       , show gdoc
                       ]) $ return g

typecheck' γ (termView -> VVar m) = m $ \v [] -> do
  Debug.trace ("lookup of var: " ++ show v) $ do
   case Map.lookup v γ of
     Just tm -> goal tm cTrue
     Nothing -> do
        nm <- lookupVariableName v
        dctx <- dumpContext
        fail $ unlines [ unwords ["Type variable not bound!", nm]
                       , show dctx
                       ]
typecheck' _ ZeroP = goal nat cTrue
typecheck' γ (SucP n) = do
  g <- typecheck γ n
  underGoal g $ \ty c ->
     goal nat (conj [return c, unify (return ty) nat])

typecheck' γ (LamP (termView -> VLam m)) = do
  m (const return) $ \v x -> do
     vnm <- lookupVariableName v
     sigma ("t_"++vnm) tp $ \t -> do
       g <- typecheck (Map.insert v (var t) γ) =<< (runChangeT $ weaken 0 1 x)
       underGoal g $ \xty c ->
          strengthen v =<< goal (arrow (var t) (return xty)) (return c)

typecheck' γ (AppP x y) = do
  g1 <- typecheck γ x
  underGoal g1 $ \ty1 c1 ->
    case ty1 of
      ArrowP tArg tBody -> do
        g2 <- typecheck γ =<< (autoweaken (return y))
        underGoal g2 $ \ty2 c2 -> do
          goal (return tBody) (conj [return c1, return c2, unify (return tArg) (return ty2)])
      _ -> fail "Expected function type"
typecheck' γ (NatElimP z s n) = do
  gz <- typecheck γ z
  gs <- typecheck γ s
  gn <- typecheck γ n
  sigma "t" tp $ \t ->
    underGoal gz $ \tyz cz ->
      underGoal gs $ \tys cs ->
        underGoal gn $ \tyn cn ->
          goal (var t) (conj [ unify (return tyn) nat
                             , unify (return tyz) (var t)
                             , unify (return tys) (arrow (var t) (var t))
                             , return cz, return cs, return cn])
{-    
typecheck (LamP t m) = do
  g <- typecheck m
  underGoal g $ \p c ->
     goal (tmConst "of_lam" @@ return t @@ return 
-}

-- CBV reduction to head-normal form
eval :: LF TERM -> ChangeT M (LF TERM)

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
eval tm@(LamP m) =
    case underLambda m eval of
      Changed m' -> Changed (lam m')
      _ -> Unchanged tm

-- nat recursor: zero case
eval (NatElimP z _s ZeroP) =
    Changed (return z)

-- nat recursor: successor case
eval (NatElimP z s (SucP n)) =
    eval =<< Changed (return s `app` (nat_elim (return z) (return s) (return n)))

eval t = Unchanged t

-}

five :: M (LF E TERM)
five = suc $ suc $ suc $ suc $ suc $ zero

three :: M (LF E TERM)
three = suc $ suc $ suc $ zero

add :: M (LF E TERM)
add = lam (λ"x" tm $ \x ->
      lam (λ"y" tm $ \y ->
        nat_elim (var x) (lam (λ"n" tm $ \n -> suc (var n))) (var y)))

composeN :: M (LF E TERM)
composeN = do
  lam (λ"f" tm $ \f ->
    lam (λ"n" tm $ \n ->
      nat_elim (lam (λ"q" tm $ \q -> var q))
               (lam (λ"g" tm $ \g ->
                  lam (λ"q" tm $ \q ->
                    var f `app` (var g `app` var q))))
               (var n)))

testTerm :: LF E TERM
testTerm =
  --mkTerm sig $ composeN unit `app` (lam unit (λ"q" tm $ \q -> tmConst "F" `app` q)) `app` five -- `app` tt
  mkTerm sig $ add `app` three `app` five

--evalTerm :: LF TERM
--evalTerm = mkTerm sig $ runChangeT $ eval testTerm


main = sig `seq` do
{-
   let x :: LF GOAL
       x = runM sig $ (typecheck Map.empty =<< add)
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec x
   putStrLn ""
   --displayIO stdout $ renderSmart 0.7 80 $ runM sig $ (ppLF TopPrec =<< inferType x)
   --putStrLn ""
-}

   let x :: LF E TERM
       x = typing2
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec Set.empty HNil x
   putStrLn ""
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $
     (ppLF TopPrec Set.empty HNil =<< inferType Set.empty HNil x)
   putStrLn ""
