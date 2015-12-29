{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wwarn #-}
module Main where

import Prelude hiding (pi, abs)

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

--import qualified Debug.Trace as Debug

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

lam :: WFContext γ
    => String
    -> (forall b. IsBoundVar b => Var (γ::>b) -> M (LF (γ::>b) TERM))
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

typecheck :: forall γ γ'
           . (?nms :: Set String, ?hyps :: H γ, ?hyps' :: H γ'
             , WFContext γ', WFContext γ, ?soln :: LFSoln LF)
          => Subst M LF γ γ'
          -> LF γ TERM
          -> M (LF γ' GOAL)
          
typecheck sub (termView -> VVar v []) =
   goal (hsubst sub =<< var v) cTrue

typecheck _ ZeroP = goal nat cTrue

typecheck sub (SucP n) = do
   g <- typecheck sub n
   let ?hyps = ?hyps'
   underGoal' g $ \ty c ->
     goal nat (conj [return c, unify (return ty) nat])

typecheck sub (LamP (termView -> VLam nm k)) =
  sigma ("t_"++nm) tp $ \(t :: Var (γ'::>b)) -> do
    (g :: LF (γ'::>b) GOAL)
       <- k $ \w _v _a m -> do
                 tp' <- tp
                 let ?hyps' = extendHyps ?hyps' ("t_"++nm) QSigma tp'
                 typecheck (SubstApply (SubstWeak (SubstSkip (weakSubst w sub)))
                                       (\_ -> var t))
                             m
    tp' <- tp
    let ?hyps = extendHyps ?hyps' "t" QSigma tp'
    underGoal g $ \wk xty c ->
      goal (arrow (wk <$> (var t)) (return xty)) (return c)

typecheck sub (AppP x y) = do
  g1 <- typecheck sub x
  g2 <- typecheck sub y
  let ?hyps = ?hyps'
  underGoal g1 $ \wk1 ty1 c1 -> do
    underGoal (wk1 g2) $ \wk2 ty2 c2 -> do
      sigma "tbody" tp $ \tbody ->
         goal (var tbody)
              (conj [ return $ weaken $ wk2 c1
                    , return $ weaken $ c2
                    , unify (arrow (return $ weaken ty2) (var tbody))
                            (return $ weaken $ wk2 $ ty1)
                    ])

typecheck sub (NatElimP z s n) = do
  gz <- typecheck sub z
  gs <- typecheck sub s
  gn <- typecheck sub n
  sigma "t" tp $ \t -> do
    tp' <- tp
    let ?hyps = extendHyps ?hyps' "t" QSigma tp'
    underGoal (weaken gz) $ \wk1 tyz cz ->
      underGoal (wk1 $ weaken gs) $ \wk2 tys cs ->
        underGoal (wk2 $ wk1 $ weaken gn) $ \wk3 tyn cn -> do
          t' <- wk3 . wk2 . wk1 <$> var t 
          goal (return t')
               (conj [ unify (return $ tyn) nat
                     , unify (return $ wk3 $ wk2 $ tyz) (return t')
                     , unify (return $ wk3 $ tys) (arrow (return t') (return t'))
                     , return $ wk3 $ wk2 cz
                     , return $ wk3 $ cs
                     , return cn])


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
eval tm@(LamP (termView -> VLam nm k)) =
  k $ \wk _var tp body -> do
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
five = suc $ suc $ suc $ suc $ suc $ zero

three :: M (LF E TERM)
three = suc $ suc $ suc $ zero

add :: M (LF E TERM)
add = lam "x" $ \x ->
      lam "y" $ \y ->
        nat_elim (var x) (lam "n" $ \n -> suc (var n)) (var y)

composeN :: M (LF E TERM)
composeN =
  lam "f" $ \f ->
    lam "n" $ \n ->
      nat_elim (lam "q" $ \q -> var q)
               (lam "g" $ \g ->
                  lam "q" $ \q ->
                    var f `app` (var g `app` var q))
               (var n)

testTerm :: LF E TERM
testTerm =
  mkTerm sig $ add `app` three `app` five
  --mkTerm sig $ composeN `app` (lam "q" $ \q -> tmConst "F" `app` var q) `app` five `app` tt


evalTerm :: LF E TERM
evalTerm = inEmptyCtx $
   mkTerm sig $ runChangeT $ eval testTerm

main = inEmptyCtx $ do
{-
   let x :: LF E TERM
       x = evalTerm
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec x
   putStrLn ""
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ (ppLF TopPrec =<< inferType x)
   putStrLn ""
-}

   let ?hyps' = ?hyps 
   let x :: LF E GOAL
       --x = runM sig $ (typecheck SubstRefl =<< add)
       x = runM sig $ (typecheck SubstRefl =<< composeN)
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec x
   putStrLn ""
   --displayIO stdout $ renderSmart 0.7 80 $ runM sig $ (ppLF TopPrec =<< inferType x)
   --putStrLn ""
