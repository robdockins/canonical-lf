{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wwarn #-}
module Main where

import Prelude hiding (pi, abs)

--import Control.Monad.Trans.Class
--import Control.Monad.State
--import           Data.Sequence (Seq, (|>))
--import qualified Data.Sequence as Seq
import           Data.Set (Set)
--import qualified Data.Set as Set
--import           Data.Map (Map)
--import qualified Data.Map as Map
import           Data.String
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF
--import           Lang.LF.ChangeT
import           Lang.LF.Tree hiding (M)
import qualified Lang.LF.Tree as Tree

--import qualified Debug.Trace as Debug

data TyConst
   = TNm String
 deriving (Eq, Ord, Show)

instance Pretty TyConst where
  pretty (TNm x) = pretty x
instance IsString TyConst where
  fromString = TNm

data TmConst
   = CNm String
 deriving (Eq, Ord, Show)

instance Pretty TmConst where
  pretty (CNm x) = pretty x
instance IsString TmConst where
  fromString = CNm


type LF = Tree.LFTree TyConst TmConst
type Sig = Tree.Signature TyConst TmConst
type M = Tree.M TyConst TmConst
type H = Hyps LF

-- Signature for the language λᵁCPS from Andrew Kennedy's
-- "Compiling with Continuations, Continued" (ICFP 2007)
sig :: Sig
sig = buildSignature
  [ "tm"       ::. lf_type
  , "val"      ::. lf_type
  , "ml"       ::. lf_type
  , "v"        ::. lf_type
  , "kv"       ::. lf_type

  , "letval"   :. val ==> (v ==> tm) ==> tm
  , "letcont"  :. (v ==> tm) ==> (kv ==> tm) ==> tm
  , "let_prj1" :. v ==> (v ==> tm) ==> tm
  , "let_prj2" :. v ==> (v ==> tm) ==> tm
  , "app"      :. v ==> kv ==> v ==> tm
  , "case"     :. v ==> kv ==> kv ==> tm
  , "enter"    :. kv ==> v ==> tm

  , "tt"       :. val
  , "pair"     :. v ==> v ==> val
  , "inl"      :. v ==> val
  , "inr"      :. v ==> val
  , "lam"      :. (kv ==> v ==> tm) ==> val

  , "ml_var"    :. v ==> ml
  , "ml_app"    :. ml ==> ml ==> ml
  , "ml_lam"    :. (v ==> ml) ==> ml
  , "ml_pair"   :. ml ==> ml ==> ml
  , "ml_fst"    :. ml ==> ml
  , "ml_snd"    :. ml ==> ml
  , "ml_tt"     :. ml
  , "ml_inl"    :. ml ==> ml
  , "ml_inr"    :. ml ==> ml
  , "ml_letval" :. ml ==> (v ==> ml) ==> ml
  , "ml_case"   :. ml ==> (v ==> ml) ==> (v ==> ml) ==> ml

  , "f" :. v
  , "y" :. v
  , "halt"     :. kv
  ]


instance LiftClosed γ => IsString (M (LF γ TYPE)) where
  fromString = tyConst . TNm

instance LiftClosed γ => IsString (M (LF γ TERM)) where
  fromString = tmConst . CNm

tm :: LiftClosed γ => M (LF γ TYPE)
tm = tyConst "tm"

val :: LiftClosed γ => M (LF γ TYPE)
val = tyConst "val"

v :: LiftClosed γ => M (LF γ TYPE)
v = tyConst "v"

kv :: LiftClosed γ => M (LF γ TYPE)
kv = tyConst "kv"

ml :: LiftClosed γ => M (LF γ TYPE)
ml = tyConst "ml"



cps_ml :: (LiftClosed γ, ?nms :: Set String, ?hyps :: H γ, ?soln :: LFSoln LF)
       => LF γ TERM -- ^ ML term to transform  :: ml
       -> LF γ TERM -- ^ static continuation :: (v ==> tm)
       -> M (LF γ TERM) -- ^ cps transformed term :: tm
cps_ml (termView -> VConst (CNm "ml_var") [x]) k_top =
  (return k_top) @@ (return x)

cps_ml (termView -> VConst "ml_tt" []) k_top =
  "letval" @@ "tm_tt" @@ (return $ k_top)

cps_ml (termView -> VConst "ml_app" [e1,e2]) k_top =
  cps_ml e1 =<< (λ "z1" v $ \z1 ->
    cps_ml (weak e2) =<< (λ "z2" v $ \z2 ->
      "letcont" @@ (return $ weak $ weak k_top)
                @@ (λ "k" kv $ \k ->
                      "app" @@ (weak . weak <$> var z1)
                            @@ (var k)
                            @@ (weak <$> var z2))))

cps_ml (termView -> VConst "ml_pair" [e1,e2]) k_top =
  cps_ml e1 =<< (λ "z1" v $ \z1 ->
    cps_ml (weak e2) =<< (λ "z2" v $ \z2 ->
      "letval" @@ ("pair" @@ (weak <$> var z1) @@ (var z2))
               @@ (return $ weak $ weak k_top)))

cps_ml (termView -> VConst "ml_inl" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "letval" @@ ("inl" @@ var z)
              @@ (return $ weak k_top))

cps_ml (termView -> VConst "ml_inr" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "letval" @@ ("inr" @@ var z)
              @@ (return $ weak k_top))

cps_ml (termView -> VConst "ml_fst" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "let_prj1" @@ var z
                @@ (return $ weak k_top))

cps_ml (termView -> VConst "ml_snd" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "let_prj2" @@ var z
                @@ (return $ weak k_top))

cps_ml (termView -> VConst "ml_lam" [e]) k_top =
  "letval" @@ ("lam" @@ (λ "k" kv $ \k ->
                          (λ "x" v $ \x -> do
                            x' <- (return $ weak $ weak $ e) @@ (var x)
                            tailcps_ml x' =<< (weak <$> var k))))
           @@ (return k_top)

cps_ml (termView -> VConst "ml_letval" [e1,e2]) k_top =
  "letcont" @@ (λ "x" v $ \x -> do
                   x' <- (return $ weak $ e2) @@ (var x)
                   cps_ml x' (weak k_top))
            @@ (λ "j" kv $ \j -> do
                   tailcps_ml (weak $ e1) =<< (var j))

cps_ml (termView -> VConst "ml_case" [e,el,er]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
    "letcont" @@ (return $ weak $ k_top)
      @@ (λ "j" kv $ \j ->
      "letcont" @@ (λ "x1" v $ \x1 -> do
                         el' <- (return $ weak $ weak $ weak el) @@ var x1
                         tailcps_ml el' =<< (weak <$> var j))
        @@ (λ "k1" kv $ \k1 ->
          "letcont" @@ (λ "x2" v $ \x2 -> do
                           er' <- (return $ weak $ weak $ weak $ weak er) @@ var x2
                           tailcps_ml er' =<< (weak . weak <$> var j))
            @@ (λ "k2" kv $ \k2 ->
               "case" @@ (weak . weak . weak <$> var z) @@ (weak <$> var k1) @@ var k2))))

cps_ml tm _ = do
  tm_doc <- ppLF TopPrec WeakRefl tm
  fail $ show $ vcat
     [ text "Unexpected term in cps_ml:"
     , indent 2 tm_doc
     ]

tailcps_ml :: (LiftClosed γ, ?nms :: Set String, ?hyps :: H γ, ?soln :: LFSoln LF)
       => LF γ TERM -- ^ ML term to transform :: ml
       -> LF γ TERM -- ^ a continuation variable :: kv
       -> M (LF γ TERM) -- ^ result :: tm

tailcps_ml (termView -> VConst "ml_var" [x]) k_top =
  "enter" @@ return k_top @@ return x

tailcps_ml (termView -> VConst "ml_app" [e1,e2]) k_top =
  cps_ml e1 =<< (λ "x1" v $ \x1 ->
    cps_ml (weak e2) =<< (λ "x2" v $ \x2 ->
      "app" @@ (weak <$> var x1) @@ (return $ weak $ weak k_top) @@ (var x2)))

tailcps_ml (termView -> VConst "ml_lam" [e]) k_top =
  "letval" @@ ("lam" @@ (λ "j" kv $ \j -> λ "x" v $ \x -> do
                           e' <- (return $ weak $ weak e) @@ (var x)
                           tailcps_ml e' =<< (weak <$> var j)))
           @@ (λ "f" v $ \f -> "enter" @@ (return $ weak $ k_top) @@ (var f))

tailcps_ml (termView -> VConst "ml_pair" [e1,e2]) k_top =
  cps_ml e1 =<< (λ "x1" v $ \x1 ->
    cps_ml (weak e2) =<< (λ "x2" v $ \x2 ->
      "letval" @@ ("pair" @@ (weak <$> var x1) @@ (var x2))
               @@ (λ "x" v $ \x ->
                     "enter" @@ (return $ weak $ weak $ weak $ k_top) @@ (var x))))

tailcps_ml (termView -> VConst "ml_inl" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "letval" @@ ("inl" @@ var z)
              @@ (λ "x" v $ \x ->
                    "enter" @@ (return $ weak $ weak k_top) @@ var x))

tailcps_ml (termView -> VConst "ml_tt" []) k_top =
  "letval" @@ "tt"
           @@ (λ "x" v $ \x -> 
                "enter" @@ (return $ weak k_top) @@ var x)

tailcps_ml (termView -> VConst "ml_fst" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "let_prj1" @@ var z
                @@ (λ "x" v $ \x -> 
                     "enter" @@ (return $ weak $ weak k_top) @@ var x))

tailcps_ml (termView -> VConst "ml_snd" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "let_prj2" @@ var z
                @@ (λ "x" v $ \x -> 
                     "enter" @@ (return $ weak $ weak k_top) @@ var x))

tailcps_ml (termView -> VConst "ml_letval" [e1,e2]) k_top =
  "letcont" @@ (λ "x" v $ \x -> do
                   e2' <- (return $ weak $ e2) @@ (var x)
                   tailcps_ml e2' (weak k_top))
            @@ (λ "j" kv $ \j -> do
                   tailcps_ml (weak e1) =<< (var j))

tailcps_ml (termView -> VConst "ml_case" [e,el,er]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
    "letcont" @@ (λ "x1" v $ \x1 -> do
                     el' <- (return $ weak $ weak el) @@ (var x1)
                     tailcps_ml el' (weak $ weak k_top))
      @@ (λ "k1" kv $ \k1 ->
        "letcont" @@ (λ "x2" v $ \x2 -> do
                        er' <- (return $ weak $ weak $ weak er) @@ (var x2)
                        tailcps_ml er' (weak $ weak $ weak k_top))
           @@ (λ "k2" kv $ \k2 ->
                "case" @@ (weak . weak <$> var z)
                       @@ (weak <$> var k1)
                       @@ (var k2))))

tailcps_ml tm _ = do
  tm_doc <- ppLF TopPrec WeakRefl tm
  fail $ show $ vcat
     [ text "Unexpected term in tailcps_ml:"
     , indent 2 tm_doc
     ]


testTerm :: LF E TERM
testTerm = mkTerm sig $
  "ml_lam" @@ (λ "x" v $ \x ->
                 "ml_app" @@ ("ml_var" @@ "f")
                          @@ ("ml_pair" @@ ("ml_var" @@ (var x)) @@ ("ml_var" @@ "y")))

data BindData (γ :: Ctx *) where
  BindEmpty   :: BindData E
  BindLetcont :: BindData γ
              -> LF γ TERM {- :: v ==> term -}
              -> BindData (γ ::> b)
  BindLetval  :: BindData γ
              -> LF γ TERM {- :: val  -}
              -> BindData (γ ::> b)
  BindLetinj  :: BindData γ
              -> Bool {- left or right -}
              -> LF γ TERM {- :: v -}
              -> BindData (γ ::> b)

strengthenVar :: Weakening γ γ'
              -> Var γ'
              -> Maybe (Var γ)
strengthenVar = undefined

simplifier :: (LiftClosed γ, ?hyps :: H γ, ?nms :: Set String, ?soln :: LFSoln LF)
           => BindData γ
           -> LF γ TERM
           -> M (LF γ TERM)
simplifier bd (termView -> VConst "letval" [v,m]) = do
   let hyps = ?hyps
   let bd' = BindLetval bd v
   case termView v of
     VConst "lam" [termView -> VLam _ k _ (termView -> VLam _ x _ (termView ->
                        VConst "app" [ termView -> VVar g []
                                     , termView -> VVar k' []
                                     , termView -> VVar x' []
                                     ]))]
        | F (F g') <- g
        , F k == k'
        , x == x' ->
             let ?hyps = hyps in
             simplifier bd =<< (return m) @@ (var g')

--  "letval" @@ "tt" @@ (λ "x" v $ \x -> "tm_var" @@ var x)

cpsTerm :: LF E TERM
cpsTerm = mkTerm sig $ do
  cps_ml testTerm =<< (λ "z" v $ \z -> "enter" @@ "halt" @@ var z)

main = inEmptyCtx $ do
   let x :: LF E TERM
       x = cpsTerm
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec WeakRefl x
   putStrLn ""
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $ (ppLF TopPrec WeakRefl =<< inferType WeakRefl x)
   putStrLn ""
