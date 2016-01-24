{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wwarn #-}
module Ucps where

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
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF
--import           Lang.LF.ChangeT
import           Lang.LF.Tree hiding (M)
import qualified Lang.LF.Tree as Tree

import qualified Debug.Trace as Debug

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
  , "g" :. v
  , "g'" :. v
  , "g''" :. v
  , "y" :. v
  , "x2" :. v
  , "x3" :. v
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
  "letval" @@ "tt" @@ (return $ k_top)

cps_ml (termView -> VConst "ml_app" [e1,e2]) k_top =
 "letcont" @@ (return k_top)
           @@ (λ "k" kv $ \k ->
   cps_ml (weak e1) =<< (λ "z1" v $ \z1 ->
     cps_ml (weak $ weak e2) =<< (λ "z2" v $ \z2 ->
                      "app" @@ (weak <$> var z1)
                            @@ (weak . weak <$> var k)
                            @@ (var z2))))

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

tailcps_ml (termView -> VConst "ml_inr" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "letval" @@ ("inr" @@ var z)
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



data BindData (γ :: Ctx *) where
  BindEmpty   :: BindData E
  BindLetcont :: BindData γ
              -> LF γ TERM {- :: v ==> term -}
              -> BindData (γ ::> b)
  BindOpaque  :: BindData γ
              -> BindData (γ ::> b)
  BindLetval  :: BindData γ
              -> LF γ TERM {- :: val  -}
              -> BindData (γ ::> b)
  BindLetproj :: BindData γ
              -> Bool {- False = fst, True = snd -}
              -> LF γ TERM {- :: v -}
              -> BindData (γ ::> b)

lookupContData :: BindData γ
               -> Var γ
               -> Maybe (LF γ TERM)
lookupContData = go WeakRefl
 where go :: Weakening γ γ' -> BindData γ -> Var γ -> Maybe (LF γ' TERM)
       go w (BindLetcont bd _)   (F v) = go (WeakL w) bd v
       go w (BindOpaque bd)      (F v) = go (WeakL w) bd v
       go w (BindLetval  bd _)   (F v) = go (WeakL w) bd v
       go w (BindLetproj bd _ _) (F v) = go (WeakL w) bd v
       go w (BindLetcont  _ v)   B     = Just (weaken (WeakL w) v)
       go _ _                    _     = Nothing

lookupValData :: BindData γ
              -> Var γ
              -> Maybe (LF γ TERM)
lookupValData = go WeakRefl
 where go :: Weakening γ γ' -> BindData γ -> Var γ -> Maybe (LF γ' TERM)
       go w (BindLetcont bd _)   (F v) = go (WeakL w) bd v
       go w (BindOpaque bd)      (F v) = go (WeakL w) bd v
       go w (BindLetval  bd _)   (F v) = go (WeakL w) bd v
       go w (BindLetproj bd _ _) (F v) = go (WeakL w) bd v
       go w (BindLetval  _  v) B     = Just (weaken (WeakL w) v)
       go _ _                  _     = Nothing

lookupProjData :: BindData γ
              -> Var γ
              -> Maybe (Bool, LF γ TERM)
lookupProjData = go WeakRefl
 where go :: Weakening γ γ' -> BindData γ -> Var γ -> Maybe (Bool, LF γ' TERM)
       go w (BindLetcont bd _)   (F v) = go (WeakL w) bd v
       go w (BindOpaque bd)      (F v) = go (WeakL w) bd v
       go w (BindLetval  bd _)   (F v) = go (WeakL w) bd v
       go w (BindLetproj bd _ _) (F v) = go (WeakL w) bd v
       go w (BindLetproj _ b v)  B     = Just (b, weaken (WeakL w) v)
       go _ _                    _     = Nothing


dropData :: Var γ
         -> Int
         -> BindData γ
         -> BindData γ
dropData v n bd
  | n <= 1 = bd
  | otherwise = go bd v
 where go :: BindData γ -> Var γ -> BindData γ
       go (BindLetcont bd k)   (F v) = BindLetcont (go bd v) k
       go (BindOpaque bd)      (F v) = BindOpaque (go bd v)
       go (BindLetval bd val)  (F v) = BindLetval (go bd v) val
       go (BindLetproj bd x y) (F v) = BindLetproj (go bd v) x y
       go (BindLetcont bd _)   B     = BindOpaque bd
       go (BindLetval bd _)    B     = BindOpaque bd
       go (BindLetproj bd _ _) B     = BindOpaque bd
       go bd                   _     = bd

strengthenVar :: Weakening γ γ'
              -> Var γ'
              -> Maybe (Var γ)
strengthenVar = undefined

simplifier :: forall γ
            . (LiftClosed γ, ?hyps :: H γ, ?nms :: Set String, ?soln :: LFSoln LF)
           => BindData γ
           -> LF γ TERM
           -> M (LF γ TERM)

simplifier bd (termView -> VConst "letcont" [k,m]) = do
   -- first, simplify inside the bound continuation body
   k' <- case termView k of
            VLam nm x t km -> do
               q <- simplifier (BindOpaque bd) km
               mkLam nm x t q
            _ -> fail "simplifier: expected function in 'letcont'"

   case tryEtaCont k' of
     Just j ->
       Debug.trace "η-CONT" $ do
         j' <- j
         m' <- return m @@ return j'
         let bd' = case termView j' of
                     VVar vj [] -> dropData vj (varCensus vj m') bd
                     _ -> bd
         simplifier bd' m'

     _ -> do
        -- next, simplify inside the body of the 'letcont'
        case termView m of
            VLam nm x t m' -> do
              q <- if (varCensus x m' == 1) then do
                      Debug.trace ("β-CONT-LIN " ++ show (varCensus x m')) $
                        simplifier (BindLetcont bd k') m'
                   else
                      Debug.trace ("CONT multiple occur: " ++ show (varCensus x m')) $
                        simplifier (BindOpaque bd) m'
              -- DEAD-cont. remove dead code if the 'letcont' variable is now unused
              if freeVar x q then
                "letcont" @@ (return k') @@ (mkLam nm x t q)
              else
                Debug.trace "DEAD-CONT" $
                 strengthen q
            _ -> fail "simplifier: expected function in 'letcont' body"


     -- η-CONT rule.  If the bound contnuation is just an η-expanded
     -- version of 'j', replace the bound variable in the body with 'j'
     -- and drop the 'letcont'
 where tryEtaCont :: LF γ TERM -> Maybe (M (LF γ TERM))
       tryEtaCont (termView -> VLam _ x _
                     (termView -> VConst "enter" [ j, termView -> VVar x' []]))
          | x == x' =
             case termView j of
               VVar (F j') [] -> Just $ var j'
               VConst c []    -> Just $ tmConst c
               _ -> Nothing
       tryEtaCont _ = Nothing

simplifier bd (termView -> VConst "letval" [v,m]) = do
   let hyps = ?hyps
   case termView v of
     -- η-FUN rule.  If the bound value is just an η-expanded 'g', then replace
     -- the body of the let with 'g' and drop the let.
     VConst "lam" [termView -> VLam _ k _ (termView -> VLam _ x _ (termView ->
                        VConst "app" [ termView -> VVar (F (F g)) []
                                     , termView -> VVar (F k') []
                                     , termView -> VVar x' []
                                     ]))]
        | k == k', x == x' ->
             let ?hyps = hyps in
             Debug.trace "η-FUN" $
               simplifier bd =<< (return m) @@ (var g)

     -- η-PAIR rule.  If a pair is bound in a context where the components of the
     -- pair were previously projected from a pair variable, replace the reconstructed
     -- pair with the original variable. (NB: this rule is only valid for strict pairs)
     VConst "pair" [ termView -> VVar x []
                   , termView -> VVar y []
                   ]
       | Just (True, vx) <- lookupProjData bd x
       , Just (False,vy) <- lookupProjData bd y
       , alphaEq vx vy ->
             Debug.trace "η-PAIR" $ do
               m' <- return m @@ return vx
               let bd' = case termView vx of
                           VVar vx' [] -> dropData vx' (varCensus vx' m') bd
                           _ -> bd
               simplifier bd' m'

     -- otherwise, recurse
     _ -> case termView m of
            VLam nm x t m' -> do
              q <- if (varCensus x m' == 1) then
                     Debug.trace "β-FUN-LIN" $ do
                      let bd' = BindLetval bd v
                      simplifier bd' m'
                   else do
                     let bd' = BindOpaque bd
                     simplifier bd' m'
              -- DEAD-val remove dead code if the 'letval' variable is now unused
              if freeVar x q then
                  "letval" @@ return v @@ mkLam nm x t q
              else
                Debug.trace "DEAD-VAL" $
                  strengthen q

            _ -> fail "simplifier: expected function in 'letval'"

simplifier bd (termView -> VConst "let_prj1" [v, m]) = do
   let bd' = BindLetproj bd False v
   case termView v of
     -- β-PAIR1 rule
     VVar v' []
       | Just (termView -> VConst "pair" [x,_]) <- lookupValData bd v' ->
           Debug.trace "β-PAIR1" $ do
             m' <- return m @@ return x
             let bd' = case termView x of
                         VVar x' [] -> dropData x' (varCensus x' m') bd
                         _ -> bd
             simplifier bd' m'
     _ ->
          case termView m of
            VLam nm x t m' -> do
              q <- simplifier bd' m'
               -- DEAD-proj. remove dead code if the 'let_prj' variable is now unused
              if freeVar x q then
                "let_prj1" @@ return v @@ mkLam nm x t q
              else
                Debug.trace "DEAD-PROJ1" $
                 strengthen q
            _ -> fail "simplifier: expected function in 'let_prj1'"

simplifier bd (termView -> VConst "let_prj2" [ v, m]) = do
   let bd' = BindLetproj bd True v
   case termView v of
     -- β-PAIR2 rule
     VVar v' []
       | Just (termView -> VConst "pair" [_,y]) <- lookupValData bd v' ->
           Debug.trace "β-PAIR2" $ do
             m' <- return m @@ return y
             let bd' = case termView y of
                         VVar y' [] -> dropData y' (varCensus y' m') bd
                         _ -> bd
             simplifier bd' m'
     _ ->
          case termView m of
            VLam nm x t m' -> do
              q <- simplifier bd' m'
               -- DEAD-proj. remove dead code if the 'let_prj' variable is now unused
              if freeVar x q then
                "let_prj2" @@ return v @@ mkLam nm x t q
              else
                Debug.trace "DEAD-PROJ2" $
                 strengthen q
            _ -> fail "simplifier: expected function in 'let_prj2'"

simplifier bd (termView -> VConst "enter" [termView -> VVar kv [], x])
   | Just cont <- lookupContData bd kv =
        Debug.trace "β-CONT" $ do
          cont' <- return cont @@ return x
          let bd' =
                case termView x of
                   VVar x' [] -> dropData x' (varCensus x' cont') bd
                   _ -> bd
          simplifier bd' cont'

simplifier bd (termView -> VConst "app" [ termView -> VVar f [], j, y])
  | Just (termView -> VConst "lam" [m]) <- lookupValData bd f =
     Debug.trace "β-FUN" $ do
        m' <- return m @@ return j @@ return y
        let bd' =
             (case termView j of
               VVar j' [] -> dropData j' (varCensus j' m')
               _ -> id) $
             (case termView y of
               VVar y' [] -> dropData y' (varCensus y' m')
               _ -> id) $
             bd
        simplifier bd' m'

simplifier bd m@(termView -> VConst "case" [e,l,r]) = do
   case termView e of
     VVar e' []
        -- β-CASE rules.  If we case on an 'inl' or 'inr' value, simply
        -- enter the correct continuation.
        | Just (termView -> VConst "inl" [x]) <- lookupValData bd e' ->
            Debug.trace "β-CASE-L" $
              simplifier bd =<< "enter" @@ return l @@ return x
        | Just (termView -> VConst "inr" [x]) <- lookupValData bd e' ->
            Debug.trace "β-CASE-R" $
             simplifier bd =<< "enter" @@ return r @@ return x

     _ -> case (termView l, termView r) of
            -- η-case rule.  If the branches of a case simply reconstitute
            -- an either value and then enter the same continuation, we can skip
            -- the case and just enter the continuation.  (NB: this rule is only valid
            -- for strict languages).
            (VVar l' [], VVar r' [])
              | Just lk <- lookupContData bd l'
              , Just rk <- lookupContData bd r'
              , Just k1 <- tryEtaCase "inl" lk
              , Just k2 <- tryEtaCase "inr" rk
              , k1 == k2 ->
                 Debug.trace "η-CASE"
                  simplifier bd =<< "enter" @@ var k1 @@ return e

            _ -> return m

 where
   tryEtaCase :: String -> LF γ TERM -> Maybe (Var γ)
   tryEtaCase con m =
     case termView m of
        VLam _ x _ (termView ->
                   VConst "letval" [ termView -> VConst (CNm con') [termView -> VVar x' []]
                                   , termView -> VLam _ y _ (termView ->
                                          VConst "enter" [ termView -> VVar (F (F k)) []
                                                         , termView -> VVar y' []
                                                         ])
                                   ])
          | con == con', x == x', y == y' -> Just k
        _ -> Nothing

-- No other rule applies, just return the term
simplifier _ m = return m



--  "letval" @@ "tt" @@ (λ "x" v $ \x -> "tm_var" @@ var x)

testTerm :: LF E TERM
testTerm = mkTerm sig $

 --  "ml_app" @@ ("ml_var" @@ "g'")
 --           @@ ("ml_app" @@ ("ml_var" @@ "g")
 --                        @@ ("ml_app" @@ body
 --                                     @@ ("ml_var" @@ "y")))
 -- where
 --  body = inEmptyCtx $
 --   "ml_lam" @@ (λ "x" v $ \x ->
 --     "ml_case" @@ ("ml_var" @@ var x)
 --               @@ (λ "l" v $ \l ->
 --                      "ml_pair" @@ ("ml_var" @@ var l) @@ ("ml_var" @@ "x3")
 --                  )
 --               @@ (λ "r" v $ \_r ->
 --                      "ml_app" @@ ("ml_var" @@ "g''") @@ ("ml_var" @@ var x)
 --                  )
 --   )

  "ml_fst" @@
     ("ml_app" @@ ("ml_lam" @@ (λ "x" v $ \x ->
                      "ml_pair" @@ ("ml_app" @@ ("ml_var" @@ "g")
                                             @@ ("ml_var" @@ var x))
                                @@ ("ml_var" @@ var x)
                  ))
               @@ ("ml_var" @@ "y"))

  -- "ml_lam" @@ (λ "x" v $ \x ->
  --                "ml_app" @@ ("ml_var" @@ "f")
  --                         @@ ("ml_pair" @@ ("ml_var" @@ (var x)) @@ ("ml_var" @@ "y")))

cpsTerm :: LF E TERM
cpsTerm = mkTerm sig $ do
  tailcps_ml testTerm =<< "halt"

simplTerm :: LF E TERM
simplTerm = mkTerm sig $ do
  Debug.trace "run simplifier" $
     simplifier BindEmpty cpsTerm

