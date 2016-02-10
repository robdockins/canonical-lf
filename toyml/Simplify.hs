module Simplify where

import Prelude hiding (pi, abs)
import           Lang.LF
import           Terms

import qualified Debug.Trace as Debug

data BindData (γ :: Ctx *) where
  BindEmpty   :: BindData E
  BindLetcont :: BindData γ
              -> LF γ TERM {- :: v ==> term -}
              -> BindData (γ ::> b)
  BindOpaque  :: BindData γ
              -> BindData (γ ::> b)
  BindLetval  :: BindData γ
              -> Bool -- Has at most one occurance?
              -> Bool -- Is cheap?
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
       go w (BindLetcont bd _)     (F v) = go (WeakRight w) bd v
       go w (BindOpaque bd)        (F v) = go (WeakRight w) bd v
       go w (BindLetval  bd _ _ _) (F v) = go (WeakRight w) bd v
       go w (BindLetproj bd _ _)   (F v) = go (WeakRight w) bd v
       go w (BindLetcont  _ v)     B     = Just (weaken (WeakRight w) v)
       go _ _                      _     = Nothing

lookupValData :: BindData γ
              -> Var γ
              -> Maybe (Bool, Bool, LF γ TERM)
lookupValData = go WeakRefl
 where go :: Weakening γ γ' -> BindData γ -> Var γ -> Maybe (Bool, Bool, LF γ' TERM)
       go w (BindLetcont bd _)   (F v) = go (WeakRight w) bd v
       go w (BindOpaque bd)      (F v) = go (WeakRight w) bd v
       go w (BindLetval  bd _ _ _) (F v) = go (WeakRight w) bd v
       go w (BindLetproj bd _ _) (F v) = go (WeakRight w) bd v
       go w (BindLetval _ lin cheap val) B     = Just (lin, cheap, weaken (WeakRight w) val)
       go _ _                  _     = Nothing

lookupProjData :: BindData γ
              -> Var γ
              -> Maybe (Bool, LF γ TERM)
lookupProjData = go WeakRefl
 where go :: Weakening γ γ' -> BindData γ -> Var γ -> Maybe (Bool, LF γ' TERM)
       go w (BindLetcont bd _)   (F v) = go (WeakRight w) bd v
       go w (BindOpaque bd)      (F v) = go (WeakRight w) bd v
       go w (BindLetval  bd _ _ _) (F v) = go (WeakRight w) bd v
       go w (BindLetproj bd _ _) (F v) = go (WeakRight w) bd v
       go w (BindLetproj _ b v)  B     = Just (b, weaken (WeakRight w) v)
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
       go (BindLetval bd lin cheap val) (F v) = BindLetval (go bd v) lin cheap val
       go (BindLetproj bd x y) (F v) = BindLetproj (go bd v) x y
       go (BindLetcont bd _)   B     = BindOpaque bd
       go (BindLetval bd _ cheap val)  B     = BindLetval bd False cheap val
       go (BindLetproj bd _ _) B     = BindOpaque bd
       go bd                   _     = bd


newtype InlineHeuristic
  = InlineHeuristic
      { applyHeuristic :: forall γ. LF γ TERM -> Bool }

simplifier :: forall γ
            . (LiftClosed γ
              , ?hyps :: H γ
              , ?soln :: LFSoln LF
              , ?ischeap :: InlineHeuristic
              )
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
               VVar (F j') [] -> Just $ mkVar j'
               VConst c []    -> Just $ tmConst c
               _ -> Nothing
       tryEtaCont _ = Nothing

simplifier bd (termView -> VConst "letval" [v0,m]) = do
   -- first simplify the value
   v <- simplifyVal bd v0

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

     -- η-UNIT rule.  Replace every let-binding of tt with a distinguished
     -- variable standing for the constant unit value
     VConst "tt" [] ->
       Debug.trace "η-UNIT" $ do
         simplifier bd =<< (return m) @@ "tt_CAF"

     -- otherwise, recurse
     _ -> case termView m of
            VLam nm x t m' -> do
              q <- let bd' = BindLetval bd (varCensus x m' <= 1)
                                           (applyHeuristic ?ischeap v)
                                           v in
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
       | Just (_, _, termView -> VConst "pair" [x,_]) <- lookupValData bd v' ->
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
       | Just (_, _, termView -> VConst "pair" [_,y]) <- lookupValData bd v' ->
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
  | Just (lin, cheap, termView -> VConst "lam" [m]) <- lookupValData bd f
  , lin || cheap =
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
        | Just (_, _, termView -> VConst "inl" [x]) <- lookupValData bd e' ->
            Debug.trace "β-CASE-L" $
              simplifier bd =<< "enter" @@ return l @@ return x
        | Just (_, _, termView -> VConst "inr" [x]) <- lookupValData bd e' ->
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


simplifyVal :: forall γ
            . (LiftClosed γ, ?hyps :: H γ
              , ?soln :: LFSoln LF
              , ?ischeap :: InlineHeuristic
              )
            => BindData γ
            -> LF γ TERM
            -> M (LF γ TERM)
-- Simplify inside the body of lambdas
simplifyVal bd (termView -> VConst "lam"
                             [termView -> VLam jnm j jt
                               (termView -> VLam xnm x xt m)
                             ]) = do
   let bd' = BindOpaque (BindOpaque bd)
   m' <- simplifier bd' m
   "lam" @@ (mkLam jnm j jt =<< mkLam xnm x xt m')

-- otherwise return the term unchanged
simplifyVal _ m = return m

