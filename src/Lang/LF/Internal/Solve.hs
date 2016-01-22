module Lang.LF.Internal.Solve where

import Data.Proxy

import Lang.LF.ChangeT
import Lang.LF.Internal.Model
import Lang.LF.Internal.Weak

solveLF :: forall f m
         . (LFModel f m)
        => f E CON
        -> m (f E CON, LFSoln f)
solveLF c0 = withCurrentSolution $ go (c0, ?soln)
 where
  go :: (LFModel f m)
     => (f E CON, LFSoln f)
     -> m (f E CON, LFSoln f)
  go (c, soln) =
    case doSolve c soln of
      Unchanged _ -> return (c, soln)
      Changed m -> do
        (mxs, soln') <- m
        case mxs of
          Nothing -> do
            x <- foldLF Fail
            return (x, soln')
          Just xs -> do
            let ?soln = soln'
            x <- foldLF (And xs)
            x' <- runChangeT $ instantiate x
            go (x', soln')

doSolve :: (LFModel f m)
        => f E CON
        -> LFSoln f
        -> ChangeT m (Maybe [f E CON], LFSoln f)
doSolve c soln =
  case unfoldLF c of
    Weak _ _ -> fail "doSolve: impossible"

    Fail -> Unchanged (Nothing, soln)

    UnifyVar u r -> Changed $ do
      extendSolution u (aterm r) soln >>= \case
         Nothing    -> return (Just [c], soln)
         Just soln' -> return (Just [], soln')

    Unify r1 r2 ->
      let ?soln = soln in
      let res = unifyATm WeakRefl WeakRefl r1 r2 in
      case res of
        UnifyDefault -> Unchanged (Just [c], soln)
        UnifyDecompose xs -> Changed (xs >>= \xs' -> return (xs', soln))
        UnifySolve u r -> Changed $ do
          let m = aterm r
          extendSolution u m soln >>= \case
            Nothing    -> return (Just [c], soln)
            Just soln' -> return (Just [], soln')

    And cs -> go cs soln
     where go [] s = return (Just [], s)
           go (x:xs) s = do
             (cs1, s') <- doSolve x s
             (cs2, s'') <- go xs s'
             let mcs = case (cs1, cs2) of
                         (Nothing, _) -> Nothing
                         (_, Nothing) -> Nothing
                         (Just as, Just bs) -> Just (as++bs)
             return (mcs, s'')

    Forall _ _ _ -> error "doSolve : forall quantifier"
    Exists _ _ _ -> error "doSolve : exists quantifier"

mkConj :: forall f m γ
      . (LFModel f m)
     => [f γ CON]
     -> m (f γ CON)
mkConj cs = do
   x <- fmap concat . sequence <$> (mapM f cs)
   case x of
     Nothing -> foldLF Fail
     Just xs -> foldLF (And xs)

 where f :: forall γ. f γ CON -> m (Maybe [f γ CON])
       f (unfoldLF -> And xs)   = (fmap concat . sequence) <$> mapM f xs
       f (unfoldLF -> Weak w x) = fmap (map (weaken w)) <$> f x
       f (unfoldLF -> Fail)     = return Nothing
       f x = return (Just [x])

unifyTm :: forall f m γ₁ γ₂ γ
      . (LFModel f m, ?soln :: LFSoln f)
     => Weakening γ₁ γ
     -> Weakening γ₂ γ
     -> f γ₁ TERM
     -> f γ₂ TERM
     -> m (f γ CON)
unifyTm w₁ w₂ x y =
   case (unfoldLF x, unfoldLF y) of
     (Weak w x', _) -> unifyTm (weakTrans w w₁) w₂ x' y
     (_, Weak w y') -> unifyTm w₁ (weakTrans w w₂) x y'
     (ATerm r1, ATerm r2) -> do
         let res = unifyATm w₁ w₂ r1 r2
         case res of
           UnifyDecompose m -> do
             x <- m
             case x of
               Nothing -> foldLF Fail
               Just cs -> foldLF (And cs)
           UnifyDefault ->
             foldLF (Unify (weaken w₁ r1) (weaken w₂ r2))
           UnifySolve u m ->
             foldLF (UnifyVar u m)

     (Lam nm a1 m1, Lam _ a2 m2) -> do
        cty <- unifyTy w₁ w₂ a1 a2
        c <- unifyTm (WeakSkip w₁) (WeakSkip w₂) m1 m2
        c' <- foldLF (Forall nm (weaken w₁ a1) c)
        mkConj [cty, c']
     _ -> fail "Attempting to unify LF terms with unequal types"

unifyTy :: forall f m γ₁ γ₂ γ
      . (LFModel f m, ?soln :: LFSoln f)
     => Weakening γ₁ γ
     -> Weakening γ₂ γ
     -> f γ₁ TYPE
     -> f γ₂ TYPE
     -> m (f γ CON)
unifyTy w₁ w₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak w x', _) -> unifyTy (weakTrans w w₁) w₂ x' y
    (_, Weak w y') -> unifyTy w₁ (weakTrans w w₂) x y'
    (TyPi nm a1 a2, TyPi _ a1' a2') ->
      mkConj =<< sequence
           [ unifyTy w₁ w₂ a1 a1'
           , do c <- unifyTy (WeakSkip w₁) (WeakSkip w₂) a2 a2'
                let a1' = weaken w₁ a1
                foldLF (Forall nm a1' c)
           ]
    (AType p1, AType p2) -> unifyATy w₁ w₂ p1 p2
    _ -> fail "Attempting to unify LF types of different kinds"

unifyATy :: forall f m γ₁ γ₂ γ
      . (LFModel f m, ?soln :: LFSoln f)
     => Weakening γ₁ γ
     -> Weakening γ₂ γ
     -> f γ₁ ATYPE
     -> f γ₂ ATYPE
     -> m (f γ CON)
unifyATy w₁ w₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak w x', _) -> unifyATy (weakTrans w w₁) w₂ x' y
    (_, Weak w y') -> unifyATy w₁ (weakTrans w w₂) x y'
    (TyConst c1, TyConst c2)
      | c1 == c2  -> foldLF (And [])
    (TyApp p1 m1, TyApp p2 m2) -> do
      mkConj =<< sequence
           [ unifyATy w₁ w₂ p1 p2
           , unifyTm  w₁ w₂ m1 m2
           ]
    _ -> foldLF Fail

cAnd' :: LFModel f m
      => f γ CON
      -> m (Maybe [f γ CON])
      -> m (Maybe [f γ CON])
cAnd' c cs =
  case unfoldLF c of
    Fail   -> return Nothing
    And xs -> fmap (fmap (xs++)) cs
    _      -> fmap (fmap (c:)) cs

data UnifyResult f m γ
  = UnifyDefault
  | UnifyDecompose (m (Maybe [f γ CON]))
  | UnifySolve (LFUVar f) (f γ ATERM)

unifyATm :: forall f m γ₁ γ₂ γ
      . (LFModel f m, ?soln :: LFSoln f)
     => Weakening γ₁ γ
     -> Weakening γ₂ γ
     -> f γ₁ ATERM
     -> f γ₂ ATERM
     -> UnifyResult f m γ
unifyATm w₁ w₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak w x', _) -> unifyATm (weakTrans w w₁) w₂ x' y
    (_, Weak w y') -> unifyATm w₁ (weakTrans w w₂) x y'
    (Const c₁, Const c₂)
       | c₁ == c₂  -> UnifyDecompose (return (Just []))
       | otherwise -> UnifyDecompose (return Nothing)

    (UVar u, UVar v)
       | u == v -> UnifyDecompose (return (Just []))
    (UVar u, _)
       | Just x' <- lookupUVar Proxy u ?soln -> UnifyDecompose $ do
           c <- unifyTm w₁ w₂ x' (aterm y)
           return (Just [c])
       | otherwise -> UnifySolve u (weaken w₂ y)
    (_, UVar u)
       | Just y' <- lookupUVar Proxy u ?soln -> UnifyDecompose $ do
           c <- unifyTm w₁ w₂ (aterm x) y'
           return (Just [c])
       | otherwise -> UnifySolve u (weaken w₁ x)

    (App r₁ m₁, App r₂ m₂) ->
       let res = unifyATm w₁ w₂ r₁ r₂ in
       case res of
         UnifyDefault      -> UnifyDefault
         UnifySolve _ _    -> UnifyDefault
         UnifyDecompose xs -> UnifyDecompose $ do
             cm <- unifyTm w₁ w₂ m₁ m₂
             cAnd' cm xs

    _ -> UnifyDefault
