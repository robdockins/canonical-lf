module Lang.LF.Internal.Solve where

import Data.Proxy

import Lang.LF.ChangeT
import Lang.LF.Internal.Model

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
            x <- liftClosed <$> foldLF Fail
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
    Fail -> Unchanged (Nothing, soln)

    Unify r1 r2 ->
      let ?soln = soln in
      let res = unifyATm SubstRefl SubstRefl r1 r2 in
      case res of
        UnifyDefault -> Unchanged (Just [c], soln)
        UnifyDecompose xs -> Changed (xs >>= \xs' -> return (xs', soln))
        UnifySolve u r -> Changed $ do
          m <- aterm <$> r
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
      . (WFContext γ, LFModel f m)
     => [f γ CON]
     -> m (f γ CON)
mkConj cs = do
   x <- fmap concat . sequence <$> (mapM f cs)
   case x of
     Nothing -> liftClosed <$> foldLF Fail
     Just xs -> foldLF (And xs)

 where f :: forall γ. f γ CON -> m (Maybe [f γ CON])
       f (unfoldLF -> And xs) = (fmap concat . sequence) <$> mapM f xs
       f (unfoldLF -> Weak x) = fmap (map weaken) <$> f x
       f (unfoldLF -> Fail)   = return Nothing
       f x = return (Just [x])

unifyTm :: forall f m γ₁ γ₂ γ
      . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
     => (Subst m f γ₁ γ)
     -> (Subst m f γ₂ γ)
     -> f γ₁ TERM
     -> f γ₂ TERM
     -> m (f γ CON)
unifyTm s₁ s₂ x y =
   case (unfoldLF x, unfoldLF y) of
     (Weak x', _) -> unifyTm (SubstWeak s₁) s₂ x' y
     (_, Weak y') -> unifyTm s₁ (SubstWeak s₂) x y'
     (ATerm r1, ATerm r2) -> do
         let res = unifyATm s₁ s₂ r1 r2
         case res of
           UnifyDecompose m -> do
             x <- m
             case x of
               Nothing -> liftClosed <$> foldLF Fail
               Just cs -> foldLF (And cs)
           UnifyDefault ->
             foldLF =<< Unify <$> hsubst s₁ r1 <*> hsubst s₂ r2
           UnifySolve u m ->
             foldLF =<< Unify <$> (liftClosed <$> foldLF (UVar u)) <*> m

     (Lam nm a1 m1, Lam _ a2 m2) -> do
        cty <- unifyTy s₁ s₂ a1 a2
        c <- unifyTm (SubstSkip s₁) (SubstSkip s₂) m1 m2
        c' <- foldLF =<< Forall nm <$> hsubst s₁ a1 <*> return c
        mkConj [cty, c']
     _ -> fail "Attempting to unify LF terms with unequal types"

unifyTy :: forall f m γ₁ γ₂ γ
      . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
     => (Subst m f γ₁ γ)
     -> (Subst m f γ₂ γ)
     -> f γ₁ TYPE
     -> f γ₂ TYPE
     -> m (f γ CON)
unifyTy s₁ s₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak x', _) -> unifyTy (SubstWeak s₁) s₂ x' y
    (_, Weak y') -> unifyTy s₁ (SubstWeak s₂) x y'
    (TyPi nm a1 a2, TyPi _ a1' a2') ->
      mkConj =<< sequence
           [ unifyTy s₁ s₂ a1 a1'
           , do c <- unifyTy (SubstSkip s₁) (SubstSkip s₂) a2 a2'
                a1' <- hsubst s₁ a1
                foldLF (Forall nm a1' c)
           ]
    (AType p1, AType p2) -> unifyATy s₁ s₂ p1 p2
    _ -> fail "Attempting to unify LF types of different kinds"

unifyATy :: forall f m γ₁ γ₂ γ
      . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
     => (Subst m f γ₁ γ)
     -> (Subst m f γ₂ γ)
     -> f γ₁ ATYPE
     -> f γ₂ ATYPE
     -> m (f γ CON)
unifyATy s₁ s₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak x', _) -> unifyATy (SubstWeak s₁) s₂ x' y
    (_, Weak y') -> unifyATy s₁ (SubstWeak s₂) x y'
    (TyConst c1, TyConst c2)
      | c1 == c2  -> foldLF (And [])
    (TyApp p1 m1, TyApp p2 m2) -> do
      mkConj =<< sequence
           [ unifyATy s₁ s₂ p1 p2
           , unifyTm  s₁ s₂ m1 m2
           ]
    _ -> liftClosed <$> foldLF Fail

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
  | UnifySolve (LFUVar f) (m (f γ ATERM))

unifyATm :: forall f m γ₁ γ₂ γ
      . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
     => (Subst m f γ₁ γ)
     -> (Subst m f γ₂ γ)
     -> f γ₁ ATERM
     -> f γ₂ ATERM
     -> UnifyResult f m γ
unifyATm s₁ s₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak x', _) -> unifyATm (SubstWeak s₁) s₂ x' y
    (_, Weak y') -> unifyATm s₁ (SubstWeak s₂) x y'
    (Const c₁, Const c₂)
       | c₁ == c₂  -> UnifyDecompose (return (Just []))
       | otherwise -> UnifyDecompose (return Nothing)

    (UVar u, UVar v)
       | u == v -> UnifyDecompose (return (Just []))
    (UVar u, _)
       | Just x' <- lookupUVar Proxy u ?soln -> UnifyDecompose $ do
           c <- unifyTm s₁ s₂ x' (aterm y)
           return (Just [c])
       | otherwise -> UnifySolve u (hsubst s₂ y)
    (_, UVar u)
       | Just y' <- lookupUVar Proxy u ?soln -> UnifyDecompose $ do
           c <- unifyTm s₁ s₂ (aterm x) y'
           return (Just [c])
       | otherwise -> UnifySolve u (hsubst s₁ x)

    (App r₁ m₁, App r₂ m₂) ->
       let res = unifyATm s₁ s₂ r₁ r₂ in
       case res of
         UnifyDefault      -> UnifyDefault
         UnifySolve _ _    -> UnifyDefault
         UnifyDecompose xs -> UnifyDecompose $ do
             cm <- unifyTm s₁ s₂ m₁ m₂
             cAnd' cm xs

    _ -> UnifyDefault