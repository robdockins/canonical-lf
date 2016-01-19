module Lang.LF.Internal.Subst where

import Data.Proxy

import Lang.LF.ChangeT
import Lang.LF.Internal.Build
import Lang.LF.Internal.Model
import Lang.LF.Internal.Solve

weakSubst :: Weakening γ₁ γ₂
          -> Subst m f γ₂ γ₃
          -> Subst m f γ₁ γ₃
weakSubst WeakRefl = id
weakSubst (WeakR w) = weakSubst w . SubstWeak
weakSubst (WeakL w) = SubstWeak . weakSubst w
weakSubst (WeakTrans w₁ w₂) = weakSubst w₁ . weakSubst w₂

lookupSubst :: LFModel f m
          => Var γ₁
          -> Subst m f γ₁ γ₂
          -> m (f γ₂ TERM)
lookupSubst v SubstRefl = var v
lookupSubst v (SubstWeak s) = lookupSubst (F v) s
lookupSubst (B v) (SubstApply _ f) = f v
lookupSubst (F v) (SubstApply s _) = lookupSubst v s
lookupSubst (B v) (SubstSkip _) = aterm <$> var0 (B v) id
lookupSubst (F v) (SubstSkip s) = weaken <$> lookupSubst v s

strengthen :: (LFModel f m, ?soln :: LFSoln f)
           => f (γ::>b) s
           -> m (f γ s)
strengthen =
   hsubst (SubstApply
             SubstRefl
             (\_ -> fail "Cannot strengthen; variable occurs free"))


instantiateLF :: forall f m γ s
          . (WFContext γ, LFModel f m, ?soln :: LFSoln f)
         => f γ s -> ChangeT m (f γ s)
instantiateLF tm =
  case unfoldLF tm of
    Weak x -> weaken <$> instantiate x

    Type   -> Unchanged tm
    KPi nm ty k -> onChange tm foldLF (KPi nm <$> instantiate ty <*> instantiate k)

    AType x -> onChange tm foldLF (AType <$> instantiate x)
    TyPi nm t1 t2 -> onChange tm foldLF (TyPi nm <$> instantiate t1 <*> instantiate t2)
    TyConst _ -> Unchanged tm
    TyApp t m -> onChange tm foldLF (TyApp <$> instantiate t <*> instantiate m)

    ATerm x ->
      case go x of
        Left _  -> Unchanged tm
        Right m -> Changed m
    Lam nm ty m -> onChange tm foldLF (Lam nm <$> instantiate ty <*> instantiate m)

    Var _ -> Unchanged tm
    Const _ -> Unchanged tm
    App _ _ -> Unchanged tm
    UVar _ -> Unchanged tm 

    Fail -> Unchanged tm
    Unify x y -> do
      res <- case (go x, go y) of
        (Left _, Left _) -> Unchanged UnifyDefault
        (Left x', Right my) -> Changed $ do
          ATerm y' <- unfoldLF <$> my
          return $ unifyATm SubstRefl SubstRefl x' y'
        (Right mx, Left y') -> Changed $ do
          ATerm x' <- unfoldLF <$> mx
          return $ unifyATm SubstRefl SubstRefl x' y'
        (Right mx, Right my) -> Changed $ do
          ATerm x' <- unfoldLF <$> mx
          ATerm y' <- unfoldLF <$> my
          return $ unifyATm SubstRefl SubstRefl x' y'
      case res of
        UnifyDefault   -> Unchanged tm
        UnifySolve _ _ -> Unchanged tm
        UnifyDecompose m -> Changed $
          m >>= \case
            Just xs -> foldLF (And xs)
            Nothing -> liftClosed <$> foldLF Fail

    And xs -> onChange tm foldLF (And <$> mapM instantiate xs)
    Forall nm ty c -> onChange tm foldLF (Forall nm <$> instantiate ty <*> instantiate c)
    Exists nm ty c -> onChange tm foldLF (Exists nm <$> instantiate ty <*> instantiate c)

    Goal m c -> onChange tm foldLF (Goal <$> instantiate m <*> instantiate c)
    Sigma nm ty g -> onChange tm foldLF (Sigma nm <$> instantiate ty <*> instantiate g)

 where
  go :: forall γ. WFContext γ => f γ ATERM -> Either (f γ ATERM) (m (f γ TERM))
  go atm =
    case unfoldLF atm of
      Weak x ->
        case go x of
          Left x' -> Left (weaken x')
          Right m -> Right (weaken <$> m)
      Var _   -> Left atm
      Const _ -> Left atm
      App m1 m2 ->
        case (go m1, instantiate m2) of
          (Left _, Unchanged _) -> Left atm
          (Left _, Changed m2') -> Right (aterm <$> (foldLF . App m1 =<< m2'))
          (Right m1', Unchanged _) -> Right (app m1' (return m2))
          (Right m1', Changed m2') -> Right (app m1' m2')
      UVar u
        | Just tm <- lookupUVar Proxy u ?soln -> Right (runChangeT $ instantiate tm)
        | otherwise -> Left atm

hsubstLF :: forall f m s γ γ'
          . (LFModel f m, ?soln :: LFSoln f)
         => Subst m f γ γ'
         -> f γ s
         -> m (f γ' s)
hsubstLF SubstRefl tm = return tm
hsubstLF (SubstWeak s) tm = hsubst s (weaken tm)
hsubstLF sub tm =
  case unfoldLF tm of
     Weak x ->
       case sub of
         SubstRefl      -> return tm
         SubstWeak s    -> hsubst s (weaken tm)
         SubstSkip s    -> weaken <$> hsubst s x
         SubstApply s _ -> hsubst s x

     Type ->
        case sub of
          SubstRefl   -> return tm
          SubstWeak s -> hsubst s (weaken tm)
          _ -> error "impossible"

     KPi nm a k   -> foldLF =<< (KPi nm <$> hsubst sub a <*> hsubst sub' k)

     AType x      -> foldLF =<< (AType <$> hsubst sub x)
     TyPi nm a a' -> foldLF =<< (TyPi nm <$> hsubst sub a <*> hsubst sub' a')

     TyConst _ ->
        case sub of
          SubstRefl   -> return tm
          SubstWeak s -> hsubst s (weaken tm)
          _ -> error "impossible"

     TyApp p m    -> foldLF =<< (TyApp <$> hsubst sub p <*> hsubst sub m)

     Lam nm a m   -> foldLF =<< (Lam nm <$> hsubst sub a <*> hsubst sub' m)

     And cs       -> foldLF . And =<< (mapM (hsubst sub) cs)

     Unify r1 r2  -> do
        r1' <- f =<< hsubstTm sub r1
        r2' <- f =<< hsubstTm sub r2
        foldLF (Unify r1' r2')

     Forall nm a c -> foldLF =<< (Forall nm <$> hsubst sub a <*> hsubst sub' c)
     Exists nm a c -> foldLF =<< (Exists nm <$> hsubst sub a <*> hsubst sub' c)

     Sigma nm a g  -> foldLF =<< (Sigma nm <$> hsubst sub a <*> hsubst sub' g)
     Goal m c      -> foldLF =<< (Goal <$> hsubst sub m <*> hsubst sub c)
     Fail ->
        case sub of
          SubstRefl   -> return tm
          SubstWeak s -> hsubst s (weaken tm)
          _ -> error "impossible"

     ATerm x      -> either return (foldLF . ATerm) =<< hsubstTm sub x
     Const _      -> f =<< hsubstTm sub tm
     Var _        -> f =<< hsubstTm sub tm
     App _ _      -> f =<< hsubstTm sub tm
     UVar _       -> f =<< hsubstTm sub tm

 where
  sub' :: forall b. Subst m f (γ ::> b) (γ' ::> b)
  sub' = SubstSkip sub

  f :: Either (f γ' TERM) (f γ' ATERM) -> m (f γ' ATERM)
  f (Left (unfoldLF -> ATerm r)) = return r
  f (Right r) = return r
  f _ = fail "hereditary substitution failed: expected ATERM result"

{- FIXME? rewrite this in continuation passing form
    to avoid repeated matching on Either values. -}
hsubstTm :: forall m f γ γ'
          . (LFModel f m, ?soln :: LFSoln f)
         => Subst m f γ γ'
         -> f γ ATERM
         -> m (Either (f γ' TERM) (f γ' ATERM))
hsubstTm sub tm =
         case unfoldLF tm of
           Weak x ->
             case sub of
               SubstRefl      -> return (Right tm)
               SubstWeak s    -> hsubstTm s (weaken tm)
               SubstApply s _ -> hsubstTm s x
               SubstSkip s -> do
                   x' <- hsubstTm s x
                   return $ either (Left . weaken) (Right . weaken) x'

           Var v ->
             case sub of
               SubstRefl      -> return $ Right tm
               SubstWeak s    -> hsubstTm s (weaken tm)
               SubstApply _ f -> Left <$> f v
               SubstSkip _    -> Right <$> foldLF (Var v)

           UVar u ->
             case sub of
               SubstRefl ->
                 case lookupUVar Proxy u ?soln of
                   Just m  -> return $ Left m
                   Nothing -> return $ Right tm
               SubstWeak s -> hsubstTm s (weaken tm)
               _ -> error "impossible"

           Const _ ->
             case sub of
               SubstRefl   -> return $ Right tm
               SubstWeak s -> hsubstTm s (weaken tm)
               _ -> error "impossible"

           App r1 m2 -> do
             case sub of
               SubstRefl -> return $ Right tm
               _ -> do
                r1' <- hsubstTm sub r1
                m2' <- hsubst sub m2
                case r1' of
                  Left m1' ->
                    Left <$> gosub1 m1' m2'
                  Right r1'' ->
                    Right <$> foldLF (App r1'' m2')

 where
  gosub1 :: forall γ. f γ TERM -> f γ TERM -> m (f γ TERM)
  gosub1 x y =
   case (unfoldLF x, unfoldLF y) of
     (Weak x', Weak y') -> weaken <$> gosub1 x' y'
     _ -> gosub2 x y SubstRefl

  gosub2 :: forall γ γ'. f γ TERM
                      -> f γ' TERM
                      -> Subst m f γ γ'
                      -> m (f γ' TERM)
  gosub2 x y s =
    case unfoldLF x of
      Weak x'   -> gosub2 x' y (SubstWeak s)
      Lam _ _ m -> hsubst (SubstApply s (\_ -> return y)) m
      _ -> fail "hereditary substitution failed: ill-typed term"
