module Lang.LF.Internal.Subst where

import Data.Proxy

import Lang.LF.ChangeT
import Lang.LF.Internal.Build
import Lang.LF.Internal.Model

weakSubst :: Weakening γ₁ γ₂
          -> Subst m f γ₂ γ₃
          -> Subst m f γ₁ γ₃
weakSubst = SubstWeak

lookupSubst :: (WFContext γ₂, LFModel f m)
          => Var γ₁
          -> Subst m f γ₁ γ₂
          -> m (f γ₂ TERM)
lookupSubst v SubstRefl = var v
lookupSubst v (SubstWeak w s) = lookupSubst (weakenVar w v) s
lookupSubst B (SubstApply _ x) = return x
lookupSubst (F v) (SubstApply s _) = lookupSubst v s
lookupSubst B (SubstSkip _) = aterm <$> foldLF Var
lookupSubst (F v) (SubstSkip s) = weaken (WeakL WeakRefl) <$> lookupSubst v s

strengthen :: (LFModel f m, ?soln :: LFSoln f)
           => f (γ::>b) s
           -> m (f γ s)
strengthen =
   hsubst (SubstApply
             SubstRefl
             (error "Cannot strengthen; variable occurs free"))

instantiateLF :: forall f m γ s
          . (LFModel f m, ?soln :: LFSoln f)
         => f γ s
         -> ChangeT m (f γ s)
instantiateLF tm =
  case unfoldLF tm of
    Weak w x -> weaken w <$> instantiate x

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

    Var -> Unchanged tm
    Const _ -> Unchanged tm
    App _ _ -> Unchanged tm
    UVar _ -> Unchanged tm 

    Fail -> Unchanged tm

    Unify x y ->
      case (go x, go y) of
        (Left _, Left _) -> Unchanged tm
        (Left x', Right my) -> Changed $ do
          ATerm y' <- unfoldLF <$> my
          foldLF (Unify x' y')
        (Right mx, Left y') -> Changed $ do
          ATerm x' <- unfoldLF <$> mx
          foldLF (Unify x' y')
        (Right mx, Right my) -> Changed $ do
          ATerm x' <- unfoldLF <$> mx
          ATerm y' <- unfoldLF <$> my
          foldLF (Unify x' y')

    And xs -> onChange tm foldLF (And <$> mapM instantiate xs)
    Forall nm ty c -> onChange tm foldLF (Forall nm <$> instantiate ty <*> instantiate c)
    Exists nm ty c -> onChange tm foldLF (Exists nm <$> instantiate ty <*> instantiate c)

    Goal m c -> onChange tm foldLF (Goal <$> instantiate m <*> instantiate c)
    Sigma nm ty g -> onChange tm foldLF (Sigma nm <$> instantiate ty <*> instantiate g)

 where
  go :: forall γ. f γ ATERM -> Either (f γ ATERM) (m (f γ TERM))
  go atm =
    case unfoldLF atm of
      Weak w x ->
        case go x of
          Left x' -> Left (weaken w x')
          Right m -> Right (weaken w <$> m)
      Var     -> Left atm
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


substWeak :: Subst m f γ₂ γ₃
         -> Weakening γ₁ γ₂
         -> (forall γ'
              . Weakening γ' γ₃
             -> Subst m f γ₁ γ'
             -> x)
         -> x
substWeak s WeakRefl k = k WeakRefl s
substWeak SubstRefl w k = k w SubstRefl

substWeak s (WeakL w) k =
  substWeak s w $ \w' s' ->
    substWeak s' (WeakR WeakRefl) $ \w'' s'' ->
      k (weakTrans w'' w') s''

substWeak (SubstWeak w s) w' k =
  substWeak s (weakTrans w' w) k

substWeak (SubstSkip s) (WeakR w) k =
  substWeak s w $ \w' s' ->
    k (WeakR w') s'
substWeak (SubstSkip s) (WeakSkip w) k =
  substWeak s w $ \w' s' ->
    k (WeakSkip w') (SubstSkip s')

substWeak (SubstApply s _f) (WeakR w) k =
  substWeak s w k
substWeak (SubstApply s f) (WeakSkip w) k =
  k WeakRefl (SubstApply (SubstWeak w s) f)


hsubstLF :: forall f m s γ γ'
          . (LFModel f m, ?soln :: LFSoln f)
         => Subst m f γ γ'
         -> f γ s
         -> m (f γ' s)
hsubstLF SubstRefl tm = return tm
hsubstLF (SubstWeak w s) tm = hsubst s (weaken w tm)
hsubstLF sub tm =
  case unfoldLF tm of
     Weak w x ->
       substWeak sub w $ \w' sub' ->
         weaken w' <$> hsubstLF sub' x

     Type ->
        case sub of
          SubstRefl     -> return tm
          SubstWeak w s -> hsubst s (weaken w tm)
          _ -> error "impossible"

     KPi nm a k   -> foldLF =<< (KPi nm <$> hsubst sub a <*> hsubst sub' k)

     AType x      -> foldLF =<< (AType <$> hsubst sub x)
     TyPi nm a a' -> foldLF =<< (TyPi nm <$> hsubst sub a <*> hsubst sub' a')

     TyConst _ ->
        case sub of
          SubstRefl   -> return tm
          SubstWeak w s -> hsubst s (weaken w tm)
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
          SubstWeak w s -> hsubst s (weaken w tm)
          _ -> error "impossible"

     ATerm x      -> either return (foldLF . ATerm) =<< hsubstTm sub x
     Const _      -> f =<< hsubstTm sub tm
     Var          -> f =<< hsubstTm sub tm
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
           Weak w x ->
             substWeak sub w $ \w' sub' ->
               either (Left . weaken w') (Right . weaken w') <$> hsubstTm sub' x

           Var ->
             case sub of
               SubstRefl      -> return $ Right tm
               SubstWeak w s  -> hsubstTm s (weaken w tm)
               SubstApply _ x -> return $ Left x
               SubstSkip _    -> Right <$> foldLF Var

           UVar u ->
             case sub of
               SubstRefl ->
                 case lookupUVar Proxy u ?soln of
                   Just m  -> return $ Left m
                   Nothing -> return $ Right tm
               SubstWeak w s -> hsubstTm s (weaken w tm)
               _ -> error "impossible"

           Const _ ->
             case sub of
               SubstRefl   -> return $ Right tm
               SubstWeak w s -> hsubstTm s (weaken w tm)
               _ -> error "impossible"

           App r1 m2 -> do
             case sub of
               SubstRefl -> return $ Right tm
               _ -> do
                r1' <- hsubstTm sub r1
                m2' <- hsubst sub m2
                case r1' of
                  Left m1' ->
                    Left <$> gosub WeakRefl WeakRefl m1' m2'
                  Right r1'' ->
                    Right <$> foldLF (App r1'' m2')

 where
  gosub :: forall γ₁ γ₂. Weakening γ₁ γ' -> Weakening γ₂ γ' -> f γ₁ TERM -> f γ₂ TERM -> m (f γ' TERM)
  gosub w1 w2 x' y' =
   case (unfoldLF x', unfoldLF y') of
     (Weak w1' x'', _) -> gosub (weakTrans w1' w1) w2 x'' y'
     (_, Weak w2' y'') -> gosub w1 (weakTrans w2' w2) x' y''
     (Lam _ _ m, _) ->
        mergeWeak (weakNormalize w1) (weakNormalize w2) $ \wcommon w1' w2' -> 
            weaken wcommon <$>
              let sub' = SubstApply (SubstWeak w1' SubstRefl) (weaken w2' y') in
              hsubst sub' m
     _ -> fail "hereditary substitution failed: ill-typed term"
