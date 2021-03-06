{-# LANGUAGE ScopedTypeVariables #-}

module Lang.LF.Internal.Subst where

import qualified Data.Map.Strict as Map

import Lang.LF.ChangeT
import Lang.LF.Internal.Basics
import Lang.LF.Internal.Model
import Lang.LF.Internal.Solve
import Lang.LF.Internal.Weak

weakSubst :: Subst f γ₂ γ₃
          -> Weakening γ₁ γ₂
          -> Subst f γ₁ γ₃
weakSubst s w = substWeak s w SubstWeak

lookupSubst :: forall f m γ₁ γ₂
             . (LFModel f m)
            => Var γ₁
            -> Subst f γ₁ γ₂
            -> m (f γ₂ TERM)
lookupSubst v0 sub0 = go v0 sub0 WeakRefl
 where
  go :: forall γ₁ γ₂ γ₃
      . Var γ₁
     -> Subst f γ₁ γ₂
     -> Weakening γ₂ γ₃
     -> m (f γ₃ TERM)
  go v     SubstRefl         wk = aterm <$> var0 v wk
  go v     (SubstWeak w s)   wk = go v s (weakCompose wk w)
  go B     (SubstApply _ x)  wk = return $ weaken wk x
  go (F v) (SubstApply s _)  wk = go v s wk
  go B     (SubstSkip _)     wk = aterm <$> var0 B wk
  go (F v) (SubstSkip s)     wk = go v s (WeakRight wk)



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
    Weak w x -> onChange tm (return . weaken w) (instantiate x)

    Type   -> Unchanged tm
    KPi nm ty k -> onChange tm foldLF (KPi nm <$> instantiate ty <*> instantiate k)

    AType x -> onChange tm foldLF (AType <$> instantiate x)
    TyPi nm t1 t2 -> onChange tm foldLF (TyPi nm <$> instantiate t1 <*> instantiate t2)
    TyConst _ -> Unchanged tm
    TyApp t m -> onChange tm foldLF (TyApp <$> instantiate t <*> instantiate m)
    TyRecord row -> onChange tm foldLF (TyRecord <$> instantiate row)
    TyRow _ -> Unchanged tm

    ATerm x ->
      case go x of
        Left _  -> Unchanged tm
        Right m -> Changed m
    Lam nm ty m -> onChange tm foldLF (Lam nm <$> instantiate ty <*> instantiate m)
    Record flds -> onChange tm foldLF (Record <$> traverse instantiate flds)
    RecordModify r dels ins -> onChange tm foldLF
        (RecordModify <$> instantiate r <*> return dels <*> traverse instantiate ins)
    Row flds    -> onChange tm foldLF (Row <$> traverse instantiate flds)
    RowModify r dels ins -> onChange tm foldLF
        (RowModify <$> instantiate r <*> return dels <*> traverse instantiate ins)

    Var -> Unchanged tm
    Const _ -> Unchanged tm
    App _ _ -> Unchanged tm
    UVar _ -> Unchanged tm
    Project _ _ -> Unchanged tm

    Fail -> Unchanged tm

    Unify x y -> doUnify x y

    And xs -> onChange tm foldLF (And <$> mapM instantiate xs)
    Forall nm ty c -> onChange tm foldLF (Forall nm <$> instantiate ty <*> instantiate c)
    Exists nm ty c -> onChange tm foldLF (Exists nm <$> instantiate ty <*> instantiate c)

    Goal m c -> onChange tm foldLF (Goal <$> instantiate m <*> instantiate c)
    Sigma nm ty g -> onChange tm foldLF (Sigma nm <$> instantiate ty <*> instantiate g)

 where

  doUnify :: (s ~ CON) => f γ ATERM -> f γ ATERM -> ChangeT m (f γ CON)
  doUnify x y =
      case (go x, go y) of
        (Left _, Left _) -> Unchanged tm
        (Left x', Right my) -> Changed $ do
          y' <- extractATerm <$> my
          foldLF (Unify x' y')
        (Right mx, Left y') -> Changed $ do
          x' <- extractATerm <$> mx
          foldLF (Unify x' y')
        (Right mx, Right my) -> Changed $ do
          x' <- extractATerm <$> mx
          y' <- extractATerm <$> my
          foldLF (Unify x' y')

  go :: forall γ. f γ ATERM -> Either (f γ ATERM) (m (f γ TERM))
  go atm =
    case unfoldLF atm of
      Weak w x ->
        case go x of
          Left x' -> Left (weaken w x')
          Right m -> Right (weaken w <$> m)
      Var     -> Left atm
      Const _ -> Left atm
      Project m fld ->
        case instantiate m of
          Unchanged _ -> Left atm
          Changed m1' -> Right (aterm <$> (foldLF =<< (Project <$> m1' <*> return fld)))
      App m1 m2 ->
        case (go m1, instantiate m2) of
          (Left _, Unchanged _) -> Left atm
          (Left _, Changed m2') -> Right (aterm <$> (foldLF . App m1 =<< m2'))
          (Right m1', Unchanged _) -> Right (app m1' (return m2))
          (Right m1', Changed m2') -> Right (app m1' m2')
      UVar u
        | Just tm <- lookupUVar u ?soln -> Right (runChangeT $ instantiate tm)
        | otherwise -> Left atm


absUVar :: LFModel f m
        => Abstraction f γ γ'
        -> LFUVar f
        -> Maybe (Var γ')
absUVar AbstractRefl _u =
  Nothing
absUVar (AbstractSkip a) u =
  fmap F (absUVar a u)
absUVar (AbstractApply a u') u =
  if u == u' then
    Just B
  else
    fmap F (absUVar a u)


abstractLF :: forall f m s γ γ'
            . (LFModel f m)
           => Abstraction f γ γ'
           -> f γ s
           -> m (f γ' s)
abstractLF AbstractRefl tm = return tm
abstractLF abs tm =
  case unfoldLF tm of
    Weak w x -> abstractWeak abs (weakNormalize w) $ \w' abs' ->
                  weaken w' <$> abstractUVars abs' x

    Type -> foldLF Type
    KPi nm a k -> foldLF =<< (KPi nm <$> abstractUVars abs a <*> abstractUVars abs' k)

    AType x      -> foldLF =<< (AType <$> abstractUVars abs x)
    TyPi nm a a' -> foldLF =<< (TyPi nm <$> abstractUVars abs a <*> abstractUVars abs' a')
    TyRecord row -> foldLF =<< (TyRecord <$> abstractUVars abs row)
    TyRow fldSet -> foldLF (TyRow fldSet)

    TyConst _ -> return $ weaken (absWeaken abs) tm

    TyApp p m    -> foldLF =<< (TyApp <$> abstractUVars abs p <*> abstractUVars abs m)
    Lam nm a m   -> foldLF =<< (Lam nm <$> abstractUVars abs a <*> abstractUVars abs' m)
    Record flds  -> foldLF =<< (Record <$> traverse (abstractUVars abs) flds)
    RecordModify r del ins -> foldLF =<<
       (RecordModify <$> abstractUVars abs r <*> return del <*> traverse (abstractUVars abs) ins)

    Row flds     -> foldLF =<< (Row <$> traverse (abstractUVars abs) flds)
    RowModify r del ins -> foldLF =<<
       (RowModify <$> abstractUVars abs r <*> return del <*> traverse (abstractUVars abs) ins)

    And cs       -> foldLF . And =<< (mapM (abstractUVars abs) cs)

    Unify r1 r2  -> do
       r1' <- abstractUVars abs r1
       r2' <- abstractUVars abs r2
       foldLF (Unify r1' r2')

    Forall nm a c -> foldLF =<< (Forall nm <$> abstractUVars abs a <*> abstractUVars abs' c)
    Exists nm a c -> foldLF =<< (Exists nm <$> abstractUVars abs a <*> abstractUVars abs' c)

    Sigma nm a g  -> foldLF =<< (Sigma nm <$> abstractUVars abs a <*> abstractUVars abs' g)
    Goal m c      -> foldLF =<< (Goal <$> abstractUVars abs m <*> abstractUVars abs c)
    Fail          -> foldLF Fail

    ATerm x      -> foldLF =<< (ATerm <$> abstractUVars abs x)
    Const _      -> return $ weaken (absWeaken abs) tm

    Var          -> return $ weaken (absWeaken abs) tm
    App x y      -> foldLF =<< (App <$> abstractUVars abs x <*> abstractUVars abs y)
    Project m fld -> foldLF =<< (Project <$> abstractUVars abs m <*> return fld)

    UVar u ->
      case absUVar abs u of
        Just v ->
          var0 v WeakRefl
        Nothing ->
          return $ weaken (absWeaken abs) tm

 where abs' :: forall b. Abstraction f (γ::>b) (γ'::>b)
       abs' = AbstractSkip abs


hsubstLF :: forall f m s γ γ'
          . (LFModel f m, ?soln :: LFSoln f)
         => Subst f γ γ'
         -> f γ s
         -> m (f γ' s)
hsubstLF SubstRefl tm = return tm
hsubstLF (SubstWeak w s) tm = weaken w <$> hsubst s tm
hsubstLF sub tm =
  case unfoldLF tm of
     Weak w x ->
       substWeak sub (weakNormalize w) $ \w' sub' ->
         weaken w' <$> hsubstLF sub' x

     Type -> foldLF Type

     KPi nm a k   -> foldLF =<< (KPi nm <$> hsubst sub a <*> hsubst sub' k)

     AType x       -> foldLF =<< (AType <$> hsubst sub x)
     TyPi nm a a'  -> foldLF =<< (TyPi nm <$> hsubst sub a <*> hsubst sub' a')
     TyRecord row  -> foldLF =<< (TyRecord <$> hsubst sub row)
     TyRow fldSet  -> foldLF (TyRow fldSet)

     TyConst _ ->
        case sub of
          SubstRefl   -> return tm
          SubstWeak w s -> weaken w <$> hsubst s tm
          _ -> error "impossible"

     TyApp p m    -> foldLF =<< (TyApp <$> hsubst sub p <*> hsubst sub m)

     Lam nm a m   -> foldLF =<< (Lam nm <$> hsubst sub a <*> hsubst sub' m)

     Record flds -> foldLF =<< (Record <$> traverse (hsubst sub) flds)
     RecordModify r del ins -> do
        x    <- hsubstTm sub r
        ins' <- traverse (hsubst sub) ins
        case x of
          Left m -> recordModify m WeakRefl del ins'
          Right r' -> foldLF (RecordModify r' del ins')

     Row flds    -> foldLF =<< (Row <$> traverse (hsubst sub) flds)
     RowModify r del ins -> do
        x    <- hsubstTm sub r
        ins' <- traverse (hsubst sub) ins
        case x of
          Left m -> rowModify m WeakRefl del ins'
          Right r' -> foldLF (RowModify r' del ins')

     And cs       -> foldLF . And =<< (mapM (hsubst sub) cs)

     Unify r1 r2  -> do
        r1' <- f =<< hsubstTm sub r1
        r2' <- f =<< hsubstTm sub r2
        foldLF (Unify r1' r2')

     Forall nm a c -> foldLF =<< (Forall nm <$> hsubst sub a <*> hsubst sub' c)
     Exists nm a c -> foldLF =<< (Exists nm <$> hsubst sub a <*> hsubst sub' c)

     Sigma nm a g  -> foldLF =<< (Sigma nm <$> hsubst sub a <*> hsubst sub' g)
     Goal m c      -> foldLF =<< (Goal <$> hsubst sub m <*> hsubst sub c)
     Fail          -> foldLF Fail

     ATerm x       -> either return (return . aterm) =<< hsubstTm sub x
     Const _       -> f =<< hsubstTm sub tm
     Var           -> f =<< hsubstTm sub tm
     App _ _       -> f =<< hsubstTm sub tm
     UVar _        -> f =<< hsubstTm sub tm
     Project _ _   -> f =<< hsubstTm sub tm

 where
  sub' :: forall b. Subst f (γ ::> b) (γ' ::> b)
  sub' = SubstSkip sub

  f :: Either (f γ' TERM) (f γ' ATERM) -> m (f γ' ATERM)
  f (Left r)  = return $ extractATerm r
  f (Right r) = return r


{- FIXME? rewrite this in continuation passing form
    to avoid repeated matching on Either values. -}
hsubstTm :: forall m f γ γ'
          . (LFModel f m, ?soln :: LFSoln f)
         => Subst f γ γ'
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
               SubstWeak w s  -> either (Left . weaken w) (Right . weaken w) <$> hsubstTm s tm
               SubstApply _ x -> return $ Left x
               SubstSkip _    -> Right <$> foldLF Var

           UVar u ->
             case sub of
               SubstRefl ->
                 case lookupUVar u ?soln of
                   Just m  -> return $ Left m
                   Nothing -> return $ Right tm
               SubstWeak w s -> either (Left . weaken w) (Right . weaken w) <$> hsubstTm s tm
               _ -> error "impossible"

           Const _ ->
             case sub of
               SubstRefl   -> return $ Right tm
               SubstWeak w s -> either (Left . weaken w) (Right . weaken w) <$> hsubstTm s tm
               _ -> error "impossible"

           Project r fld ->
             case sub of
               SubstRefl -> return $ Right tm
               _ -> do
                 r' <- hsubstTm sub r
                 case r' of
                   Left m' ->
                     Left <$> goproj WeakRefl m' fld
                   Right r'' ->
                     Right <$> foldLF (Project r'' fld)

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
  goproj :: forall γ. Weakening γ γ' -> f γ TERM -> LFRecordIndex f -> m (f γ' TERM)
  goproj w x' fld =
    case unfoldLF x' of
      Weak w' x'' -> goproj (weakCompose w w') x'' fld
      Record flds ->
        case Map.lookup fld flds of
          Just m -> return $ weaken w m
          Nothing -> fail "hereditary substituion failed: ill-typed record projection"
      _ -> fail "hereditary substituion failed: ill-typed record projection"

  gosub :: forall γ₁ γ₂. Weakening γ₁ γ' -> Weakening γ₂ γ' -> f γ₁ TERM -> f γ₂ TERM -> m (f γ' TERM)
  gosub w1 w2 x' y' =
   case (unfoldLF x', unfoldLF y') of
     (Weak w1' x'', _) -> gosub (weakCompose w1 w1') w2 x'' y'
     (_, Weak w2' y'') -> gosub w1 (weakCompose w2 w2') x' y''
     (Lam _ _ m, _) ->
        mergeWeak (weakNormalize w1) (weakNormalize w2) $ \wcommon w1' w2' ->
            weaken wcommon <$>
              let sub' = SubstApply (SubstWeak w1' SubstRefl) (weaken w2' y') in
              hsubst sub' m
     _ -> fail "hereditary substitution failed: ill-typed function application"
