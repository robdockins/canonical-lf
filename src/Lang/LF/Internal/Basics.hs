module Lang.LF.Internal.Basics where

import           Control.Monad
import           Data.Hashable
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Internal.Model
import Lang.LF.Internal.Weak

var0 :: (LFModel f m) => Var γ -> Weakening γ γ' -> m (f γ' ATERM)
var0 (F x) w = var0 x (WeakRight w)
var0 B w = weaken w <$> foldLF Var


app :: forall m f γ. (LFModel f m)
    => m (f γ TERM)
    -> m (f γ TERM)
    -> m (f γ TERM)
app x y = join (go WeakRefl WeakRefl <$> x <*> y)
 where
  go :: forall γ₁ γ₂
      . Weakening γ₁ γ -> Weakening γ₂ γ -> f γ₁ TERM -> f γ₂ TERM -> m (f γ TERM)
  go w1 w2 x' y' =
   case (unfoldLF x', unfoldLF y') of
     (Weak w1' x'', _) -> go (weakCompose w1 w1') w2 x'' y'
     (_, Weak w2' y'') -> go w1 (weakCompose w2 w2') x' y''
     (ATerm r, _) ->
        mergeWeak (weakNormalize w1) (weakNormalize w2) $ \wcommon w1' w2' ->
          weaken wcommon . aterm <$> foldLF (App (weaken w1' r) (weaken w2' y'))
     (Record _, _) ->
        fail "cannot apply values to records"
     (RecordModify{}, _) ->
        fail "cannot apply values to records"
     (Row{}, _) ->
        fail "cannot apply values to rows"
     (RowModify{}, _) ->
        fail "cannot apply values to rows"
     (Lam _ _ m, _) ->
        mergeWeak (weakNormalize w1) (weakNormalize w2) $ \wcommon w1' w2' ->
          weaken wcommon <$>
            let sub = (SubstApply (SubstWeak w1' SubstRefl) (weaken w2' y')) in
            withCurrentSolution (hsubst sub m)

recordModify :: LFModel f m
          => f γ TERM
          -> Weakening γ γ'
          -> Set (LFRecordIndex f)
          -> Map (LFRecordIndex f) (f γ' TERM)
          -> m (f γ' TERM)
recordModify m w del ins =
  case unfoldLF m of
    Weak w' m' -> recordModify m' (weakCompose w w') del ins
    Record flds -> do
        let flds'  = Map.filterWithKey (\k _ -> not (Set.member k del)) (fmap (weaken w) flds)
        let flds'' = Map.union flds' ins
        foldLF (Record flds'')
    RecordModify r del0 ins0 -> do
        let ins0'  = Map.filterWithKey (\k _ -> not (Set.member k del)) (fmap (weaken w) ins0)
        let ins0'' = Map.union ins0' ins
        let del0'  = Set.union del0 (Set.difference del (Map.keysSet ins0))
        foldLF (RecordModify (weaken w r) del0' ins0'')
    ATerm r -> foldLF (RecordModify (weaken w r) del ins)

    Lam _ _ _ -> fail "Expected record value"
    Row{} -> fail "Expected record value"
    RowModify{} -> fail "Expected record value"


rowModify :: LFModel f m
          => f γ TERM
          -> Weakening γ γ'
          -> Set (LFRecordIndex f)
          -> Map (LFRecordIndex f) (f γ' TYPE)
          -> m (f γ' TERM)
rowModify m w del ins =
  case unfoldLF m of
    Weak w' m' -> rowModify m' (weakCompose w w') del ins
    Row row -> do
        let row'  = Map.filterWithKey (\k _ -> not (Set.member k del)) (fmap (weaken w) row)
        let row'' = Map.union row' ins
        foldLF (Row row'')
    RowModify r del0 ins0 -> do
        let ins0'  = Map.filterWithKey (\k _ -> not (Set.member k del)) (fmap (weaken w) ins0)
        let ins0'' = Map.union ins0' ins
        let del0'  = Set.union del0 (Set.difference del (Map.keysSet ins0))
        foldLF (RowModify (weaken w r) del0' ins0'')
    ATerm r -> foldLF (RowModify (weaken w r) del ins)
    Lam _ _ _ -> fail "Expected row value"
    Record _ -> fail "Expected row value"
    RecordModify{} -> fail "Expected row value"


alphaEqLF :: forall f m γ₁ γ₂ γ s
           . LFModel f m
          => Weakening γ₁ γ
          -> Weakening γ₂ γ
          -> f γ₁ s
          -> f γ₂ s
          -> Bool
alphaEqLF w₁ w₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak w x'   , _)              -> alphaEqFull (weakCompose w₁ w) w₂ x' y
    (_           , Weak w y')      -> alphaEqFull w₁ (weakCompose w₂ w) x y'
    (Type        , Type)           -> True
    (KPi _ a k   , KPi _ a' k')    -> (&&) (alphaEqFull w₁ w₂ a a') (alphaEqFull (weakSkip w₁) (weakSkip w₂) k k')
    (AType x     , AType x')       -> alphaEqFull w₁ w₂ x x'
    (TyPi _ a1 a2, TyPi _ a1' a2') -> (&&) (alphaEqFull w₁ w₂ a1 a1') (alphaEqFull (weakSkip w₁) (weakSkip w₂) a2 a2')
    (TyRecord r1 , TyRecord r2)    -> alphaEqFull w₁ w₂ r1 r2
    (TyRow fs1   , TyRow fs2)      -> fs1 == fs2
    (TyConst x   , TyConst x')     -> x == x'
    (TyApp a m   , TyApp a' m')    -> (&&) (alphaEqFull w₁ w₂ a a') (alphaEqFull w₁ w₂ m m')
    (ATerm x     , ATerm x')       -> alphaEqFull w₁ w₂ x x'
    (Lam _ a m   , Lam _ a' m')    -> (&&) (alphaEqFull w₁ w₂ a a') (alphaEqFull (weakSkip w₁) (weakSkip w₂) m m')
    (Row fs1     , Row fs2)        -> minimum $ mergeFlds fs1 fs2
    ( RowModify r1 del1 ins1
     , RowModify r2 del2 ins2)     -> and [ alphaEqFull w₁ w₂ r1 r2
                                          , del1 == del2
                                          , minimum $ mergeFlds ins1 ins2
                                          ]
    (Record fs1  , Record fs2)     -> minimum $ mergeFlds fs1 fs2
    (RecordModify r1 del1 ins1
     , RecordModify r2 del2 ins2)  -> and [ alphaEqFull w₁ w₂ r1 r2
                                          , del1 == del2
                                          , minimum $ mergeFlds ins1 ins2
                                          ]
    (Var         , Var)            -> weakenVar w₁ B == weakenVar w₂ B
    (UVar u      , UVar u')        -> u == u'
    (Const x     , Const x')       -> x == x'
    (App r m     , App r' m')      -> (&&) (alphaEqFull w₁ w₂ r r') (alphaEqFull w₁ w₂ m m')
    ( Project r1 f1
     , Project r2 f2)              -> (&&) (alphaEqFull w₁ w₂ r1 r2) (f1 == f2)

    (Fail        , Fail)           -> True
    (Unify r1 r2 , Unify r1' r2')  -> (&&) (alphaEqFull w₁ w₂ r1 r1') (alphaEqFull w₁ w₂ r2 r2')
    (And cs      , And cs')        -> and (zipWith (alphaEqFull w₁ w₂) cs cs')
    (Forall _ a c, Forall _ a' c') -> (&&) (alphaEqFull w₁ w₂ a a') (alphaEqFull (weakSkip w₁) (weakSkip w₂) c c')
    (Exists _ a c, Exists _ a' c') -> (&&) (alphaEqFull w₁ w₂ a a') (alphaEqFull (weakSkip w₁) (weakSkip w₂) c c')
    (Sigma _ a g , Sigma _ a' g')  -> (&&) (alphaEqFull w₁ w₂ a a') (alphaEqFull (weakSkip w₁) (weakSkip w₂) g g')
    (Goal m c    , Goal m' c')     -> (&&) (alphaEqFull w₁ w₂ m m') (alphaEqFull w₁ w₂ c c')
    _ -> False

 where mergeFlds :: forall s
                  . Map (LFRecordIndex f) (f γ₁ s)
                 -> Map (LFRecordIndex f) (f γ₂ s)
                 -> Map (LFRecordIndex f) Bool
       mergeFlds = Map.mergeWithKey
                     (\_k t1 t2 -> Just $ alphaEqFull w₁ w₂ t1 t2)
                     (fmap $ const False)
                     (fmap $ const False)

data VarSet :: Ctx * -> * where
  VarSetEmpty :: VarSet γ
  VarSetCons  :: !(VarSet γ) -> !Int -> VarSet (γ ::> b)

eqVarSet :: VarSet γ -> VarSet γ -> Bool
eqVarSet VarSetEmpty VarSetEmpty = True
eqVarSet (VarSetCons x a) VarSetEmpty
  | a == 0    = eqVarSet x VarSetEmpty
  | otherwise = False
eqVarSet VarSetEmpty (VarSetCons y b)
  | 0 == b    = eqVarSet VarSetEmpty y
  | otherwise = False
eqVarSet (VarSetCons x a) (VarSetCons y b)
  | a == b    = eqVarSet x y
  | otherwise = False

instance Eq (VarSet γ) where
  (==) = eqVarSet

mergeVarSet :: VarSet γ -> VarSet γ -> VarSet γ
mergeVarSet VarSetEmpty y = y
mergeVarSet x VarSetEmpty = x
mergeVarSet (VarSetCons v b) (VarSetCons v' b') =
   VarSetCons (mergeVarSet v v') (b + b')

singleVarSet :: Var γ -> VarSet γ
singleVarSet (F f) = VarSetCons (singleVarSet f) 0
singleVarSet B     = VarSetCons VarSetEmpty 1

emptyVarSet :: VarSet γ
emptyVarSet = VarSetEmpty

inVarSet :: VarSet γ -> Var γ -> Bool
inVarSet s v = lookupVarSet s v > 0

lookupVarSet :: VarSet γ -> Var γ -> Int
lookupVarSet VarSetEmpty _ = 0
lookupVarSet (VarSetCons s _) (F v) = lookupVarSet s v
lookupVarSet (VarSetCons _ x) B = x

varCensusLF :: LFModel f m => Var γ -> f γ s -> Int
varCensusLF v tm = lookupVarSet (countCensus tm) v

freeVarLF :: LFModel f m => Var γ -> f γ s -> Bool
freeVarLF v tm = inVarSet (countCensus tm) v

strengthenVarSet :: VarSet (γ ::> a) -> VarSet γ
strengthenVarSet (VarSetCons vs _) = vs
strengthenVarSet VarSetEmpty       = VarSetEmpty

weakenVarSet :: Weakening γ γ' -> VarSet γ -> VarSet γ'
weakenVarSet WeakRefl      vs = vs
weakenVarSet (WeakLeft w)  vs = VarSetCons (weakenVarSet w vs) 0
weakenVarSet (WeakRight w) vs = weakenVarSet w (VarSetCons vs 0)
weakenVarSet (WeakSkip w)  (VarSetCons vs x) = VarSetCons (weakenVarSet w vs) x
weakenVarSet (WeakSkip w)  VarSetEmpty       = VarSetCons (weakenVarSet w VarSetEmpty) 0


countCensus :: LFModel f m
         => f γ s
         -> VarSet γ
countCensus = foldFree mergeVarSet emptyVarSet singleVarSet

foldFree :: forall f m γ a s
          . LFModel f m
         => (a -> a -> a)
         -> a
         -> (Var γ -> a)
         -> f γ s
         -> a
foldFree merge z = go
 where
  go :: forall γ s. (Var γ -> a) -> f γ s -> a
  go f tm =
    let f' :: forall b. (Var (γ ::> b) -> a)
        f' B     = z
        f' (F x) = f x
     in
    case unfoldLF tm of
      Weak w x -> go (f . weakenVar w) x
      Type -> z
      KPi _ a k -> go f a `merge` go f' k
      AType x -> go f x
      TyPi _ a1 a2 -> go f a1 `merge` go f' a2
      TyConst _ -> z
      TyApp p a -> go f p `merge` go f a
      TyRecord row -> go f row
      TyRow _fldSet -> z
      Lam _ a m -> go f a `merge` go f' m
      Row flds -> foldr merge z $ map (go f) $ Map.elems flds
      RowModify r _delSet insMap -> foldr merge (go f r) $ map (go f) $ Map.elems insMap
      Record flds -> foldr merge z $ map (go f) $ Map.elems flds
      RecordModify r _delSet insMap -> foldr merge (go f r) $ map (go f) $ Map.elems insMap
      Const _ -> z
      ATerm x -> go f x
      App r m -> go f r `merge` go f m
      Var -> f B
      Project x _ -> go f x
      Unify r1 r2 -> go f r1 `merge` go f r2
      And cs -> foldr merge z $ map (go f) cs
      Forall _ a c -> go f a `merge` go f' c
      Exists _ a c -> go f a `merge` go f' c
      Sigma _ a g -> go f a `merge` go f' g
      Goal m c -> go f m `merge` go f c
      Fail -> z
      UVar _ -> z

freeUVarsLF :: LFModel f m
            => f γ s
            -> Set (LFUVar f)
freeUVarsLF tm =
  case unfoldLF tm of
    Weak _ x -> freeUVars x
    Type -> Set.empty
    KPi _ a k -> Set.union (freeUVars a) (freeUVars k)
    AType x -> freeUVars x
    TyPi _ a1 a2 -> Set.union (freeUVars a1) (freeUVars a2)
    TyConst _ -> Set.empty
    TyApp p a -> Set.union (freeUVars p) (freeUVars a)
    TyRow _fldSet -> Set.empty
    TyRecord row -> freeUVars row
    Lam _ a m -> Set.union (freeUVars a) (freeUVars m)
    Row flds -> Set.unions $ map freeUVars $ Map.elems flds
    RowModify r _delSet insMap ->
        Set.union (freeUVars r) $ Set.unions $ map freeUVars $ Map.elems insMap
    Record flds -> Set.unions $ map freeUVars $ Map.elems flds
    RecordModify r _delSet insMap ->
        Set.union (freeUVars r) $ Set.unions $ map freeUVars $ Map.elems insMap
    Const _ -> Set.empty
    ATerm x -> freeUVars x
    App r m -> Set.union (freeUVars r) (freeUVars m)
    Var -> Set.empty
    Project x _ -> freeUVars x
    Unify r1 r2 -> Set.union (freeUVars r1) (freeUVars r2)
    And cs -> Set.unions (map freeUVars cs)
    Forall _ a c -> Set.union (freeUVars a) (freeUVars c)
    Exists _ a c -> Set.union (freeUVars a) (freeUVars c)
    Sigma _ a g -> Set.union (freeUVars a) (freeUVars g)
    Goal m c -> Set.union (freeUVars m) (freeUVars c)
    Fail -> Set.empty
    UVar v -> Set.singleton v


weakenEnv :: Weakening γ γ' -> Seq a -> Maybe (Seq a)
weakenEnv w env =
  case w of
    WeakSkip w ->
      case Seq.viewl env of
        x Seq.:< env' -> (x Seq.<|) <$> weakenEnv w env'
        Seq.EmptyL    -> Nothing
    WeakLeft w ->
      case Seq.viewl env of
        _ Seq.:< env' -> weakenEnv w env'
        Seq.EmptyL    -> Nothing
    WeakRight w ->
      case Seq.viewr env of
        env' Seq.:> _ -> weakenEnv w env'
        Seq.EmptyR    -> Nothing
    WeakRefl ->
      Just env

evaluateLF :: forall f γ m a
            . (LFModel f m, ?soln :: LFSoln f)
           => LFAlgebra f m a
           -> f γ TERM
           -> Seq (LFVal f m a)
           -> m (LFVal f m a)
evaluateLF eval_const = gom
 where
  gor :: forall γ. f γ ATERM -> Seq (LFVal f m a) -> [LFVal f m a] -> m (LFVal f m a)
  gor r env args =
    case unfoldLF r of
      Weak w x ->
        case weakenEnv w env of
          Just env' ->
            gor x env' args
          Nothing ->
            fail "insufficent arguments"
      Var ->
        case Seq.viewl env of
          x Seq.:< _ -> applyAll x args
          Seq.EmptyL -> fail $ "insufficent arguments"
      UVar u  ->
        case lookupUVar u ?soln of
          Just m -> do
            m' <- gom m env
            applyAll m' args
          Nothing ->
            fail $ unwords ["Unbound UVar found in evaluate:", show (pretty u)]
      Const c ->
        eval_const c args
      App r m -> do
        m' <- gom m env
        gor r env (m':args)
      Project r f -> do
        r' <- gor r env []
        x  <- project r' f
        applyAll x args

  apply :: LFVal f m a -> LFVal f m a -> m (LFVal f m a)
  apply (ValLam f) x = f x
  apply _ _ = fail "Expected function"

  project :: LFVal f m a -> LFRecordIndex f -> m (LFVal f m a)
  project (ValRecord xs) f =
    case Map.lookup f xs of
      Just x  -> return x
      Nothing -> fail $ unwords ["missing field", show (pretty f)]
  project _ _=
    fail $ "expected record value"

  applyAll :: LFVal f m a -> [LFVal f m a] -> m (LFVal f m a)
  applyAll x []     = return x
  applyAll x (a:as) = apply x a >>= \x' -> applyAll x' as

  gom :: forall γ. f γ TERM -> Seq (LFVal f m a) -> m (LFVal f m a)
  gom m env =
    case unfoldLF m of
      Weak w x   ->
        case weakenEnv w env of
          Just env' ->
            gom x env'
          Nothing ->
            fail $ "insufficent arguments"
      ATerm r    ->
        gor r env []
      Lam _ _ m' ->
        return $ ValLam (\x -> gom m' (x Seq.<| env))
      Record xs  ->
        ValRecord <$> traverse (\x -> gom x env) xs
      RecordModify r del ins -> do
        r' <- gor r env []
        case r' of
          ValRecord xs -> do
            let xs'  = Map.filterWithKey (\k _ -> not (Set.member k del)) xs
            xs'' <- Map.union xs' <$> traverse (\x -> gom x env) ins
            return $ ValRecord xs''
          _ -> fail "Expected record value"
      Row xs ->
        return $ ValRow $ Map.keysSet xs
      RowModify r del ins -> do
        r' <- gor r env []
        case r' of
          ValRow xs ->
            return $ ValRow $ Set.union (Set.difference xs del) (Map.keysSet ins)
          _ -> fail "Expected row value"


-- | This function calculates a hash value on the structure of a term.
--   Note: the strucutre of a term explicitly ignores the identity of
--   deBruijn variables and all suspended weakenings.  This ensures that
--   structural hashing commutes with weakenings.  In particular, we do
--   not have to recalculate hash values when we push weakenings further
--   down into a term.
structuralHash :: forall f.
  ( Hashable (LFTypeConst f)
  , Hashable (LFConst f)
  , Hashable (LFRecordIndex f)
  , Hashable (LFUVar f)
  )
  => (forall γ s. Var γ -> f γ s -> Int)
  -> (forall γ s. f γ s -> Int)
  -> (forall γ s. LF f γ s -> Int)
structuralHash census h tm =
  let hashFieldSet :: Int -> FieldSet f -> Int
      hashFieldSet c (PosFieldSet fs) = hashSet (hashWithSalt 100 c) fs
      hashFieldSet c (NegFieldSet fs) = hashSet (hashWithSalt 200 c) fs

      hashSet :: Int -> Set (LFRecordIndex f) -> Int
      hashSet c fs = foldl hashWithSalt c $ Set.toAscList fs

      hashMap :: forall γ s. Int -> Map (LFRecordIndex f) (f γ s) -> Int
      hashMap c fs =
          foldl (\c' (i,t) -> hashWithSalt c' (hashWithSalt (h t) i))
                c
                (Map.toAscList fs)
  in case tm of
    -- NB: skip all weakenings
    Weak _ x     -> h x

    Type         -> 1
    KPi _ t k    -> hashWithSalt (hashWithSalt 2 (census B k))
                                 (hashWithSalt (h t) (h k))
    AType x      -> h x
    TyPi _ t1 t2 -> hashWithSalt (hashWithSalt 3 (census B t2))
                                 (hashWithSalt (h t1) (h t2))
    TyRecord r   -> hashWithSalt 4 (h r)
    TyRow fs     -> hashFieldSet 5 fs
    TyConst c    -> hashWithSalt 6 c
    TyApp r m    -> hashWithSalt 7 (hashWithSalt (h r) (h m))

    ATerm x      -> h x
    Lam _ t m    -> hashWithSalt (hashWithSalt 8 (census B m))
                                 (hashWithSalt (h t) (h m))
    Row fs       -> hashMap 9 fs
    RowModify r del ins
                 -> hashMap (hashSet (hashWithSalt 10 (h r)) del) ins
    Record fs    -> hashMap 11 fs
    RecordModify r del ins
                 -> hashMap (hashSet (hashWithSalt 12 (h r)) del) ins

    -- NB: all variables hash to the same value.  This is deliberate
    Var          -> 13

    UVar u       -> hashWithSalt 14 u
    Const c      -> hashWithSalt 15 c
    App r m      -> hashWithSalt 16 (hashWithSalt (h r) (h m))
    Project r f  -> hashWithSalt 17 (hashWithSalt (h r) f)

    Fail         -> 18
    Unify x y    -> hashWithSalt 18 (hashWithSalt (h x) (h y))
    And xs       -> foldl hashWithSalt 19 $ map h xs
    Forall _ k c -> hashWithSalt (hashWithSalt 20 (census B c))
                                 (hashWithSalt (h k) (h c))
    Exists _ k c -> hashWithSalt (hashWithSalt 21 (census B c))
                                 (hashWithSalt (h k) (h c))
    Sigma _ k g  -> hashWithSalt (hashWithSalt 22 (census B g))
                                 (hashWithSalt (h k) (h g))
    Goal m c     -> hashWithSalt 23 (hashWithSalt (h m) (h c))
