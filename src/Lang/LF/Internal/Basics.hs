module Lang.LF.Internal.Basics where

import           Control.Monad
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

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
    (Weak w x'   , _)              -> alphaEqLF (weakCompose w₁ w) w₂ x' y
    (_           , Weak w y')      -> alphaEqLF w₁ (weakCompose w₂ w) x y'
    (Type        , Type)           -> True
    (KPi _ a k   , KPi _ a' k')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) k k')
    (AType x     , AType x')       -> alphaEqLF w₁ w₂ x x'
    (TyPi _ a1 a2, TyPi _ a1' a2') -> (&&) (alphaEqLF w₁ w₂ a1 a1') (alphaEqLF (weakSkip w₁) (weakSkip w₂) a2 a2')
    (TyRecord r1 , TyRecord r2)    -> alphaEqLF w₁ w₂ r1 r2
    (TyRow fs1   , TyRow fs2)      -> fs1 == fs2
    (TyConst x   , TyConst x')     -> x == x'
    (TyApp a m   , TyApp a' m')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF w₁ w₂ m m')
    (ATerm x     , ATerm x')       -> alphaEqLF w₁ w₂ x x'
    (Lam _ a m   , Lam _ a' m')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) m m')
    (Row fs1     , Row fs2)        -> minimum $ mergeFlds fs1 fs2
    ( RowModify r1 del1 ins1
     , RowModify r2 del2 ins2)     -> and [ alphaEqLF w₁ w₂ r1 r2
                                          , del1 == del2
                                          , minimum $ mergeFlds ins1 ins2
                                          ]
    (Record fs1  , Record fs2)     -> minimum $ mergeFlds fs1 fs2
    (RecordModify r1 del1 ins1
     , RecordModify r2 del2 ins2)  -> and [ alphaEqLF w₁ w₂ r1 r2
                                          , del1 == del2
                                          , minimum $ mergeFlds ins1 ins2
                                          ]
    (Var         , Var)            -> weakenVar w₁ B == weakenVar w₂ B
    (UVar u      , UVar u')        -> u == u'
    (Const x     , Const x')       -> x == x'
    (App r m     , App r' m')      -> (&&) (alphaEqLF w₁ w₂ r r') (alphaEqLF w₁ w₂ m m')
    ( Project r1 f1
     , Project r2 f2)              -> (&&) (alphaEqLF w₁ w₂ r1 r2) (f1 == f2)

    (Fail        , Fail)           -> True
    (Unify r1 r2 , Unify r1' r2')  -> (&&) (alphaEqLF w₁ w₂ r1 r1') (alphaEqLF w₁ w₂ r2 r2')
    (And cs      , And cs')        -> and (zipWith (alphaEqLF w₁ w₂) cs cs')
    (Forall _ a c, Forall _ a' c') -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) c c')
    (Exists _ a c, Exists _ a' c') -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) c c')
    (Sigma _ a g , Sigma _ a' g')  -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) g g')
    (Goal m c    , Goal m' c')     -> (&&) (alphaEqLF w₁ w₂ m m') (alphaEqLF w₁ w₂ c c')
    _ -> False

 where mergeFlds :: forall s
                  . Map (LFRecordIndex f) (f γ₁ s)
                 -> Map (LFRecordIndex f) (f γ₂ s)
                 -> Map (LFRecordIndex f) Bool
       mergeFlds = Map.mergeWithKey
                     (\_k t1 t2 -> Just $ alphaEqLF w₁ w₂ t1 t2)
                     (fmap $ const False)
                     (fmap $ const False)

data VarSet :: Ctx * -> * where
  VarSetEmpty :: VarSet γ
  VarSetCons  :: VarSet γ -> !Int -> VarSet (γ ::> b)

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


