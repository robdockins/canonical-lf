{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wwarn #-}
module Lang.LF.DAG
( LFDag
, M
, runM
) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Data.Foldable
import           Data.IORef
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Sequence (Seq, (|>) )
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
--import           Data.IntMap (IntMap)
--import qualified Data.IntMap as IntMap
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))



import Lang.LF.Internal.Basics
import Lang.LF.Internal.Model
import qualified Lang.LF.Internal.Hyps as H
import Lang.LF.Internal.Print
import Lang.LF.Internal.Solve
import Lang.LF.Internal.Subst
import Lang.LF.Internal.Typecheck
import Lang.LF.Internal.View
import Lang.LF.Internal.Weak


data DagUVar = DagUVar Int
  deriving (Eq,Ord)

instance Pretty DagUVar where
  pretty (DagUVar i) = text "#" <> text (show i)
instance Show DagUVar where
  show = show . pretty


data DagTerm a c i γ (s::SORT) =
   DagTerm
   { dagIndex     :: !Int
   , dagFreeUVars :: !IntSet
   , dagFreeVars  :: !(VarSet γ)
   , dagTerm      :: !(LF (LFDag a c i) γ s)
   }

data LFDag a c i γ (s::SORT)
 = DagShared (DagTerm a c i γ s)
 | DagUnshared (LF (LFDag a c i) γ s)

type instance LFTypeConst (LFDag a c i) = a
type instance LFConst (LFDag a c i) = c
type instance LFUVar (LFDag a c i) = DagUVar
type instance LFRecordIndex (LFDag a c i) = i

newtype instance LFSoln (LFDag a c i)
  = Soln (Map DagUVar (LFDag a c i E TERM))

data instance Hyps (LFDag a c i) γ
  = DagHyps
    { hypList :: H.LFHyps (LFDag a c i) γ
    , hypNms  :: Set String
    }


emptyDagHyps :: Hyps (LFDag a c i) E
emptyDagHyps = DagHyps H.HNil Set.empty

extendDagHyps :: Hyps (LFDag a c i) γ
              -> String
              -> Quant
              -> LFDag a c i γ TYPE
              -> Hyps (LFDag a c i) (γ::>b)
extendDagHyps (DagHyps h nms) nm q ty =
  let nm'  = H.freshName nms nm
      nms' = Set.insert nm' nms
      h'   = H.extendHyps h nm' q ty
   in DagHyps h' nms'

data LFDagState a c i =
  LFDagState
  { indexGen     :: IORef Int
  , uvarGen      :: IORef Int
  , curSoln      :: IORef (Map DagUVar (LFDag a c i E TERM))
  , uvarTypes    :: IORef (Map DagUVar (LFDag a c i E TYPE))
  , sigFamilies  :: Map a (LFDag a c i E KIND)
  , sigTerms     :: Map c (LFDag a c i E TYPE)
  , sigDecls     :: Seq (SigDecl (LFDag a c i) Identity)
--  , tcValidKinds :: IORef IntSet
--  , tcValidTypes :: IORef IntSet
--  , tcKinds      :: IORef (IntMap (LFDag a c i E
  }

newLFDagState :: IO (LFDagState a c i)
newLFDagState =
  LFDagState
    <$> newIORef 0
    <*> newIORef 0
    <*> newIORef Map.empty
    <*> newIORef Map.empty
    <*> return Map.empty
    <*> return Map.empty
    <*> return Seq.empty

newtype M a c i x =
  M { unM :: ReaderT (LFDagState a c i) (ExceptT String IO) x }

deriving instance Functor (M a c i)
deriving instance Applicative (M a c i)
deriving instance Monad (M a c i)
deriving instance MonadIO (M a c i)

instance (Ord a, Ord c, Ord i, Pretty a, Pretty c, Pretty i)
         => LFModel (LFDag a c i) (M a c i) where

  unfoldLF m =
    case m of
      DagShared tm -> dagTerm tm
      DagUnshared tm -> tm

  weaken WeakRefl x = x
  weaken w' (DagUnshared (Weak w x)) =
    DagUnshared (Weak (weakCompose w' w) x)
  weaken w' m =
    DagUnshared (Weak w' m)

  aterm = DagUnshared . ATerm
  atype = DagUnshared . AType

  foldLF (Weak w x) =
    return $ weaken w x
  foldLF tm = M $ do
    st  <- ask
    idx <- liftIO $ atomicModifyIORef' (indexGen st) (\n -> (n+1,n))
    let fv  = calcFreeVars' tm
    let ufv = calcFreeUVars' tm
    let dtm = DagTerm
              { dagIndex = idx
              , dagFreeVars = fv
              , dagFreeUVars = ufv
              , dagTerm = tm
              }
    return $ DagShared dtm

  hsubst = hsubstLF
  instantiate = instantiateLF
  abstractUVars = abstractLF
  ppLF = prettyLF
  validateKind = validateKindLF
  validateType = validateTypeLF
  inferKind = inferKindLF
  inferType = inferTypeLF
  inferAType = inferATypeLF
  validateGoal = validateGoalLF
  validateCon = validateConLF

  -- FIXME? Can we do better than this for alpha-equivalance?
  alphaEq (DagShared x) (DagShared y)
     | dagIndex x == dagIndex y = True
  alphaEq x y = alphaEqLF WeakRefl WeakRefl x y

  constKind a = M $ do
     sig <- ask
     case Map.lookup a (sigFamilies sig) of
       Nothing -> fail $ unwords ["type family lookup failed:", show (pretty a)]
       Just x  -> return x
  constType c = M $ do
     sig <- ask
     case Map.lookup c (sigTerms sig) of
       Nothing -> fail $ unwords ["term constant lookup failed:", show (pretty c)]
       Just x  -> return x

  varCensus v x = lookupVarSet (calcFreeVars x) v
  freeVar v x = inVarSet (calcFreeVars x) v
  freeUVars x =
    Set.fromDistinctAscList $ map DagUVar $ IntSet.toAscList $ calcFreeUVars x

  kindView = kindViewLF WeakRefl
  typeView = typeViewLF WeakRefl
  termView = termViewLF WeakRefl
  goalView = goalViewLF WeakRefl
  constraintView = constraintViewLF WeakRefl

  freshUVar tp = M $ do
    st <- ask
    uidx <- liftIO $ atomicModifyIORef' (uvarGen st) (\n -> (n+1,n))
    let u = DagUVar uidx
    liftIO $ atomicModifyIORef' (uvarTypes st) (\tps -> (Map.insert u tp tps, ()))
    return u

  withCurrentSolution x = M $ do
    st <- ask
    soln <- liftIO $ readIORef (curSoln st)
    let ?soln = Soln soln in unM x
  commitSolution (Soln soln) = M $ do
    st <- ask
    liftIO $ writeIORef (curSoln st) soln
  lookupUVar u (Soln soln) = Map.lookup u soln
  assignUVar v m (Soln soln)  = return $ Soln $ Map.insert v m soln
  uvarType u = M $ do
    st <- ask
    tps <- liftIO $ readIORef (uvarTypes st)
    case Map.lookup u tps of
      Just tp -> return tp
      Nothing -> fail $ unwords ["unknown uvar:", show u]
  emptySolution = Soln $ Map.empty
  extendSolution u tm (Soln soln) =
    case Map.lookup u soln of
      Nothing -> Just $ Soln $ Map.insert u tm soln
      Just _  -> Nothing

  solve = solveLF

  getSignature = M $ do
    toList . sigDecls <$> ask

  extendSignature [] m = m
  extendSignature ((a ::. ty) : xs) m = M $ ReaderT $ \sig -> do
    sig' <- addTypeConstant sig a ty
    runReaderT (unM (extendSignature xs m)) sig'
  extendSignature ((c :. tm) : xs) m = M $ ReaderT $ \sig -> do
    sig' <- addTermConstant sig c tm
    runReaderT (unM (extendSignature xs m)) sig'

  evaluate = evaluateLF -- FIXME, memo tables and such...

  freshName nm = H.freshName (hypNms ?hyps) nm
  inEmptyCtx x = let ?hyps = emptyDagHyps in x
  extendCtx nm q a x = let ?hyps = extendDagHyps ?hyps nm q a in x
  lookupCtx v = H.lookupHyp (hypList ?hyps) v WeakRefl

calcFreeVars :: LFDag a c i γ s -> VarSet γ
calcFreeVars (DagShared x) = dagFreeVars x
calcFreeVars (DagUnshared tf) = calcFreeVars' tf

calcFreeVars' :: LF (LFDag a c i) γ s -> VarSet γ
calcFreeVars' t =
  case t of
    Weak w x          -> weakenVarSet w (calcFreeVars x)

    Type              -> emptyVarSet
    KPi _ t k         -> calcFreeVars t `mergeVarSet`
                         strengthenVarSet (calcFreeVars k)

    AType x           -> calcFreeVars x
    TyPi _ t1 t2      -> calcFreeVars t1 `mergeVarSet`
                         strengthenVarSet (calcFreeVars t2)

    TyRecord row      -> calcFreeVars row
    TyRow _           -> emptyVarSet
    TyConst _         -> emptyVarSet
    TyApp r m         -> calcFreeVars r `mergeVarSet`
                         calcFreeVars m

    ATerm x           -> calcFreeVars x
    Lam _ t m         -> calcFreeVars t `mergeVarSet`
                         strengthenVarSet (calcFreeVars m)
    Row xs            -> foldr mergeVarSet emptyVarSet $
                           map calcFreeVars $ Map.elems xs
    RowModify r _ ins -> foldr mergeVarSet (calcFreeVars r) $
                           map calcFreeVars $ Map.elems ins
    Record xs         -> foldr mergeVarSet emptyVarSet $
                           map calcFreeVars $ Map.elems xs
    RecordModify r _ ins -> foldr mergeVarSet (calcFreeVars r) $
                              map calcFreeVars $ Map.elems ins

    Var               -> VarSetCons VarSetEmpty 1
    UVar _            -> emptyVarSet
    Const _           -> emptyVarSet
    App r m           -> calcFreeVars r `mergeVarSet`
                         calcFreeVars m
    Project r _       -> calcFreeVars r

    Fail              -> emptyVarSet
    Unify x y         -> calcFreeVars x `mergeVarSet`
                         calcFreeVars y
    And xs            -> foldr mergeVarSet emptyVarSet $ map calcFreeVars xs
    Forall _ t c      -> calcFreeVars t `mergeVarSet`
                         strengthenVarSet (calcFreeVars c)
    Exists _ t c      -> calcFreeVars t `mergeVarSet`
                         strengthenVarSet (calcFreeVars c)
    Sigma _ t g       -> calcFreeVars t `mergeVarSet`
                         strengthenVarSet (calcFreeVars g)
    Goal m c          -> calcFreeVars m `mergeVarSet`
                         calcFreeVars c

calcFreeUVars :: LFDag a c i γ s -> IntSet
calcFreeUVars (DagShared tm) = dagFreeUVars tm
calcFreeUVars (DagUnshared tm) = calcFreeUVars' tm

calcFreeUVars' :: LF (LFDag a c i) γ s -> IntSet
calcFreeUVars' t =
  case t of
    Weak _w x         -> calcFreeUVars x

    Type              -> IntSet.empty
    KPi _ t k         -> calcFreeUVars t `IntSet.union`
                         calcFreeUVars k

    AType x           -> calcFreeUVars x
    TyPi _ t1 t2      -> calcFreeUVars t1 `IntSet.union`
                         calcFreeUVars t2

    TyRecord row      -> calcFreeUVars row
    TyRow _           -> IntSet.empty
    TyConst _         -> IntSet.empty
    TyApp r m         -> calcFreeUVars r `IntSet.union`
                         calcFreeUVars m

    ATerm x           -> calcFreeUVars x
    Lam _ t m         -> calcFreeUVars t `IntSet.union`
                         calcFreeUVars m
    Row xs            -> IntSet.unions $
                           map calcFreeUVars $ Map.elems xs
    RowModify r _ ins -> IntSet.unions $ (calcFreeUVars r:) $
                           map calcFreeUVars $ Map.elems ins
    Record xs         -> IntSet.unions $
                           map calcFreeUVars $ Map.elems xs
    RecordModify r _ ins -> IntSet.unions $ (calcFreeUVars r:) $
                              map calcFreeUVars $ Map.elems ins

    Var               -> IntSet.empty
    UVar (DagUVar u)  -> IntSet.singleton u
    Const _           -> IntSet.empty
    App r m           -> calcFreeUVars r `IntSet.union`
                         calcFreeUVars m
    Project r _       -> calcFreeUVars r

    Fail              -> IntSet.empty
    Unify x y         -> calcFreeUVars x `IntSet.union`
                         calcFreeUVars y
    And xs            -> IntSet.unions $ map calcFreeUVars xs
    Forall _ t c      -> calcFreeUVars t `IntSet.union`
                         calcFreeUVars c
    Exists _ t c      -> calcFreeUVars t `IntSet.union`
                         calcFreeUVars c
    Sigma _ t g       -> calcFreeUVars t `IntSet.union`
                         calcFreeUVars g
    Goal m c          -> calcFreeUVars m `IntSet.union`
                         calcFreeUVars c

addTypeConstant :: (Ord a, Ord c, Ord i, Pretty a, Pretty c, Pretty i)
                => LFDagState a c i
                -> a
                -> M a c i (LFDag a c i E KIND)
                -> ExceptT String IO (LFDagState a c i)
addTypeConstant sig nm m =
  case Map.lookup nm (sigFamilies sig) of
    Just _ -> fail $ unwords ["Type constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip runReaderT sig $ inEmptyCtx $ do
           k <- unM m
           let ?soln = Soln Map.empty
           unM $ validateKind WeakRefl k
           return sig{ sigFamilies = Map.insert nm k (sigFamilies sig)
                     , sigDecls = sigDecls sig |> (nm ::. return k)
                     }

addTermConstant :: (Ord a, Ord c, Ord i, Pretty a, Pretty c, Pretty i)
                => LFDagState a c i
                -> c
                -> M a c i (LFDag a c i E TYPE)
                -> ExceptT String IO (LFDagState a c i)
addTermConstant sig nm m =
  case Map.lookup nm (sigTerms sig) of
    Just _ -> fail $ unwords ["Term constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip runReaderT sig $ inEmptyCtx $ do
           x <- unM m
           let ?soln = Soln Map.empty
           unM $ validateType WeakRefl x
           return sig{ sigTerms = Map.insert nm x (sigTerms sig)
                     , sigDecls = sigDecls sig |> (nm :. return x)
                     }

runM :: (Ord a, Ord c, Ord i, Pretty a, Pretty c, Pretty i)
     => [SigDecl (LFDag a c i) (M a c i)]
     -> ((?soln :: LFSoln (LFDag a c i)) => M a c i x)
     -> IO x
runM sig m = do
  st <- newLFDagState
  let ?soln = Soln Map.empty
  either fail return =<<
   ( runExceptT
   $ flip runReaderT st
   $ unM
   $ extendSignature sig m
   )
