{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lang.LF.Tree
( LFTree
, M
, runM
, mkTerm
)
where

import           Control.Monad.Identity
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Foldable
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Internal.Basics
import qualified Lang.LF.Internal.Hyps as H
import Lang.LF.Internal.Model
import Lang.LF.Internal.Print
import Lang.LF.Internal.Solve
import Lang.LF.Internal.Subst
import Lang.LF.Internal.Typecheck
import Lang.LF.Internal.View

newtype LFTree a c γ (s::SORT) =
  LFTree { lfTree :: LF (LFTree a c) γ s
         }

instance (Pretty a, Pretty c, Ord a, Ord c) => Show (LFTree a c E s) where
  show x =
    runM [] (inEmptyCtx (let ?soln = Soln Map.empty in displayLF x))



data UVarState a c =
  UVarState
  { curSoln :: Soln a c
  , uvarTypes :: Map Integer (LFTree a c E TYPE)
  , uvarNext :: !Integer
  }

emptyUVarState :: UVarState a c
emptyUVarState =
  UVarState
  { curSoln = Map.empty
  , uvarTypes = Map.empty
  , uvarNext = 0
  }

type instance LFTypeConst (LFTree a c) = a
type instance LFConst (LFTree a c) = c
type instance LFUVar (LFTree a c) = Integer
type instance LFRecordIndex (LFTree a c) = String

type Soln a c = Map Integer (LFTree a c E TERM)
newtype instance LFSoln (LFTree a c) = Soln (Soln a c)

data instance Hyps (LFTree a c) γ =
  TreeHyps
  { hypList :: H.LFHyps (LFTree a c) γ
  , hypNms  :: Set String
  } 

emptyTreeHyps :: Hyps (LFTree a c) E
emptyTreeHyps = TreeHyps H.HNil Set.empty

extendTreeHyps :: Hyps (LFTree a c) γ
              -> String
              -> Quant
              -> LFTree a c γ TYPE
              -> Hyps (LFTree a c) (γ::>b)
extendTreeHyps (TreeHyps h nms) nm q ty =
  let nm'  = H.freshName nms nm
      nms' = Set.insert nm' nms
      h'   = H.extendHyps h nm' q ty
   in TreeHyps h' nms'

newtype M a c x = M { unM :: ReaderT (Signature a c) (StateT (UVarState a c) (Except String)) x }

deriving instance Functor (M a c)
deriving instance Applicative (M a c)
deriving instance Monad (M a c)

instance (Pretty a, Pretty c, Ord a, Ord c)
    => LFModel (LFTree a c) (M a c) where
  unfoldLF = lfTree
  foldLF = return . LFTree
  hsubst = hsubstLF
  weaken w = LFTree . Weak w
  aterm = LFTree . ATerm
  atype = LFTree . AType
  ppLF = prettyLF
  validateKind = validateKindLF
  validateType = validateTypeLF
  inferKind = inferKindLF
  inferType = inferTypeLF
  inferAType = inferATypeLF
  validateGoal = validateGoalLF
  validateCon = validateConLF

  alphaEq = alphaEqLF WeakRefl WeakRefl

  evaluate = evaluateLF

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

  freeVar = freeVarLF
  varCensus = varCensusLF
  freeUVars = freeUVarsLF

  kindView = kindViewLF WeakRefl
  typeView = typeViewLF WeakRefl
  termView = termViewLF WeakRefl
  goalView = goalViewLF WeakRefl
  constraintView = constraintViewLF WeakRefl

  withCurrentSolution x = M $ do
    soln <- curSoln <$> get
    let ?soln = Soln soln in (unM x)
  commitSolution (Soln soln) = M $ modify (\s -> s{ curSoln = soln })
  lookupUVar u (Soln soln) = Map.lookup u soln
  assignUVar v m (Soln soln) = return $ Soln $ Map.insert v m soln
  uvarType u = M $ do
    tps <- uvarTypes <$> get
    case Map.lookup u tps of
      Just tp -> return tp
      Nothing -> fail $ unwords ["invalid UVar: ", show u]
  freshUVar tp = M $ do
    s <- get
    let n = uvarNext s
    put s{ uvarNext = n + 1
         , uvarTypes = Map.insert n tp $ uvarTypes s
         }
    return n
  emptySolution = Soln Map.empty
  extendSolution u tm (Soln soln) =
    case Map.lookup u soln of
      Nothing -> Just $ Soln $ Map.insert u tm soln
      Just _  -> Nothing

  solve = solveLF

  getSignature = M $ do
    toList . sigDecls <$> ask

  extendSignature [] m = m
  extendSignature ((a ::. ty) : xs) m = M $ ReaderT $ \sig -> do
    sig' <- lift $ addTypeConstant sig a ty
    runReaderT (unM (extendSignature xs m)) sig'
  extendSignature ((c :. tm) : xs) m = M $ ReaderT $ \sig -> do
    sig' <- lift $ addTermConstant sig c tm
    runReaderT (unM (extendSignature xs m)) sig'

  instantiate = instantiateLF
  abstractUVars = abstractLF

  freshName nm = H.freshName (hypNms ?hyps) nm
  inEmptyCtx x = let ?hyps = emptyTreeHyps in x
  extendCtx nm q a x = let ?hyps = extendTreeHyps ?hyps nm q a in x
  lookupCtx v = H.lookupHyp (hypList ?hyps) v WeakRefl


emptySig :: Signature a c
emptySig = Sig Map.empty Map.empty Seq.empty

data Signature a c
  = Sig
    { sigFamilies :: Map a (LFTree a c E KIND)
    , sigTerms    :: Map c (LFTree a c E TYPE)
    , sigDecls    :: Seq (SigDecl (LFTree a c) Identity)
    }

addTypeConstant :: (Ord a, Ord c, Pretty a, Pretty c)
                => Signature a c
                -> a
                -> M a c (LFTree a c E KIND)
                -> Except String (Signature a c)
addTypeConstant sig nm m =
  case Map.lookup nm (sigFamilies sig) of
    Just _ -> fail $ unwords ["Type constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip evalStateT emptyUVarState $ flip runReaderT sig $ inEmptyCtx $ do
           k <- unM m
           let ?soln = Soln Map.empty
           unM $ validateKind WeakRefl k
           return sig{ sigFamilies = Map.insert nm k (sigFamilies sig)
                     , sigDecls = sigDecls sig |> (nm ::. return k)
                     }

addTermConstant :: (Ord a, Ord c, Pretty a, Pretty c)
                => Signature a c
                -> c
                -> M a c (LFTree a c E TYPE)
                -> Except String (Signature a c)
addTermConstant sig nm m =
  case Map.lookup nm (sigTerms sig) of
    Just _ -> fail $ unwords ["Term constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip evalStateT emptyUVarState $ flip runReaderT sig $ inEmptyCtx $ do
           x <- unM m
           let ?soln = Soln Map.empty
           unM $ validateType WeakRefl x
           return sig{ sigTerms = Map.insert nm x (sigTerms sig)
                     , sigDecls = sigDecls sig |> (nm :. return x)
                     }

runM :: (Ord a, Ord c, Pretty a, Pretty c)
     => [SigDecl (LFTree a c) (M a c)]
     -> ((?soln :: LFSoln (LFTree a c)) => M a c x)
     -> x
runM sig m =
  let ?soln = Soln Map.empty in
  either error id
    $ runExcept
    $ flip evalStateT emptyUVarState
    $ flip runReaderT emptySig
    $ unM
    $ extendSignature sig m

mkTerm :: (Ord a, Ord c, Pretty a, Pretty c)
       => [SigDecl (LFTree a c) (M a c)]
       -> (( ?soln :: LFSoln (LFTree a c)
           , ?hyps :: Hyps (LFTree a c) E
           )
            => M a c (LFTree a c E TERM))
       -> LFTree a c E TERM
mkTerm sig m = runM sig $ inEmptyCtx $ do
    let ?soln = Soln Map.empty
    m' <- m
    _ <- inferType WeakRefl m'
    return m'
