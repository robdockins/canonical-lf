{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lang.LF.Tree
( LFTree
, Signature(..)
, SigDecl(..)
, runM
, buildSignature
, emptySig
, M
, mkTerm
)
where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
--import qualified Data.Foldable as Fold
import           Data.Map (Map)
import qualified Data.Map as Map
--import           Data.Set (Set)
import qualified Data.Set as Set
--import           Data.Sequence (Seq, (|>))
--import qualified Data.Sequence as Seq

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Model
import Lang.LF.Internal.Print
import Lang.LF.Internal.Solve
import Lang.LF.Internal.Subst
import Lang.LF.Internal.Typecheck
import Lang.LF.Internal.View

--import Lang.LF.ChangeT

newtype LFTree a c γ (s::SORT) =
  LFTree { lfTree :: LF (LFTree a c) γ s
         }

instance (Pretty a, Pretty c, Ord a, Ord c) => Show (LFTree a c E s) where
  show x =
    runM emptySig (inEmptyCtx (let ?soln = Map.empty in displayLF x))

type Soln a c = Map Integer (LFTree a c E TERM)

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
type instance LFSoln (LFTree a c) = Soln a c

newtype M a c x = M { unM :: ReaderT (Signature a c) (StateT (UVarState a c) (Except String)) x }

deriving instance Functor (M a c)
deriving instance Applicative (M a c)
deriving instance Monad (M a c)

instance (Pretty a, Pretty c, Ord a, Ord c)
    => LFModel (LFTree a c) (M a c) where
  unfoldLF = lfTree
  foldLF = return . LFTree
  hsubst = hsubstLF
  weaken = LFTree . Weak
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

  alphaEq = alphaEqLF id id

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

  kindView = kindViewLF WeakRefl 
  typeView = typeViewLF WeakRefl
  termView = termViewLF WeakRefl id
  goalView = goalViewLF WeakRefl
  constraintView = constraintViewLF WeakRefl

  withCurrentSolution x = M $ do
    soln <- curSoln <$> get
    let ?soln = soln in (unM x)
  commitSolution soln = M $ modify (\s -> s{ curSoln = soln })
  lookupUVar _ = Map.lookup 
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
  extendSolution u tm soln = M $ do
    case Map.lookup u soln of
      Nothing -> return $ Just $ Map.insert u tm soln
      Just _  -> return $ Nothing

  solve = solveLF

  instantiate = instantiateLF

{-
dumpContextLF :: (Ord a, Ord c, Pretty a, Pretty c) => M a c Doc
dumpContextLF = do
   (_,ctx,_) <- ask
   binds <- mapM dumpBind $ Fold.toList ctx
   return $ vcat $ binds
 where dumpBind (nm,q,a) = do
           adoc <- ppLF TopPrec a
           return $ dumpq q <> text nm <+> text ":" <+> adoc
       dumpq QPi  = text "Π"
       dumpq QLam = text "λ"
       dumpq QForall = text "∀"
       dumpq QExists = text "∃"
       dumpq QSigma = text "Σ"
-}

infixr 0 ::.
infixr 0 :.

data SigDecl a c
  = a ::. M a c (LFTree a c E KIND)
  | c :.  M a c (LFTree a c E TYPE)

emptySig :: Signature a c
emptySig = Sig Map.empty Map.empty

data Signature a c
  = Sig
    { sigFamilies :: Map a (LFTree a c E KIND)
    , sigTerms    :: Map c (LFTree a c E TYPE)
    }

addTypeConstant :: (Ord a, Ord c, Pretty a, Pretty c)
                => Signature a c
                -> a
                -> M a c (LFTree a c E KIND)
                -> Except String (Signature a c)
addTypeConstant sig nm m =
  case Map.lookup nm (sigFamilies sig) of
    Just _ -> fail $ unwords ["Type constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip evalStateT emptyUVarState $ flip runReaderT sig $ do
           k <- unM m
           let ?nms = Set.empty
           let ?hyps = HNil
           let ?soln = Map.empty
           unM $ validateKind k
           return sig{ sigFamilies = Map.insert nm k (sigFamilies sig) }

addTermConstant :: (Ord a, Ord c, Pretty a, Pretty c)
                => Signature a c
                -> c
                -> M a c (LFTree a c E TYPE)
                -> Except String (Signature a c)
addTermConstant sig nm m =
  case Map.lookup nm (sigTerms sig) of
    Just _ -> fail $ unwords ["Term constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip evalStateT emptyUVarState $ flip runReaderT sig $ do
           x <- unM m
           let ?nms = Set.empty
           let ?hyps = HNil
           let ?soln = Map.empty
           unM $ validateType x
           return sig{ sigTerms = Map.insert nm x (sigTerms sig) }

buildSignature :: (Ord a, Ord c, Pretty a, Pretty c)
               => ((?hyps :: Hyps (LFTree a c) E, ?nms :: Set.Set String)
                    => [SigDecl a c])
               -> Signature a c
buildSignature decls =
   either error id $ runExcept $ foldM f emptySig $ inEmptyCtx decls
 where f sig (a ::. x) = addTypeConstant sig a x
       f sig (c :. x)  = addTermConstant sig c x

runM :: Signature a c
     -> ((?soln :: LFSoln (LFTree a c)) => M a c x)
     -> x
runM sig m =
  let ?soln = Map.empty in
  either error id $ runExcept $ flip evalStateT emptyUVarState $ flip runReaderT sig $ unM m

mkTerm :: (Ord a, Ord c, Pretty a, Pretty c)
       => Signature a c
       -> (( ?soln :: LFSoln (LFTree a c)
           , ?hyps :: Hyps (LFTree a c) E
           , ?nms  :: Set.Set String
           )
            => M a c (LFTree a c E TERM))
       -> LFTree a c E TERM
mkTerm sig m = runM sig $ inEmptyCtx $ do
    let ?nms = Set.empty
    let ?hyps = HNil
    let ?soln = Map.empty
    m' <- m
    _ <- inferType m'
    return m'
