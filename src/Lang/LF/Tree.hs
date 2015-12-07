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
--import qualified Data.Foldable as Fold
import           Data.Map (Map)
import qualified Data.Map as Map
--import           Data.Set (Set)
--import qualified Data.Set as Set
--import           Data.Sequence (Seq, (|>))
--import qualified Data.Sequence as Seq

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Model
--import Lang.LF.ChangeT

newtype LFTree a c γ (s::SORT) =
  LFTree { lfTree :: LF (LFTree a c) γ s
         }

type instance LFTypeConst (LFTree a c) = a
type instance LFConst (LFTree a c) = c

type M a c = ReaderT (Signature a c) (Except String)

instance (Pretty a, Pretty c, Ord a, Ord c)
    => LFModel (LFTree a c) (M a c) where
  unfoldLF = lfTree
  foldLF = return . LFTree
  hsubst = hsubstLF
  weaken = LFTree . Weak
  ppLF = prettyLF
  validateKind = validateKindLF


{-
  validateType = validateTypeLF
  inferKind = inferKindLF
  inferType = inferTypeLF
  inferAType = inferATypeLF
  alphaEq = alphaEqLF
  weaken = weakenLF
  freeVar = freeVarLF
  ppLF = prettyLF
  headConstant = headConstantLF
  dumpContext = dumpContextLF
  contextDepth = do
     (_,ctx,_) <- ask
     return $ Seq.length ctx
  kindView = kindViewLF
  typeView = typeViewLF
  termView = termViewLF
  underLambda tm action =
    case unfoldLF tm of
      Lam nm a m -> do
        case action m of
          Changed m' -> Changed (foldLF . Lam nm a =<< extendContext nm QLam a m')
          _ -> Unchanged tm

      _ -> fail "Expected a lambda term"

  extendContext nm qnt a action =
     withReaderT (\(nms,ctx,sig) -> (Set.insert nm nms, ctx |> (nm,qnt,a), sig))
                 action
  freshName nm = do
     (nms,_,_) <- ask
     return $ getName nms nm
  lookupVariable (LFVar v) = do
     (_,ctx,_) <- ask
     let d = Seq.length ctx
     if 0 <= v && v < d then
       let (_,_,a) = Seq.index ctx v in
       let j = d - v in
       runChangeT $ weaken 0 j a
     else
       fail $ unwords ["Variable out of scope (lookup):", show v]
  lookupVariableName (LFVar v) = do
     (_,ctx,_) <- ask
     let d = Seq.length ctx
     if 0 <= v && v < d then
       let (nm,_,_) = Seq.index ctx v in
       return nm
     else
       fail $ unwords ["Variable out of scope (lookup name):", show v]
  constKind a = do
     (_,_,sig) <- ask
     case Map.lookup a (sigFamilies sig) of
       Nothing -> fail $ unwords ["type family lookup failed:", show (pretty a)]
       Just x  -> return x
  constType c = do
     (_,_,sig) <- ask
     case Map.lookup c (sigTerms sig) of
       Nothing -> fail $ unwords ["term constant lookup failed:", show (pretty c)]
       Just x  -> return x

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
  = a ::. (M a c (LFTree a c E KIND))
  | c :. (M a c (LFTree a c E TYPE))

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
    Nothing -> flip runReaderT sig $ do
           k <- m
           -- validateKind k
           return sig{ sigFamilies = Map.insert nm k (sigFamilies sig) }

addTermConstant :: (Ord a, Ord c, Pretty a, Pretty c)
                => Signature a c
                -> c
                -> M a c (LFTree a c E TYPE)
                -> Except String (Signature a c)
addTermConstant sig nm m =
  case Map.lookup nm (sigTerms sig) of
    Just _ -> fail $ unwords ["Term constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip runReaderT sig $ do
           x <- m
           -- validateType x
           return sig{ sigTerms = Map.insert nm x (sigTerms sig) }

buildSignature :: (Ord a, Ord c, Pretty a, Pretty c)
               => [SigDecl a c]
               -> Signature a c
buildSignature = either error id . runExcept . foldM f emptySig
 where f sig (a ::. x) = addTypeConstant sig a x
       f sig (c :. x)  = addTermConstant sig c x

runM :: Signature a c -> M a c x -> x
runM sig = either error id . runExcept . flip runReaderT sig

mkTerm :: (Ord a, Ord c, Pretty a, Pretty c)
       => Signature a c -> M a c (LFTree a c E TERM) -> LFTree a c E TERM
mkTerm sig m = runM sig $ do
    m' <- m
    -- _ <- inferType m'
    return m'
