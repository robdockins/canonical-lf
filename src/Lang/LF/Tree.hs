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
)
where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Model

newtype LFTree a c (s::SORT) = LFTree { lfTree :: LF (LFTree a c) a c s }

type M a c = ReaderT (Signature a c) (Except String)

instance (Pretty a, Pretty c, Ord a, Ord c)
    => LFModel (LFTree a c) a c (M a c) where
  unfoldLF = lfTree
  foldLF = return . LFTree
  hsubst = hsubstLM
  validateKind = validateKindLF
  validateType = validateTypeLF
  inferKind = inferKindLF
  inferType = inferTypeLF
  inferAType = inferATypeLF
  alphaEq = alphaEqLF
  weaken = weakenLF
  freeVar = freeVarLF
  ppLF usedNames nameScope x = do
     return $ prettyLF usedNames nameScope TopPrec x

  headConstant = headConstantLF
  constKind a = do
     sig <- ask
     case Map.lookup a (sigFamilies sig) of
       Nothing -> fail $ unwords ["type family lookup failed:", show (pretty a)]
       Just x  -> return x
  constType c = do
     sig <- ask
     case Map.lookup c (sigTerms sig) of
       Nothing -> fail $ unwords ["term constant lookup failed:", show (pretty c)]
       Just x  -> return x


data SigDecl a c
  = TypeDecl a (M a c (LFTree a c KIND))
  | TermDecl c (M a c (LFTree a c TYPE))

emptySig :: Signature a c
emptySig = Sig Map.empty Map.empty

data Signature a c
  = Sig
    { sigFamilies :: Map a (LFTree a c KIND)
    , sigTerms    :: Map c (LFTree a c TYPE)
    }

addTypeConstant :: (Ord a, Ord c, Pretty a, Pretty c)
                => Signature a c
                -> a
                -> M a c (LFTree a c KIND)
                -> Except String (Signature a c)
addTypeConstant sig nm m =
  case Map.lookup nm (sigFamilies sig) of
    Just _ -> fail $ unwords ["Type constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip runReaderT sig $ do
           k <- m
           validateKind Seq.empty k
           return sig{ sigFamilies = Map.insert nm k (sigFamilies sig) }

addTermConstant :: (Ord a, Ord c, Pretty a, Pretty c)
                => Signature a c
                -> c
                -> M a c (LFTree a c TYPE)
                -> Except String (Signature a c)
addTermConstant sig nm m =
  case Map.lookup nm (sigTerms sig) of
    Just _ -> fail $ unwords ["Term constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip runReaderT sig $ do
           x <- m
           validateType Seq.empty x
           return sig{ sigTerms = Map.insert nm x (sigTerms sig) }

buildSignature :: (Ord a, Ord c, Pretty a, Pretty c)
               => [SigDecl a c]
               -> Signature a c
buildSignature = either error id . runExcept . foldM f emptySig 
 where f sig (TypeDecl a x) = addTypeConstant sig a x
       f sig (TermDecl c x) = addTermConstant sig c x

runM :: Signature a c -> M a c x -> x
runM sig = either error id . runExcept . flip runReaderT sig
