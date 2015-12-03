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
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Sequence (Seq, (<|))
import qualified Data.Sequence as Seq

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Model
import Lang.LF.ChangeT

newtype LFTree a c (s::SORT) = LFTree { lfTree :: LF (LFTree a c) a c s }

type M a c = ReaderT (Set String, Seq (String, Quant, LFTree a c TYPE), Signature a c) (Except String)

getName :: Set String
        -> String
        -> String
getName ss nm = tryName ss (nm : [ nm++show i | i <- [0..] ])
 where
  tryName ss (x:xs)
    | Set.member x ss = tryName ss xs
    | otherwise = x
  tryName _ [] = undefined

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
  ppLF = prettyLF
  headConstant = headConstantLF
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
     withReaderT (\(nms,ctx,sig) -> (Set.insert nm nms, (nm,qnt,a) <| ctx, sig))
                 action
  freshName nm = do
     (nms,_,_) <- ask
     return $ getName nms nm
  lookupVariable (LFVar i) = do
     (_,ctx,_) <- ask
     if i < Seq.length ctx then
       let (_,_,a) = Seq.index ctx i in
       runChangeT $ weaken 0 (i+1) a
     else
       fail $ unwords ["Variable out of scope:", show i]
  lookupVariableName (LFVar i) = do
     (_,ctx,_) <- ask
     if i < Seq.length ctx then
       let (nm,_,_) = Seq.index ctx i in
       return nm
     else
       fail $ unwords ["Variable out of scope:", show i]
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

infixr 0 ::.
infixr 0 :.

data SigDecl a c
  = a ::. (M a c (LFTree a c KIND))
  | c :. (M a c (LFTree a c TYPE))

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
    Nothing -> flip runReaderT (Set.empty, Seq.empty, sig) $ do
           k <- m
           validateKind k
           return sig{ sigFamilies = Map.insert nm k (sigFamilies sig) }

addTermConstant :: (Ord a, Ord c, Pretty a, Pretty c)
                => Signature a c
                -> c
                -> M a c (LFTree a c TYPE)
                -> Except String (Signature a c)
addTermConstant sig nm m =
  case Map.lookup nm (sigTerms sig) of
    Just _ -> fail $ unwords ["Term constant",show (pretty nm),"declared multiple times"]
    Nothing -> flip runReaderT (Set.empty, Seq.empty, sig) $ do
           x <- m
           validateType x
           return sig{ sigTerms = Map.insert nm x (sigTerms sig) }

buildSignature :: (Ord a, Ord c, Pretty a, Pretty c)
               => [SigDecl a c]
               -> Signature a c
buildSignature = either error id . runExcept . foldM f emptySig
 where f sig (a ::. x) = addTypeConstant sig a x
       f sig (c :. x) = addTermConstant sig c x

runM :: Signature a c -> M a c x -> x
runM sig = either error id . runExcept . flip runReaderT (Set.empty, Seq.empty, sig)

mkTerm :: (Ord a, Ord c, Pretty a, Pretty c)
       => Signature a c -> M a c (LFTree a c TERM) -> LFTree a c TERM
mkTerm sig m = runM sig $ do
    m' <- m
    _ <- inferType m'
    return m'
