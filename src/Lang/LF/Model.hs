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

{-# OPTIONS_GHC -Werror -W #-}

module Lang.LF.Model
( type SORT
, KIND
, TYPE
, TERM
, LFModel
, Sig(..)
, Ctx
, validateKind
, validateType
, inferType
, checkType
, alphaEq
, headConstant
, LFTree
, typ
, kPi
, tyPi
, tyConst
, tyApp
, lam
, tmConst
, var
, app
) where

import           Control.Monad
import           Control.Monad.Reader
import           Data.Sequence (Seq, (<|) )
import qualified Data.Sequence as Seq
import           Data.Map (Map)
import qualified Data.Map as Map

data SORT
  = KIND    -- ^ Kinds
  | TYPE    -- ^ Type families
  | ATYPE   -- ^ Atomic type families
  | TERM    -- ^ Terms
  | ATERM   -- ^ Atomic terms

type KIND  = 'KIND
type TYPE  = 'TYPE
type ATYPE = 'ATYPE
type TERM  = 'TERM
type ATERM = 'ATERM

-- | The syntax algebra of canonical LF terms, parameterized
--   by the type of subterms `f`, the type `a` of type family
--   constants and the type `c` of term constants.
data LF (f :: SORT -> *) (a :: *) (c :: *) :: SORT -> * where
  Type   :: LF f a c KIND
  KPi    :: f TYPE -> f KIND -> LF f a c KIND

  AType   :: f ATYPE -> LF f a c TYPE
  TyPi    :: f TYPE -> f TYPE -> LF f a c TYPE
  TyConst :: a -> LF f a c ATYPE
  TyApp   :: f ATYPE -> f TERM -> LF f a c ATYPE

  ATerm  :: f ATERM -> LF f a c TERM
  Lam    :: f TYPE -> f TERM -> LF f a c TERM
  Var    :: Int -> LF f a c ATERM
  Const  :: c -> LF f a c ATERM
  App    :: f ATERM -> f TERM -> LF f a c ATERM


typ :: LFModel f a c m => m (f KIND)
typ = foldLF Type

kPi :: LFModel f a c m => f TYPE -> f KIND -> m (f KIND)
kPi a k = foldLF (KPi a k)

tyPi :: LFModel f a c m => f TYPE -> f TYPE-> m (f TYPE)
tyPi a1 a2 = foldLF (TyPi a1 a2)

tyConst :: LFModel f a c m => a -> m (f TYPE)
tyConst x = foldLF . AType =<< foldLF (TyConst x)

tyApp :: LFModel f a c m => f TYPE -> f TERM -> m (f TYPE)
tyApp a m =
  case unfoldLF a of
    AType p -> foldLF . AType =<< foldLF (TyApp p m)
    TyPi _ _ -> fail "Cannot apply terms to Pi Types"

lam :: LFModel f a c m => f TYPE -> f TERM -> m (f TERM)
lam a m = foldLF (Lam a m)

var :: LFModel f a c m => Int -> m (f TERM)
var v = foldLF . ATerm =<< foldLF (Var v)

tmConst :: LFModel f a c m => c -> m (f TERM)
tmConst x = foldLF . ATerm =<< foldLF (Const x)

app :: LFModel f a c m => f TERM -> f TERM -> m (f TERM)
app x y =
  case unfoldLF x of
    ATerm r -> foldLF . ATerm =<<  foldLF (App r y)
    Lam a m -> runChangeT $ hsubst y 0 (simpleType a) m

data SimpleType a
  = SConst a
  | SArrow (SimpleType a) (SimpleType a)

data Sig f a c
  = Sig
    { sigFamilies :: Map a (f KIND)
    , sigTerms    :: Map c (f TYPE)
    }

type Ctx f = Seq (f TYPE)

class (Ord a, Ord c, Monad m) => LFModel (f :: SORT -> *) a c m | f -> a c m where
  unfoldLF :: f s -> LF f a c s
  foldLF :: LF f a c s  -> m (f s)
  constKind :: a -> m (f KIND)
  constType :: c -> m (f TYPE)
  hsubst :: f TERM
         -> Int
         -> SimpleType a
         -> f s
         -> ChangeT m (f s)

  validateKind :: Ctx f -> f KIND -> m ()
  validateType :: Ctx f -> f TYPE  -> m ()
  inferKind :: Ctx f -> f ATYPE -> m (f KIND)
  inferType :: Ctx f -> f TERM -> m (f TYPE)
  inferAType :: Ctx f -> f ATERM -> m (f TYPE)
  alphaEq :: f s -> f s -> m Bool
  headConstant :: f TYPE -> m a

newtype LFTree a c (s::SORT) = LFTree { lfTree :: LF (LFTree a c) a c s }

instance (Show a, Show c, Ord a, Ord c)
    => LFModel (LFTree a c) a c (Reader (Sig (LFTree a c) a c)) where
  unfoldLF = lfTree
  foldLF = return . LFTree
  hsubst = hsubstLM
  validateKind = validateKindLF
  validateType = validateTypeLF
  inferKind = inferKindLF
  inferType = inferTypeLF
  inferAType = inferATypeLF
  alphaEq = alphaEqLF
  headConstant = headConstantLF
  constKind a = do
     sig <- ask
     case Map.lookup a (sigFamilies sig) of
       Nothing -> fail $ unwords ["type family lookup failed:", show a]
       Just x  -> return x
  constType c = do
     sig <- ask
     case Map.lookup c (sigTerms sig) of
       Nothing -> fail $ unwords ["term constant lookup failed:", show c]
       Just x  -> return x

data ChangeT m a
  = Unchanged a
  | Changed (m a)

instance Functor m => Functor (ChangeT m) where
  fmap f (Unchanged a) = Unchanged (f a)
  fmap f (Changed x) = Changed (fmap f x)

instance Applicative m => Applicative (ChangeT m) where
  pure = Unchanged
  (Unchanged f) <*> (Unchanged x) = Unchanged (f x)
  (Unchanged f) <*> (Changed x)   = Changed (pure f <*> x)
  (Changed f)   <*> (Unchanged x) = Changed (f <*> pure x)
  (Changed f)   <*> (Changed x)   = Changed (f <*> x)

instance Monad m => Monad (ChangeT m) where
  return = Unchanged
  Unchanged x >>= f = f x
  Changed x  >>= f  = Changed (join (fmap (g . f) x))
    where g (Unchanged q) = return q
          g (Changed q) = q

runChangeT :: Monad m => ChangeT m a -> m a
runChangeT (Unchanged x) = return x
runChangeT (Changed x)   = x

mapChange :: Monad m => (a -> b) -> (a -> m b) -> ChangeT m a -> ChangeT m b
mapChange f _ (Unchanged x) = Unchanged (f x)
mapChange _ g (Changed y)   = Changed (g =<< y)

onChange :: Monad m => b -> (a -> m b) -> ChangeT m a -> ChangeT m b
onChange x = mapChange (const x)

checkType :: LFModel f a c m
          => Ctx f
          -> f TERM
          -> f TYPE
          -> m ()
checkType ctx m a = do
  a' <- inferType ctx m
  q  <- alphaEq a a'
  if q then return ()
       else fail "infered type did not match expected type"

headConstantLF :: forall f a c m
                . LFModel f a c m
               => f TYPE
               -> m a
headConstantLF a =
  case unfoldLF a of
    AType p  -> f p
    TyPi _ a -> headConstant a
 where f :: f ATYPE -> m a
       f p =
         case unfoldLF p of
           TyConst a -> return a
           TyApp p _ -> f p

alphaEqLF :: LFModel f a c m
          => f s
          -> f s
          -> m Bool
alphaEqLF x y =
  case (unfoldLF x, unfoldLF y) of
    (Type      , Type)         -> return True
    (KPi a k   , KPi a' k')    -> (&&) <$> alphaEq a a' <*> alphaEq k k'
    (AType x   , AType x')     -> alphaEq x x'
    (TyPi a1 a2, TyPi a1' a2') -> (&&) <$> alphaEq a1 a1' <*> alphaEq a2 a2'
    (TyConst x , TyConst x')   -> return $ x == x'
    (TyApp a m , TyApp a' m')  -> (&&) <$> alphaEq a a' <*> alphaEq m m'
    (ATerm x   , ATerm x')     -> alphaEq x x'
    (Lam a m   , Lam a' m')    -> (&&) <$> alphaEq a a' <*> alphaEq m m'
    (Var v     , Var v')       -> return $ v == v'
    (Const x   , Const x')     -> return $ x == x'
    (App r m   , App r' m')    -> (&&) <$> alphaEq r r' <*> alphaEq m m'
    _ -> return False

validateKindLF :: LFModel f a c m
               => Ctx f
               -> f KIND
               -> m ()
validateKindLF ctx tm =
  case unfoldLF tm of
    Type -> return ()
    KPi a k -> do
      validateType ctx a
      validateKind (a <| ctx) k
      {- subordination check -}

validateTypeLF :: LFModel f a c m
               => Ctx f
               -> f TYPE
               -> m ()
validateTypeLF ctx tm =
  case unfoldLF tm of
    TyPi a1 a2 -> do
      validateType ctx a1
      validateType (a1 <| ctx) a2

    AType p -> do
      k <- inferKind ctx p
      case unfoldLF k of
        Type -> return ()
        _ -> fail "invalid atomic type"

inferKindLF :: LFModel f a c m
            => Ctx f
            -> f ATYPE
            -> m (f KIND)
inferKindLF ctx tm =
  case unfoldLF tm of
    TyConst x -> constKind x
    TyApp p1 m2 -> do
      k1 <- inferKind ctx p1
      case unfoldLF k1 of
        KPi a2 k1 -> do
          checkType ctx m2 a2
          runChangeT $ hsubst m2 0 (simpleType a2) k1
        _ -> fail "invalid atomic type family"


inferTypeLF :: LFModel f a c m
            => Ctx f
            -> f TERM
            -> m (f TYPE)
inferTypeLF ctx m =
  case unfoldLF m of
    ATerm r -> inferAType ctx r
    Lam a2 m -> do
      a1 <- inferType (a2 <| ctx) m
      foldLF (TyPi a2 a1)

inferATypeLF :: LFModel f a c m
            => Ctx f
            -> f ATERM
            -> m (f TYPE)
inferATypeLF ctx r =
  case unfoldLF r of
    Var i | i < Seq.length ctx -> return $ Seq.index ctx i 
          | otherwise -> fail "Variable out of scope"
    Const c -> constType c
    App r1 m2 -> do
      a <- inferAType ctx r1
      case unfoldLF a of
        TyPi a2 a1 -> do
          checkType ctx m2 a2
          runChangeT $ hsubst m2 0 (simpleType a2) a1
        _ -> fail "Expected function type"

simpleType :: LFModel f a c m
         => f TYPE
         -> SimpleType a
simpleType tm =
  case unfoldLF tm of
    AType f -> simpleAType f
    TyPi a1 a2 -> SArrow (simpleType a1) (simpleType a2)

simpleAType :: LFModel f a c m
         => f ATYPE
         -> SimpleType a
simpleAType tm =
  case unfoldLF tm of
    TyConst x -> SConst x
    TyApp p _ -> simpleAType p


hsubstLM :: forall f a c m s
          . LFModel f a c m
         => f TERM
         -> Int
         -> SimpleType a
         -> f s
         -> ChangeT m (f s)
hsubstLM tm0 v0 st0 = \tm ->
  case unfoldLF tm of
    Type      -> Unchanged tm
    KPi a k   -> onChange tm foldLF (KPi <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 k)

    AType x   -> onChange tm foldLF (AType <$> hsubst tm0 v0 st0 x)
    TyPi a a' -> onChange tm foldLF (TyPi <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 a')

    TyConst _ -> Unchanged tm
    TyApp p m -> onChange tm foldLF (TyApp <$> hsubst tm0 v0 st0 p <*> hsubst tm0 v0 st0 m)

    Lam a m   -> onChange tm foldLF (Lam <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 m)
    ATerm x   -> onChange tm (either (return . fst) (foldLF . ATerm)) (hsubstTm x st0)

    Const _ -> atermErr
    Var _   -> atermErr
    App _ _ -> atermErr

 where atermErr :: forall x. ChangeT m x
       atermErr = fail "Do not call hsubst directly on terms of sort ATERM"

       hsubstTm :: f ATERM
                -> SimpleType a
                -> ChangeT m (Either (f TERM, SimpleType a) (f ATERM))

       hsubstTm tm st =
         case unfoldLF tm of
           Var v
             | v0 == v   -> Changed (return $ Left (tm0, st))
             | v0 <  v   -> Changed (Right <$> (foldLF $! Var $! v-1))
             | otherwise -> Unchanged (Right tm)
           Const _       -> Unchanged (Right tm)
           App r1 m2 ->
             case hsubstTm r1 st of
               Unchanged _ ->
                 onChange (Right tm) (\m -> Right <$> foldLF (App r1 m)) (hsubst tm0 v0 st m2)
               m -> do
                 m2' <- hsubst tm0 v0 st m2
                 m >>= \case
                   Left (unfoldLF -> Lam _ m1', SArrow stArg stBody) -> do
                     m' <- hsubst m2' 0 stArg m1'
                     Changed (return $ Left (m', stBody))
                   Right r1' ->
                     Changed (Right <$> foldLF (App r1' m2'))
                   _ ->
                     fail "hereditary substitution failed: ill-typed term"
