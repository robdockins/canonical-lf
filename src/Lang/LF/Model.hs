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

module Lang.LF.Model
( type Sort
, KIND
, FAM
, TERM
, LFModel
, validateKind
, validateType
, inferType
, checkType
, alphaEq
, headConstant
, LFTree
) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader
import           Data.Sequence (Seq, (<|) )
import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Map (Map)
import qualified Data.Map as Map

data Sort
  = KIND    -- ^ Kinds
  | FAM     -- ^ Type families
  | AFAM    -- ^ Atomic type families
  | TERM    -- ^ Terms
  | ATERM   -- ^ Atomic terms

type KIND = 'KIND
type FAM  = 'FAM
type AFAM = 'AFAM
type TERM = 'TERM
type ATERM = 'ATERM

-- | The syntax algebra of canonical LF terms, parameterized
--   by the type of subterms `f`, the type `a` of type family
--   constants and the type `c` of term constants.
data LF (f :: Sort -> *) (a :: *) (c :: *) :: Sort -> * where
  Type   :: LF f a c KIND
  KPi    :: f FAM -> f KIND -> LF f a c KIND

  AFam   :: f AFAM -> LF f a c FAM
  FPi    :: f FAM -> f FAM -> LF f a c FAM
  FConst :: a -> LF f a c AFAM
  FApp   :: f AFAM -> f TERM -> LF f a c AFAM

  ATerm  :: f ATERM -> LF f a c TERM
  TLam   :: f FAM -> f TERM -> LF f a c TERM
  TVar   :: Int -> LF f a c ATERM
  TConst :: c -> LF f a c ATERM
  TApp   :: f ATERM -> f TERM -> LF f a c ATERM

typ :: LFModel f a c m => m (f KIND)
typ = foldLF Type

kPi :: LFModel f a c m => f FAM -> f KIND -> m (f KIND)
kPi a k = foldLF (KPi a k)

fPi :: LFModel f a c m => f FAM -> f FAM -> m (f FAM)
fPi a1 a2 = foldLF (FPi a1 a2)

fConst :: LFModel f a c m => a -> m (f FAM)
fConst x = foldLF . AFam =<< foldLF (FConst x)

fApp :: LFModel f a c m => f FAM -> f TERM -> m (f FAM)
fApp a m =
  case unfoldLF a of
    AFam p -> foldLF . AFam =<< foldLF (FApp p m)
    FPi _ _ -> fail "Cannot apply terms to Pi Types"

tLam :: LFModel f a c m => f FAM -> f TERM -> m (f TERM)
tLam a m = foldLF (TLam a m)

tVar :: LFModel f a c m => Int -> m (f TERM)
tVar v = foldLF . ATerm =<< foldLF (TVar v)

tConst :: LFModel f a c m => c -> m (f TERM)
tConst x = foldLF . ATerm =<< foldLF (TConst x)

tApp :: LFModel f a c m => f TERM -> f TERM -> m (f TERM)
tApp x y =
  case unfoldLF x of
    ATerm r  -> foldLF . ATerm =<<  foldLF (TApp r y)
    TLam a m -> runChangeT $ hsubst y 0 (simpleType a) y



data SimpleType a
  = SConst a
  | SArrow (SimpleType a) (SimpleType a)

data Sig f a c
  = Sig
    { sigFamilies :: Map a (f KIND)
    , sigTerms    :: Map c (f FAM)
    }

type Ctx f = Seq (f FAM)

class (Ord a, Ord c, Monad m) => LFModel (f :: Sort -> *) a c m | f -> a c m where
  unfoldLF :: f s -> LF f a c s
  foldLF :: LF f a c s  -> m (f s)
  constKind :: a -> m (f KIND)
  constType :: c -> m (f FAM)
  hsubst :: f TERM
         -> Int
         -> SimpleType a
         -> f s
         -> ChangeT m (f s)

  validateKind :: Ctx f -> f KIND -> m ()
  validateType :: Ctx f -> f FAM  -> m ()
  inferKind :: Ctx f -> f AFAM -> m (f KIND)
  inferType :: Ctx f -> f TERM -> m (f FAM)
  inferAType :: Ctx f -> f ATERM -> m (f FAM)
  alphaEq :: f s -> f s -> m Bool
  headConstant :: f FAM -> m a

newtype LFTree a c (s::Sort) = LFTree { lfTree :: LF (LFTree a c) a c s }

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
          -> f FAM
          -> m ()
checkType ctx m a = do
  a' <- inferType ctx m
  q  <- alphaEq a a'
  if q then return ()
       else fail "infered type did not match expected type"

headConstantLF :: forall f a c m
                . LFModel f a c m
               => f FAM
               -> m a
headConstantLF a =
  case unfoldLF a of
    AFam p  -> f p
    FPi _ a -> headConstant a
 where f :: f AFAM -> m a
       f p =
         case unfoldLF p of
           FConst a -> return a
           FApp p _ -> f p

alphaEqLF :: LFModel f a c m
          => f s
          -> f s
          -> m Bool
alphaEqLF x y =
  case (unfoldLF x, unfoldLF y) of
    (Type     , Type) -> return True
    (KPi a k  , KPi a' k') -> (&&) <$> alphaEq a a' <*> alphaEq k k'
    (AFam x   , AFam x' ) -> alphaEq x x'
    (FPi a1 a2, FPi a1' a2') -> (&&) <$> alphaEq a1 a1' <*> alphaEq a2 a2'
    (FConst x , FConst x') -> return $ x == x'
    (FApp a m , FApp a' m') -> (&&) <$> alphaEq a a' <*> alphaEq m m'
    (ATerm x  , ATerm x')   -> alphaEq x x'
    (TLam a m , TLam a' m') -> (&&) <$> alphaEq a a' <*> alphaEq m m'
    (TVar v   , TVar v')    -> return $ v == v'
    (TConst x , TConst x')  -> return $ x == x'
    (TApp r m , TApp r' m') -> (&&) <$> alphaEq r r' <*> alphaEq m m'
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
               -> f FAM
               -> m ()
validateTypeLF ctx tm =
  case unfoldLF tm of
    FPi a1 a2 -> do
      validateType ctx a1
      validateType (a1 <| ctx) a2

    AFam p -> do
      k <- inferKind ctx p
      case unfoldLF k of
        Type -> return ()
        _ -> fail "invalid atomic type"

inferKindLF :: LFModel f a c m
            => Ctx f
            -> f AFAM
            -> m (f KIND)
inferKindLF ctx tm =
  case unfoldLF tm of
    FConst x -> constKind x
    FApp p1 m2 -> do
      k1 <- inferKind ctx p1
      case unfoldLF k1 of
        KPi a2 k1 -> do
          checkType ctx m2 a2
          runChangeT $ hsubst m2 0 (simpleType a2) k1
        _ -> fail "invalid atomic type family"


inferTypeLF :: LFModel f a c m
            => Ctx f
            -> f TERM
            -> m (f FAM)
inferTypeLF ctx m =
  case unfoldLF m of
    ATerm r -> inferAType ctx r
    TLam a2 m -> do
      a1 <- inferType (a2 <| ctx) m
      foldLF (FPi a2 a1)

inferATypeLF :: LFModel f a c m
            => Ctx f
            -> f ATERM
            -> m (f FAM)
inferATypeLF ctx r =
  case unfoldLF r of
    TVar i | i < Seq.length ctx -> return $ Seq.index ctx i 
           | otherwise -> fail "Variable out of scope"
    TConst c -> constType c
    TApp r1 m2 -> do
      a <- inferAType ctx r1
      case unfoldLF a of
        FPi a2 a1 -> do
          checkType ctx m2 a2
          runChangeT $ hsubst m2 0 (simpleType a2) a1
        _ -> fail "Expected function type"

simpleType :: LFModel f a c m
         => f FAM
         -> SimpleType a
simpleType tm =
  case unfoldLF tm of
    AFam f -> simpleAType f
    FPi a1 a2 -> SArrow (simpleType a1) (simpleType a2)

simpleAType :: LFModel f a c m
         => f AFAM
         -> SimpleType a
simpleAType tm =
  case unfoldLF tm of
    FConst x -> SConst x
    FApp p _ -> simpleAType p


hsubstLM :: forall f a c m s
          . LFModel f a c m
         => f TERM
         -> Int
         -> SimpleType a
         -> f s
         -> ChangeT m (f s)
hsubstLM tm0 v0 st0 = \tm ->
  case unfoldLF tm of
    Type     -> Unchanged tm
    KPi a k  -> onChange tm foldLF (KPi <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 k)
    AFam x   -> onChange tm foldLF (AFam <$> hsubst tm0 v0 st0 x)
    FPi a a' -> onChange tm foldLF  (FPi <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 a')
    FConst _ -> Unchanged tm
    FApp p m -> onChange tm foldLF (FApp <$> hsubst tm0 v0 st0 p <*> hsubst tm0 v0 st0 m)
    TLam a m -> onChange tm foldLF (TLam <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 m)
    ATerm x  -> onChange tm (either (return . fst) (foldLF . ATerm)) (hsubstTm x st0)

 where hsubstTm :: f ATERM
                -> SimpleType a
                -> ChangeT m (Either (f TERM, SimpleType a) (f ATERM))

       hsubstTm tm st =
         case unfoldLF tm of
           TVar v
             | v0 == v   -> Changed (return $ Left (tm0, st))
             | v0 <  v   -> Changed (Right <$> (foldLF $! TVar $! v-1))
             | otherwise -> Unchanged (Right tm)
           TConst _      -> Unchanged (Right tm)
           TApp r1 m2 ->
             case hsubstTm r1 st of
               Unchanged _ ->
                 onChange (Right tm) (\m -> Right <$> foldLF (TApp r1 m)) (hsubst tm0 v0 st m2)
               m -> do
                 m2' <- hsubst tm0 v0 st m2
                 m >>= \case
                   Left (unfoldLF -> TLam _ m1', SArrow stArg stBody) -> do
                     m' <- hsubst m2' 0 stArg m1'
                     Changed (return $ Left (m', stBody))
                   Right r1' ->
                     Changed (Right <$> foldLF (TApp r1' m2'))
                   _ ->
                     fail "hereditary substitution failed: ill-typed term"
