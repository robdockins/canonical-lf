module Lang.LF.Model where

import           Data.Sequence (Seq, (<|) )
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF.ChangeT

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
  KPi    :: String -> f TYPE -> f KIND -> LF f a c KIND

  AType   :: f ATYPE -> LF f a c TYPE
  TyPi    :: String -> f TYPE -> f TYPE -> LF f a c TYPE
  TyConst :: a -> LF f a c ATYPE
  TyApp   :: f ATYPE -> f TERM -> LF f a c ATYPE

  ATerm  :: f ATERM -> LF f a c TERM
  Lam    :: String -> f TYPE -> f TERM -> LF f a c TERM
  Var    :: Int -> LF f a c ATERM
  Const  :: c -> LF f a c ATERM
  App    :: f ATERM -> f TERM -> LF f a c ATERM

data SimpleType a
  = SConst a
  | SArrow (SimpleType a) (SimpleType a)

type Ctx f = Seq (f TYPE)

class (Ord a, Ord c, Pretty a, Pretty c, Monad m) => LFModel (f :: SORT -> *) a c m | f -> a c m where
  unfoldLF :: f s -> LF f a c s
  foldLF :: LF f a c s  -> m (f s)
  constKind :: a -> m (f KIND)
  constType :: c -> m (f TYPE)
  hsubst :: f TERM
         -> Int
         -> SimpleType a
         -> f s
         -> ChangeT m (f s)

  ppLF :: Set String -> Seq Doc -> f s -> m Doc
  validateKind :: Ctx f -> f KIND -> m ()
  validateType :: Ctx f -> f TYPE -> m ()
  inferKind :: Ctx f -> f ATYPE -> m (f KIND)
  inferType :: Ctx f -> f TERM -> m (f TYPE)
  inferAType :: Ctx f -> f ATERM -> m (f TYPE)
  alphaEq :: f s -> f s -> m Bool
  headConstant :: f TYPE -> m a
  weaken :: Int -> Int -> f s -> ChangeT m (f s)
  freeVar :: Int -> f s -> Bool

typ :: LFModel f a c m => m (f KIND)
typ = foldLF Type

kPi :: LFModel f a c m => String -> m (f TYPE) -> m (f KIND) -> m (f KIND)
kPi nm a k = foldLF =<< (KPi nm <$> a <*> k)

tyPi :: LFModel f a c m => String -> m (f TYPE) -> m (f TYPE) -> m (f TYPE)
tyPi nm a1 a2 = foldLF =<< (TyPi nm <$> a1 <*> a2)

infixr 5 ==>
(==>) :: LFModel f a c m => m (f TYPE) -> m (f TYPE) -> m (f TYPE)
(==>) = tyArrow

infixl 2 @@

class LFApplication (s::SORT) where
  (@@) :: LFModel f a c m => m (f s) -> m (f TERM) -> m (f s)

instance LFApplication TYPE where
  (@@) = tyApp
instance LFApplication TERM where
  (@@) = app

tyArrow :: LFModel f a c m => m (f TYPE) -> m (f TYPE) -> m (f TYPE)
tyArrow a1 a2 = do
   a1' <- a1
   a2' <- a2
   a2'' <- runChangeT $ weaken 0 1 a2'
   foldLF (TyPi "_" a1' a2'')

kArrow :: LFModel f a c m => m (f TYPE) -> m (f KIND) -> m (f KIND)
kArrow a k = do
   a' <- a
   k' <- k
   k'' <- runChangeT $ weaken 0 1 k'
   foldLF (KPi "_" a' k'')

tyConst :: LFModel f a c m => a -> m (f TYPE)
tyConst x = foldLF . AType =<< foldLF (TyConst x)

tyApp :: LFModel f a c m => m (f TYPE) -> m (f TERM) -> m (f TYPE)
tyApp a m = do
  a' <- a
  m' <- m
  case unfoldLF a' of
    AType p -> foldLF . AType =<< foldLF (TyApp p m')
    TyPi _ _ _ -> fail "Cannot apply terms to Pi Types"

lam :: LFModel f a c m => String -> m (f TYPE) -> m (f TERM) -> m (f TERM)
lam nm a m = foldLF =<< (Lam nm <$> a <*> m)

var :: LFModel f a c m => Int -> m (f TERM)
var v = foldLF . ATerm =<< foldLF (Var v)

tmConst :: LFModel f a c m => c -> m (f TERM)
tmConst x = foldLF . ATerm =<< foldLF (Const x)

app :: LFModel f a c m => m (f TERM) -> m (f TERM) -> m (f TERM)
app x y = do
  x' <- x
  y' <- y
  case unfoldLF x' of
    ATerm r -> foldLF . ATerm =<<  foldLF (App r y')
    Lam _ a m -> runChangeT $ hsubst y' 0 (simpleType a) m

checkType :: LFModel f a c m
          => Ctx f
          -> f TERM
          -> f TYPE
          -> m ()
checkType ctx m a = do
  a' <- inferType ctx m
  q  <- alphaEq a a'
  if q then return ()
       else fail "inferred type did not match expected type"

headConstantLF :: forall f a c m
                . LFModel f a c m
               => f TYPE
               -> m a
headConstantLF a =
  case unfoldLF a of
    AType p  -> f p
    TyPi _ _ a -> headConstant a
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
    (Type        , Type)           -> return True
    (KPi _ a k   , KPi _ a' k')    -> (&&) <$> alphaEq a a' <*> alphaEq k k'
    (AType x     , AType x')       -> alphaEq x x'
    (TyPi _ a1 a2, TyPi _ a1' a2') -> (&&) <$> alphaEq a1 a1' <*> alphaEq a2 a2'
    (TyConst x   , TyConst x')     -> return $ x == x'
    (TyApp a m   , TyApp a' m')    -> (&&) <$> alphaEq a a' <*> alphaEq m m'
    (ATerm x     , ATerm x')       -> alphaEq x x'
    (Lam _ a m   , Lam _ a' m')    -> (&&) <$> alphaEq a a' <*> alphaEq m m'
    (Var v       , Var v')         -> return $ v == v'
    (Const x     , Const x')       -> return $ x == x'
    (App r m     , App r' m')      -> (&&) <$> alphaEq r r' <*> alphaEq m m'
    _ -> return False

validateKindLF :: LFModel f a c m
               => Ctx f
               -> f KIND
               -> m ()
validateKindLF ctx tm =
  case unfoldLF tm of
    Type -> return ()
    KPi _ a k -> do
      validateType ctx a
      validateKind (a <| ctx) k
      {- subordination check -}

validateTypeLF :: LFModel f a c m
               => Ctx f
               -> f TYPE
               -> m ()
validateTypeLF ctx tm =
  case unfoldLF tm of
    TyPi _ a1 a2 -> do
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
        KPi _ a2 k1 -> do
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
    Lam nm a2 m -> do
      a1 <- inferType (a2 <| ctx) m
      foldLF (TyPi nm a2 a1)

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
        TyPi _ a2 a1 -> do
          checkType ctx m2 a2
          runChangeT $ hsubst m2 0 (simpleType a2) a1
        _ -> fail "Expected function type"

simpleType :: LFModel f a c m
         => f TYPE
         -> SimpleType a
simpleType tm =
  case unfoldLF tm of
    AType f -> simpleAType f
    TyPi _ a1 a2 -> SArrow (simpleType a1) (simpleType a2)

simpleAType :: LFModel f a c m
         => f ATYPE
         -> SimpleType a
simpleAType tm =
  case unfoldLF tm of
    TyConst x -> SConst x
    TyApp p _ -> simpleAType p


weakenLF :: LFModel f a c m
         => Int -- ^ cutoff
         -> Int -- ^ amount to weaken
         -> f s
         -> ChangeT m (f s)
weakenLF z i tm =
  case unfoldLF tm of
    Type         -> Unchanged tm
    KPi nm a k   -> onChange tm foldLF (KPi nm <$> weaken z i a <*> weaken (z+1) i k)

    AType x      -> onChange tm foldLF (AType <$> weaken z i x)
    TyPi nm a a' -> onChange tm foldLF (TyPi nm <$> weaken z i a <*> weaken (z+1) i a')

    TyConst _    -> Unchanged tm
    TyApp p m    -> onChange tm foldLF (TyApp <$> weaken z i p <*> weaken z i m)

    Lam nm a m   -> onChange tm foldLF (Lam nm <$> weaken z i a <*> weaken (z+1) i m)
    ATerm x      -> onChange tm foldLF (ATerm <$> weaken z i x)

    Const _      -> Unchanged tm
    App m1 m2    -> onChange tm foldLF (App <$> weaken z i m1 <*> weaken z i m2)

    Var v
     | v < z     -> Unchanged tm
     | otherwise -> Changed (foldLF (Var (v+i)))

hsubstLM :: forall f a c m s
          . LFModel f a c m
         => f TERM
         -> Int
         -> SimpleType a
         -> f s
         -> ChangeT m (f s)
hsubstLM tm0 v0 st0 = \tm ->
  case unfoldLF tm of
    Type         -> Unchanged tm
    KPi nm a k   -> onChange tm foldLF (KPi nm <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 k)

    AType x      -> onChange tm foldLF (AType <$> hsubst tm0 v0 st0 x)
    TyPi nm a a' -> onChange tm foldLF (TyPi nm <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 a')

    TyConst _    -> Unchanged tm
    TyApp p m    -> onChange tm foldLF (TyApp <$> hsubst tm0 v0 st0 p <*> hsubst tm0 v0 st0 m)

    Lam nm a m   -> onChange tm foldLF (Lam nm <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 m)
    ATerm x      -> onChange tm (either (return . fst) (foldLF . ATerm)) (hsubstTm x st0)

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
                   Left (unfoldLF -> Lam _ _ m1', SArrow stArg stBody) -> do
                     m' <- hsubst m2' 0 stArg m1'
                     Changed (return $ Left (m', stBody))
                   Right r1' ->
                     Changed (Right <$> foldLF (App r1' m2'))
                   _ ->
                     fail "hereditary substitution failed: ill-typed term"

data Prec
  = TopPrec
  | AppLPrec
  | AppRPrec
  | BinderPrec
 deriving (Eq)

getName :: Set String
        -> String
        -> (String, Set String)
getName ss nm = tryName ss (nm : [ nm++show i | i <- [0..] ])
 where
  tryName ss (x:xs)
    | Set.member x ss = tryName ss xs
    | otherwise = (x, Set.insert x ss)
  tryName _ [] = undefined

prettyLF
      :: LFModel f a c m
      => Set String
      -> Seq Doc
      -> Prec
      -> f s
      -> Doc
prettyLF usedNames nameScope prec x =
  case unfoldLF x of
    Type -> text "Type"
    KPi nm a k
      | freeVar 0 k ->
         let (nm', usedNames') = getName usedNames nm in
         (if prec /= TopPrec then parens else id) $
         text "Π" <> text nm' <+> colon <+>
           prettyLF usedNames nameScope BinderPrec a <> comma <+>
           prettyLF usedNames' (text nm' <| nameScope) TopPrec k
      | otherwise ->
         (if prec /= TopPrec then parens else id) $
           prettyLF usedNames nameScope BinderPrec a <+>
           text "→" <+>
           prettyLF usedNames (error "unbound name!" <| nameScope) TopPrec k
    AType x -> prettyLF usedNames nameScope prec x
    TyPi nm a1 a2
      | freeVar 0 a2 ->
         let (nm', usedNames') = getName usedNames nm in
         (if prec /= TopPrec then parens else id) $
         text "Π" <> text nm <+> colon <+>
           prettyLF usedNames nameScope BinderPrec a1 <> comma <+>
           prettyLF usedNames' (text nm' <| nameScope) TopPrec a2
      | otherwise ->
         (if prec /= TopPrec then parens else id) $
           prettyLF usedNames nameScope BinderPrec a1 <+>
           text "→" <+>
           prettyLF usedNames (error "unbound name!" <| nameScope) TopPrec a2

    TyConst x -> pretty x
    TyApp p a ->
         (if prec == AppRPrec then parens else id) $
         prettyLF usedNames nameScope AppLPrec p <+>
         prettyLF usedNames nameScope AppRPrec a
    ATerm x -> prettyLF usedNames nameScope prec x
    Lam nm a m ->
         let (nm', usedNames') = getName usedNames nm in
         (if prec /= TopPrec then parens else id) $
         text "λ" <> text nm' <+> colon <+>
           prettyLF usedNames nameScope BinderPrec a <> comma <+>
           prettyLF usedNames' (text nm' <| nameScope) TopPrec m
    Const x -> pretty x
    App m1 m2 ->
         (if prec == AppRPrec then parens else id) $
         prettyLF usedNames nameScope AppLPrec m1 <+>
         prettyLF usedNames nameScope AppRPrec m2
    Var v
       | v < Seq.length nameScope -> Seq.index nameScope v
       | otherwise -> error "Variable out of scope!"

freeVarLF :: LFModel f a c m
          => Int
          -> f s
          -> Bool
freeVarLF i tm =
  case unfoldLF tm of
    Type -> False
    KPi _ a k -> freeVar i a || freeVar (i+1) k
    AType x -> freeVar i x
    TyPi _ a1 a2 -> freeVar i a1 || freeVar (i+1) a2
    TyConst _ -> False
    TyApp p a -> freeVar i p || freeVar i a
    ATerm x -> freeVar i x
    Lam _ a m -> freeVar i a || freeVar (i+1) m
    Const _ -> False
    App r m -> freeVar i r || freeVar i m
    Var v
      | v == i    -> True
      | otherwise -> False
