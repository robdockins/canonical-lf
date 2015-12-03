module Lang.LF.Model where

import           Control.Monad
import           Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF.ChangeT

data SORT
  = KIND    -- ^ Kinds
  | TYPE    -- ^ Type families
  | ATYPE   -- ^ Atomic type families
  | TERM    -- ^ Terms
  | ATERM   -- ^ Atomic terms
  | CON     -- ^ Constraints

type KIND  = 'KIND
type TYPE  = 'TYPE
type ATYPE = 'ATYPE
type TERM  = 'TERM
type ATERM = 'ATERM
type CON   = 'CON

data Quant
  = QPi
  | QLam
  | QForall
  | QExists
 deriving (Eq, Ord, Show)

-- | The syntax algebra of canonical LF terms, parameterized
--   by the type of subterms `f`, the type `a` of type family
--   constants and the type `c` of term constants.
data LF (f :: SORT -> *) (a :: *) (c :: *) :: SORT -> * where
  Type   :: LF f a c KIND
  KPi    :: !String -> !(f TYPE) -> !(f KIND) -> LF f a c KIND

  AType   :: !(f ATYPE) -> LF f a c TYPE
  TyPi    :: !String -> !(f TYPE) -> !(f TYPE) -> LF f a c TYPE
  TyConst :: !a -> LF f a c ATYPE
  TyApp   :: !(f ATYPE) -> !(f TERM) -> LF f a c ATYPE

  ATerm  :: !(f ATERM) -> LF f a c TERM
  Lam    :: !String -> !(f TYPE) -> !(f TERM) -> LF f a c TERM
  Var    :: !(LFVar f) -> LF f a c ATERM
  Const  :: !c -> LF f a c ATERM
  App    :: !(f ATERM) -> !(f TERM) -> LF f a c ATERM

  Unify  :: !(f ATERM) -> !(f ATERM) -> LF f a c CON
  And    :: [f CON] -> LF f a c CON
  Forall :: !String -> !(f TYPE) -> !(f CON) -> LF f a c CON
  Exists :: !String -> !(f TYPE) -> !(f CON) -> LF f a c CON

newtype LFVar f = LFVar Int
 deriving (Eq, Ord, Show)

data KindView f a c
 = KindView
     (Seq (String, f TYPE))

data TypeView f a c
 = TypeView
     (Seq (String, f TYPE))
     a
     [f TERM]

data TermView f a c
 = ConstHead
     (Seq (String, f TYPE))
     c
     [f TERM]
 | VarHead
     (Seq (String, f TYPE))
     (LFVar f)
     [f TERM]


kindViewLF :: forall f a c m
            . LFModel f a c m
           => f KIND
           -> KindView f a c
kindViewLF = goK Seq.empty
  where goK :: Seq (String, f TYPE) -> f KIND -> KindView f a c
        goK pis x =
          case unfoldLF x of
            Type -> KindView pis
            KPi nm a k -> goK (pis |> (nm,a)) k

typeViewLF :: forall f a c m
            . LFModel f a c m
           => f TYPE
           -> TypeView f a c
typeViewLF = goTy Seq.empty
  where goTy :: Seq (String, f TYPE) -> f TYPE -> TypeView f a c
        goTy pis x =
          case unfoldLF x of
            TyPi nm a1 a2 -> goTy (pis |> (nm,a1)) a2
            AType p -> goATy pis [] p
        goATy :: Seq (String, f TYPE) -> [f TERM] -> f ATYPE -> TypeView f a c
        goATy pis args x =
          case unfoldLF x of
            TyConst a -> TypeView pis a args
            TyApp p m -> goATy pis (m : args) p

termViewLF :: forall f a c m
          . LFModel f a c m
         => f TERM
         -> TermView f a c
termViewLF = goTm Seq.empty
 where goTm :: Seq (String, f TYPE) -> f TERM -> TermView f a c
       goTm lams x =
         case unfoldLF x of
           Lam nm a m -> goTm (lams |> (nm,a))  m
           ATerm r    -> goATm lams [] r

       goATm :: Seq (String, f TYPE) -> [f TERM] -> f ATERM -> TermView f a c
       goATm lams args x =
         case unfoldLF x of
           Var v   -> VarHead   lams v args
           Const c -> ConstHead lams c args
           App r m -> goATm lams (m : args) r

data SimpleType
  = SBase
  | SArrow !SimpleType !SimpleType

class (Ord a, Ord c, Pretty a, Pretty c, Monad m) => LFModel (f :: SORT -> *) a c m | f -> a c m, m -> f a c where
  unfoldLF :: f s -> LF f a c s
  foldLF :: LF f a c s  -> m (f s)
  constKind :: a -> m (f KIND)
  constType :: c -> m (f TYPE)
  hsubst :: f TERM
         -> LFVar f
         -> Int
         -> SimpleType
         -> f s
         -> ChangeT m (f s)

  extendContext :: String -> Quant -> f TYPE -> m x -> m x
  lookupVariable :: LFVar f -> m (f TYPE)
  lookupVariableName :: LFVar f -> m String
  freshName :: String -> m String

  kindView :: f KIND -> KindView f a c
  typeView :: f TYPE -> TypeView f a c
  termView :: f TERM -> TermView f a c

  ppLF :: Prec -> f s -> m Doc
  validateKind :: f KIND -> m ()
  validateType :: f TYPE -> m ()
  inferKind :: f ATYPE -> m (f KIND)
  inferType :: f TERM -> m (f TYPE)
  inferAType :: f ATERM -> m (f TYPE)
  alphaEq :: f s -> f s -> m Bool
  headConstant :: f TYPE -> m a
  weaken :: Int -> Int -> f s -> ChangeT m (f s)
  freeVar :: LFVar f -> f s -> Bool
  contextDepth :: m Int
  underLambda :: f TERM -> (f TERM -> ChangeT m (f TERM)) -> ChangeT m (f TERM)

lf_type :: LFModel f a c m => m (f KIND)
lf_type = foldLF Type

kPi :: LFModel f a c m => String -> m (f TYPE) -> m (f KIND) -> m (f KIND)
kPi nm a k = foldLF =<< (KPi nm <$> a <*> k)

tyPi :: LFModel f a c m => String -> m (f TYPE) -> m (f TYPE) -> m (f TYPE)
tyPi nm a1 a2 = foldLF =<< (TyPi nm <$> a1 <*> a2)

infixr 5 ==>
infixl 2 @@

autoVar :: LFModel f a c m => m (m (f TERM))
autoVar = do
  startDepth <- contextDepth
  return $ do
    endDepth <- contextDepth
    if (endDepth > startDepth) then
      var (endDepth - startDepth - 1)
    else
      fail $ "automatic variable escaped its scope!"

λ :: LFModel f a c m => String -> m (f TYPE) -> (m (f TERM) -> m (f TERM)) -> m (f TERM)
λ nm tp f = do
  tp' <- tp
  v   <- autoVar
  nm' <- freshName nm
  m   <- extendContext nm' QLam tp' $ f v
  foldLF (Lam nm tp' m)

class LFPi (s::SORT) where
  pi :: LFModel f a c m => String -> m (f TYPE) -> (m (f TERM) -> m (f s)) -> m (f s)

instance LFPi KIND where
  pi nm tp f = do
    tp' <- tp
    v   <- autoVar
    nm' <- freshName nm
    k   <- extendContext nm' QPi tp' $ f v
    foldLF (KPi nm tp' k)

instance LFPi TYPE where
  pi nm tp f = do
    tp' <- tp
    v   <- autoVar
    nm' <- freshName nm
    a   <- extendContext nm' QPi tp' $ f v
    foldLF (TyPi nm tp' a)

class LFFunc (s::SORT) where
  (==>) :: LFModel f a c m => m (f TYPE) -> m (f s) -> m (f s)

instance LFFunc KIND where
  (==>) = kArrow
instance LFFunc TYPE where
  (==>) = tyArrow

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
    TyPi _ _ _ -> do
       adoc <- displayLF a'
       mdoc <- displayLF m'
       fail $ unwords ["Cannot apply terms to Pi Types", adoc, mdoc]

displayLF :: LFModel f a c m => f s -> m String
displayLF x = show <$> ppLF TopPrec x

mkLam :: LFModel f a c m => String -> m (f TYPE) -> m (f TERM) -> m (f TERM)
mkLam nm a m = foldLF =<< (Lam nm <$> a <*> m)

var :: LFModel f a c m => Int -> m (f TERM)
var v = foldLF . ATerm =<< foldLF (Var (LFVar v))

tmConst :: LFModel f a c m => c -> m (f TERM)
tmConst x = foldLF . ATerm =<< foldLF (Const x)

app :: LFModel f a c m => m (f TERM) -> m (f TERM) -> m (f TERM)
app x y = do
  x' <- x
  y' <- y
  case unfoldLF x' of
    ATerm r -> foldLF . ATerm =<< foldLF (App r y')
    Lam _ a m -> runChangeT $ hsubst y' zeroVar 0 (simpleType a) m

cExists :: LFModel f a c m
        => String
        -> m (f TYPE)
        -> (m (f TERM) -> m (f CON))
        -> m (f CON)
cExists nm tp f = do
  tp' <- tp
  v   <- autoVar
  nm' <- freshName nm
  m   <- extendContext nm' QForall tp' $ f v
  foldLF (Exists nm tp' m)

cForall :: LFModel f a c m
        => String
        -> m (f TYPE)
        -> (m (f TERM) -> m (f CON))
        -> m (f CON)
cForall nm tp f = do
  tp' <- tp
  v   <- autoVar
  nm' <- freshName nm
  m   <- extendContext nm' QForall tp' $ f v
  foldLF (Forall nm tp' m)

conj :: LFModel f a c m
     => [m (f CON)]
     -> m (f CON)
conj cs = foldLF . And =<< sequence cs

unify :: forall f a c m
       . LFModel f a c m
      => m (f TERM) -> m (f TERM) -> m (f CON)
unify x y = join (go <$> x <*> y)
 where
  go :: f TERM -> f TERM -> m (f CON)
  go x y =
   case (unfoldLF x, unfoldLF y) of
     (ATerm r1, ATerm r2) -> foldLF (Unify r1 r2)
     (Lam nm a1 m1, Lam _ a2 m2) -> do
        q <- alphaEq a1 a2
        unless q (fail "Attempting to unify LF terms with unequal types")
        foldLF . Forall nm a1 =<< go m1 m2 
     _ -> fail "Attempting to unify LF terms with unequal types"


checkType :: LFModel f a c m
          => f s
          -> f TERM
          -> f TYPE
          -> m ()
checkType z m a = do
  a' <- inferType m
  q  <- alphaEq a a'
  if q then return ()
       else do
         zdoc <- displayLF z
         mdoc <- displayLF m
         adoc  <- displayLF a
         adoc' <- displayLF a'
         fail $ unlines ["inferred type did not match expected type"
                        , "  in term: " ++ zdoc
                        , "  subterm: " ++ mdoc
                        , "  expected: " ++ adoc
                        , "  inferred: " ++ adoc'
                        ]

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
               => f KIND
               -> m ()
validateKindLF tm =
  case unfoldLF tm of
    Type -> return ()
    KPi nm a k -> do
      validateType a
      nm' <- freshName nm
      extendContext nm' QPi a $ validateKind k
      {- subordination check -}

validateTypeLF :: LFModel f a c m
               => f TYPE
               -> m ()
validateTypeLF tm =
  case unfoldLF tm of
    TyPi nm a1 a2 -> do
      validateType a1
      nm' <- freshName nm
      extendContext nm' QPi a1 $ validateType a2

    AType p -> do
      k <- inferKind p
      case unfoldLF k of
        Type -> return ()
        _ -> do
          kdoc <- displayLF k
          fail $ unwords ["invalid atomic type", kdoc]

inferKindLF :: LFModel f a c m
            => f ATYPE
            -> m (f KIND)
inferKindLF tm =
  case unfoldLF tm of
    TyConst x -> constKind x
    TyApp p1 m2 -> do
      k1 <- inferKind p1
      case unfoldLF k1 of
        KPi _ a2 k1 -> do
          checkType tm m2 a2
          runChangeT $ hsubst m2 zeroVar 0 (simpleType a2) k1
        _ -> do
               k1doc <- displayLF k1
               fail $ unwords ["invalid atomic type family", k1doc]

inferTypeLF :: LFModel f a c m
            => f TERM
            -> m (f TYPE)
inferTypeLF m =
  case unfoldLF m of
    ATerm r -> do
       a <- inferAType r
       case unfoldLF a of
         AType _ -> return a
         TyPi _ _ _ -> do
             adoc <- displayLF a
             mdoc <- displayLF m
             fail $ unlines ["Term fails to be η-long:"
                            , mdoc ++ " ::"
                            , adoc
                            ]
    Lam nm a2 m -> do
      nm' <- freshName nm
      a1 <- extendContext nm' QLam a2 $ inferType m
      foldLF (TyPi nm a2 a1)

inferATypeLF :: LFModel f a c m
            => f ATERM
            -> m (f TYPE)
inferATypeLF r =
  case unfoldLF r of
    Var i -> lookupVariable i
    Const c -> constType c
    App r1 m2 -> do
      a <- inferAType r1
      case unfoldLF a of
        TyPi _ a2 a1 -> do
          checkType r m2 a2
          runChangeT $ hsubst m2 zeroVar 0 (simpleType a2) a1
        _ -> do adoc <- displayLF a
                fail $ unwords ["Expected function type", adoc]

simpleType :: LFModel f a c m
         => f TYPE
         -> SimpleType
simpleType tm =
  case unfoldLF tm of
    AType _ -> SBase
    TyPi _ a1 a2 -> SArrow (simpleType a1) (simpleType a2)

{-
simpleAType :: LFModel f a c m
         => f ATYPE
         -> SimpleType a
simpleAType tm =
  case unfoldLF tm of
    TyConst x -> SConst x
    TyApp p _ -> simpleAType p
-}


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

    Var (LFVar v)
     | v < z     -> Unchanged tm
     | otherwise -> Changed (foldLF (Var (LFVar  (v+i))))

    Unify r1 r2   -> onChange tm foldLF (Unify <$> weakenLF z i r1 <*> weaken z i r2)
    And cs        -> onChange tm foldLF (And <$> mapM (weakenLF z i) cs)
    Forall nm a c -> onChange tm foldLF (Forall nm <$> weaken z i a <*> weaken (z+1) i c)
    Exists nm a c -> onChange tm foldLF (Forall nm <$> weaken z i a <*> weaken (z+1) i c)

hsubstLM :: forall f a c m s
          . LFModel f a c m
         => f TERM
         -> LFVar f
         -> Int
         -> SimpleType
         -> f s
         -> ChangeT m (f s)
hsubstLM tm0 !v0 !j st0 = \tm ->
  case unfoldLF tm of
    Type         -> Unchanged tm
    KPi nm a k   -> onChange tm foldLF (KPi nm <$> hsubst tm0 v0 j st0 a <*> hsubst tm0 (incVar v0) (j+1) st0 k)

    AType x      -> onChange tm foldLF (AType <$> hsubst tm0 v0 j st0 x)
    TyPi nm a a' -> onChange tm foldLF (TyPi nm <$> hsubst tm0 v0 j st0 a <*> hsubst tm0 (incVar v0) (j+1) st0 a')

    TyConst _    -> Unchanged tm
    TyApp p m    -> onChange tm foldLF (TyApp <$> hsubst tm0 v0 j st0 p <*> hsubst tm0 v0 j st0 m)

    Lam nm a m   -> onChange tm foldLF (Lam nm <$> hsubst tm0 v0 j st0 a <*> hsubst tm0 (incVar v0) (j+1) st0 m)
    ATerm x      -> onChange tm (either (return . fst) (foldLF . ATerm)) (hsubstTm x st0)

    And cs       -> onChange tm (foldLF . And) (mapM (hsubst tm0 v0 j st0) cs)
    Unify r1 r2  ->
        case (hsubstTm r1 st0, hsubstTm r2 st0) of
           (Unchanged _, Unchanged _) -> Unchanged tm
           (q1, q2) -> do
             let f :: Either (f TERM, SimpleType) (f ATERM) -> ChangeT m (f ATERM)
                 f (Left (unfoldLF -> ATerm r, _)) = return r
                 f (Right r) = return r
                 f _ = fail "hereditary substitution failed: ill-typed term (in unify)"
             r1' <- f =<< q1
             r2' <- f =<< q2
             Changed (foldLF (Unify r1' r2'))
    Forall nm a c -> onChange tm foldLF (Forall nm <$> hsubst tm0 v0 j st0 a <*> hsubst tm0 (incVar v0) (j+1) st0 c)
    Exists nm a c -> onChange tm foldLF (Exists nm <$> hsubst tm0 v0 j st0 a <*> hsubst tm0 (incVar v0) (j+1) st0 c)

    Const _ -> atermErr
    Var _   -> atermErr
    App _ _ -> atermErr

 where atermErr :: forall x. ChangeT m x
       atermErr = fail "Do not call hsubst directly on terms of sort ATERM"

       hsubstTm :: f ATERM
                -> SimpleType
                -> ChangeT m (Either (f TERM, SimpleType) (f ATERM))

       hsubstTm tm st =
         case unfoldLF tm of
           Var v
             | v0 == v   -> do
                   tm0' <- weaken 0 j tm0
                   Changed (return $ Left (tm0', st))
             | v0 <  v   -> Changed (Right <$> (foldLF $! Var $! decVar v))
             | otherwise -> Unchanged (Right tm)
           Const _       -> Unchanged (Right tm)
           App r1 m2 ->
             case hsubstTm r1 st of
               Unchanged _ ->
                 onChange (Right tm) (\m -> Right <$> foldLF (App r1 m)) (hsubst tm0 v0 j st m2)
               m -> do
                 m2' <- hsubst tm0 v0 j st m2
                 m >>= \case
                   Left (unfoldLF -> Lam _ _ m1', SArrow stArg stBody) -> do
                     m' <- hsubst m2' zeroVar 0 stArg m1'
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

prettyLF
      :: LFModel f a c m
      => Prec
      -> f s
      -> m Doc
prettyLF prec x =
  case unfoldLF x of
    Type -> return $ text "Type"
    KPi nm a k
      | freeVar (LFVar 0) k -> do
         nm' <- freshName nm
         adoc <- ppLF BinderPrec a
         kdoc <- extendContext nm' QPi a $ ppLF TopPrec k
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> adoc <+> comma <> nest 2 (softline <> kdoc)
      | otherwise -> do
         adoc <- ppLF BinderPrec a
         kdoc <- extendContext "_" QPi (error "unbound name!") $ ppLF TopPrec k
         return $ group $ (if prec /= TopPrec then parens else id) $
           align (adoc <+> text "⇒" <> line <> kdoc)
    AType x -> group . (linebreak <>) . hang 2 <$> (ppLF prec x)
    TyPi nm a1 a2
      | freeVar (LFVar 0) a2 -> do
         nm' <- freshName nm
         a1doc <- ppLF BinderPrec a1
         a2doc <- extendContext nm' QPi a1 $ ppLF TopPrec a2
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> a1doc <> comma <> nest 2 (softline <> a2doc)
      | otherwise -> do
         a1doc <- ppLF BinderPrec a1
         a2doc <- extendContext "_" QPi (error "unbound name!") $ ppLF TopPrec a2
         return $! group $ (if prec /= TopPrec then parens else id) $
           (align (a1doc <+> text "⇒" <> softline <> a2doc))
    TyConst x -> return $ pretty x
    TyApp p a -> do
         pdoc <- ppLF AppLPrec p
         adoc <- ppLF AppRPrec a
         return $! group $ (if prec == AppRPrec then parens else id) $
            (pdoc <> line <> adoc)
    ATerm x
      | prec == TopPrec -> group . (linebreak <>) . hang 2 <$> (ppLF prec x)
      | otherwise -> hang 2 <$> ppLF prec x
    Lam nm a m -> do
         nm' <- freshName nm
         adoc <- ppLF BinderPrec a
         mdoc <- extendContext nm' QLam a $ ppLF TopPrec m
         return $! (if prec /= TopPrec then parens else id) $
           text "λ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> mdoc)
    Const x -> return $ pretty x
    App m1 m2 -> do
         m1doc <- ppLF AppLPrec m1
         m2doc <- ppLF AppRPrec m2
         return $! group $ (if prec == AppRPrec then parens else id) $
            (m1doc <> line <> m2doc)
    Var v -> text <$> lookupVariableName v

    Unify r1 r2 -> do
         r1doc <- ppLF TopPrec r1
         r2doc <- ppLF TopPrec r2
         return $ (r1doc <> text "=" <> line <> r2doc)

    And [] -> return $ text "⊤"
    And cs -> do
         cs' <- mapM (ppLF TopPrec) cs
         return $ align $ cat $ punctuate (text "∧") cs'

    Forall nm a c -> do
         nm' <- freshName nm
         adoc <- ppLF BinderPrec a
         cdoc <- extendContext nm' QForall a $ ppLF TopPrec c
         return $ (if prec /= TopPrec then parens else id) $
           text "∀" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Exists nm a c -> do
         nm' <- freshName nm
         adoc <- ppLF BinderPrec a
         cdoc <- extendContext nm' QExists a $ ppLF TopPrec c
         return $ (if prec /= TopPrec then parens else id) $
           text "∃" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)


incVar :: LFVar f -> LFVar v
incVar (LFVar x) = LFVar (x+1)

decVar :: LFVar f -> LFVar v
decVar (LFVar x) = LFVar (x-1)

zeroVar :: LFVar f
zeroVar = LFVar 0

freeVarLF :: LFModel f a c m
          => LFVar f
          -> f s
          -> Bool
freeVarLF !i tm =
  case unfoldLF tm of
    Type -> False
    KPi _ a k -> freeVar i a || freeVar (incVar i) k
    AType x -> freeVar i x
    TyPi _ a1 a2 -> freeVar i a1 || freeVar (incVar i) a2
    TyConst _ -> False
    TyApp p a -> freeVar i p || freeVar i a
    ATerm x -> freeVar i x
    Lam _ a m -> freeVar i a || freeVar (incVar i) m
    Const _ -> False
    App r m -> freeVar i r || freeVar i m
    Var v
      | v == i    -> True
      | otherwise -> False
    Unify r1 r2 -> freeVar i r1 || freeVar i r2
    And cs -> any (freeVar i) cs
    Forall _ a c -> freeVar i a || freeVar (incVar i) c
    Exists _ a c -> freeVar i a || freeVar (incVar i) c
