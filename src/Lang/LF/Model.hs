{-# LANGUAGE UndecidableInstances #-}
module Lang.LF.Model where

import GHC.Exts ( Constraint )

import           Control.Monad
--import           Control.Monad.Trans.Class
--import           Data.Sequence (Seq, (|>))
--import qualified Data.Sequence as Seq
import           Data.Proxy
import           Data.Set (Set)
import qualified Data.Set as Set
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

--import           Lang.LF.ChangeT

--import qualified Debug.Trace as Debug

data SORT
  = KIND    -- ^ Kinds
  | TYPE    -- ^ Type families
  | ATYPE   -- ^ Atomic type families
  | TERM    -- ^ Terms
  | ATERM   -- ^ Atomic terms
  | CON     -- ^ Constraints
  | GOAL    -- ^ Search/unification goals

type KIND  = 'KIND
type TYPE  = 'TYPE
type ATYPE = 'ATYPE
type TERM  = 'TERM
type ATERM = 'ATERM
type CON   = 'CON
type GOAL  = 'GOAL

data Quant
  = QPi
  | QLam
  | QSigma
  | QForall
  | QExists
 deriving (Eq, Ord, Show)

data Ctx k = E | Ctx k ::> k

type family LFTypeConst (f :: Ctx * -> SORT -> *) :: *
type family LFConst (f :: Ctx * -> SORT -> *) :: *

-- | The syntax algebra of canonical LF terms, parameterized
--   by the type of subterms `f`, the type `a` of type family
--   constants and the type `c` of term constants.
data LF (f :: Ctx * -> SORT -> *) :: Ctx * -> SORT -> * where
  Weak   :: f γ s -> LF f (γ ::> b) s

  Type   :: LF f E KIND
  KPi    :: !String -> !(f γ TYPE) -> f (γ ::> ()) KIND -> LF f γ KIND

  AType   :: !(f γ ATYPE) -> LF f γ TYPE
  TyPi    :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) TYPE) -> LF f γ TYPE
  TyConst :: !(LFTypeConst f) -> LF f E ATYPE
  TyApp   :: !(f γ ATYPE) -> !(f γ TERM) -> LF f γ ATYPE

  ATerm  :: !(f γ ATERM) -> LF f γ TERM
  Lam    :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) TERM) -> LF f γ TERM
  Var    :: !b -> LF f (γ ::> b) ATERM
  Const  :: !(LFConst f) -> LF f E ATERM
  App    :: !(f γ ATERM) -> !(f γ TERM) -> LF f γ ATERM

  Unify  :: !(f γ ATERM) -> !(f γ ATERM) -> LF f γ CON
  And    :: [f γ CON] -> LF f γ CON
  Forall :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON
  Exists :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON

  Sigma  :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON
  Goal   :: !(f γ TERM) -> !(f γ CON) -> LF f γ GOAL

{-
-- | LFVar is a representation of free variables whose type
--   is given by the current context.  It counts from element
--   0 being the OUTERMOST variable in the context, rather than
--   the innermost.  Thus, LFVars count the opposite way from deBruijn
--   indices.  This means they do not need to be weakened when passing
--   under binders BUT they should not be used outside the scope where
--   they are introduced!
newtype LFVar f = LFVar Int
 deriving (Eq, Ord, Show)
-}

{-
data KindView f a c m 
 = VType
 | VKPi (forall x. (LFVar f -> f KIND -> m x) -> m x)

data TypeView f a c m
 = VTyPi (forall x. (LFVar f -> f TYPE -> m x) -> m x)
 | VTyConst a [f TERM]

data TermView f a c m
 = VLam (forall x y. (LFVar f -> x -> m y) -> (LFVar f -> f TERM -> m x) -> m y)
 | VVar (forall x. (LFVar f -> [f TERM] -> m x) -> m x)
 | VConst c [f TERM]

kindViewLF :: forall f a c m
            . LFModel f a c m
           => f KIND
           -> KindView f a c m
kindViewLF k =
  case unfoldLF k of
    Type -> VType
    KPi nm a k -> VKPi $ \cont -> do
       nm' <- freshName nm
       v <- contextDepth
       extendContext nm' QPi a $ cont (LFVar v) k

typeViewLF :: forall f a c m
            . LFModel f a c m
           => f TYPE
           -> TypeView f a c m
typeViewLF a =
  case unfoldLF a of
    TyPi nm a1 a2 -> VTyPi $ \cont -> do
       nm' <- freshName nm
       v <- contextDepth
       extendContext nm' QPi a1 $ cont (LFVar v) a2
    AType p -> go [] p

  where go :: [f TERM] -> f ATYPE -> TypeView f a c m
        go args x =
          case unfoldLF x of
            TyConst a -> VTyConst a args
            TyApp p m -> go (m : args) p

termViewLF :: forall f a c m
          . LFModel f a c m
         => f TERM
         -> TermView f a c m
termViewLF m =
  case unfoldLF m of
    Lam nm a m' -> VLam $ \bind cont -> do
       nm' <- freshName nm
       v <- contextDepth
       extendContext nm' QLam a $ (bind (LFVar v) =<< cont (LFVar v) m')
    ATerm r -> go [] r

 where go :: [f TERM] -> f ATERM -> TermView f a c m
       go args x =
         case unfoldLF x of
           Var v -> VVar $ \cont -> do
              d <- contextDepth
              cont (LFVar (d - v - 1)) args
           Const c -> VConst c args
           App r m -> go (m : args) r
-}

{-
data SimpleType
  = SBase
  | SArrow !SimpleType !SimpleType
-}

{-strengthen :: LFModel f a c m
           => LFVar f
           -> f s
           -> m (f s)
strengthen (LFVar v) x = do
   d <- contextDepth
   if( d > v ) then 
     let i = d - v - 1 in
     if freeVar i x then do
       xdoc <- displayLF x
       fail $ unlines ["Cannot strengthen; variable occurs free"
                      , unwords [show d, show v, show i]
                      , xdoc
                      ]
     else 
       runChangeT $ weaken i (-1) x
   else
     fail "Strengthening an escaped variable"
-}

class (Ord (LFTypeConst f), Ord (LFConst f),
       Pretty (LFTypeConst f), Pretty (LFConst f),
       Monad m)
  => LFModel (f :: Ctx * -> SORT -> *) m | f -> m, m -> f where
  unfoldLF :: f γ s -> LF f γ s
  foldLF :: LF f γ s -> m (f γ s)
  weaken :: f γ s -> f (γ ::> b) s

  hsubst :: Subst m f γ γ'
         -> f γ s
         -> m (f γ' s)

  ppLF :: WFContext γ
       => Prec
       -> Set String
       -> Hyps f γ
       -> f γ s
       -> m Doc

  validateKind :: Set String -> Hyps f γ -> f γ KIND  -> m ()
  validateType :: Set String -> Hyps f γ -> f γ TYPE  -> m ()
  inferKind    :: Set String -> Hyps f γ -> f γ ATYPE -> m (f γ KIND)
  inferType    :: Set String -> Hyps f γ -> f γ TERM  -> m (f γ TYPE)
  inferAType   :: Set String -> Hyps f γ -> f γ ATERM -> m (f γ TYPE)
  alphaEq :: f γ s -> f γ s -> m Bool

{-
  constKind :: a -> m (f KIND x)
  constType :: c -> m (f TYPE x)
  depth :: f s x -> Int

  hsubst :: f TERM
         -> Int
         -> Int
         -> SimpleType
         -> f s
         -> ChangeT m (f s)

  extendContext :: String -> Quant -> f TYPE -> m x -> m x
  lookupVariable :: LFVar f -> m (f TYPE)
  lookupVariableName :: LFVar f -> m String
  freshName :: String -> m String

  kindView :: f KIND -> KindView f a c m
  typeView :: f TYPE -> TypeView f a c m
  termView :: f TERM -> TermView f a c m

  ppLF :: Prec -> f s -> m Doc
  headConstant :: f TYPE -> m a
  weaken :: Int -> Int -> f s -> ChangeT m (f s)
  freeVar :: Int -> f s -> Bool
  contextDepth :: m Int
  underLambda :: f TERM -> (f TERM -> ChangeT m (f TERM)) -> ChangeT m (f TERM)
  dumpContext :: m Doc
-}

type family CtxAppend γ γ' :: Ctx * where
  CtxAppend γ E = γ
  CtxAppend γ (γ' ::> b) = CtxAppend γ γ' ::> b

type family CtxDiff γ γ' :: Ctx * where
  CtxDiff γ γ = E
  CtxDiff γ (γ' ::> b) = CtxDiff γ γ' ::> b

class (CtxAppend γ diff ~ γ') => AutoWeaken γ diff γ' where
  autoweaken' :: LFModel f m => Proxy diff -> f γ s -> f γ' s
class CtxSub (γ :: Ctx *) (γ' :: Ctx *) where
  autoweaken :: LFModel f m => f γ s -> f γ' s

instance AutoWeaken γ E γ where
  autoweaken' _ = id
instance AutoWeaken γ diff γ' => AutoWeaken γ (diff ::> b) (γ' ::> b) where
  autoweaken' _ = weaken . autoweaken' (Proxy :: Proxy diff)
instance (CtxAppend γ (CtxDiff γ γ') ~ γ', AutoWeaken γ (CtxDiff γ γ') γ') => CtxSub γ γ' where
  autoweaken = autoweaken' (Proxy :: Proxy (CtxDiff γ γ'))

type IsBoundVar b = (Show b, Ord b, Eq b)

type family WFContextRec (c::Ctx *) :: Constraint where
  WFContextRec E = ()
  WFContextRec (γ ::> b) = (WFContext γ, IsBoundVar b)

type WFContext γ = (LiftClosed γ, Ord (Var γ), WFContextRec γ)

class LiftClosed (γ :: Ctx *) where
  liftClosed :: LFModel f m => f E s -> f γ s
instance LiftClosed E where
  liftClosed = id
instance LiftClosed γ => LiftClosed (γ ::> b) where
  liftClosed = weaken . liftClosed


lf_type :: (WFContext γ, LFModel f m) => m (f γ KIND)
lf_type = liftClosed <$> foldLF Type

kPi :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ ::> ()) KIND) -> m (f γ KIND)
kPi nm a k = foldLF =<< (KPi nm <$> a <*> k)

tyPi :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ ::> ()) TYPE) -> m (f γ TYPE)
tyPi nm a1 a2 = foldLF =<< (TyPi nm <$> a1 <*> a2)

infixr 5 ==>
infixl 2 @@

var0 :: LFModel f m => Var γ -> (f γ ATERM -> f γ' ATERM) -> m (f γ' ATERM)
var0 (F x) w = var0 x (w . weaken)
var0 (B b) w = w <$> foldLF (Var b)

var :: (CtxSub γ γ', LFModel f m) => Var γ -> m (f γ' TERM)
var v = autoweaken <$> (foldLF . ATerm =<< var0 v id)

λ :: (LFModel f m)
  => String
  -> m (f γ TYPE)
  -> (forall b. IsBoundVar b => Var (γ ::> b) -> m (f (γ::>b) TERM))
  -> m (f γ TERM)
λ nm tp f = do
  tp' <- tp
  m   <- f (B ())
  foldLF (Lam nm tp' m)

class LFPi (s::SORT) where
  pi :: LFModel f m
     => String
     -> m (f γ TYPE)
     -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) s))
     -> m (f γ s)

instance LFPi KIND where
  pi nm tp f = do
    tp' <- tp
    k   <- f (B ())
    foldLF (KPi nm tp' k)

instance LFPi TYPE where
  pi nm tp f = do
    tp' <- tp
    a   <- f (B ())
    foldLF (TyPi nm tp' a)

class LFFunc (s::SORT) where
  (==>) :: LFModel f m => m (f γ TYPE) -> m (f γ s) -> m (f γ s)

instance LFFunc KIND where
  (==>) = kArrow
instance LFFunc TYPE where
  (==>) = tyArrow

class LFApplication (s::SORT) where
  (@@) :: (WFContext γ, LFModel f m) => m (f γ s) -> m (f γ TERM) -> m (f γ s)

instance LFApplication TYPE where
  (@@) = tyApp
instance LFApplication TERM where
  (@@) = app

tyArrow :: LFModel f m => m (f γ TYPE) -> m (f γ TYPE) -> m (f γ TYPE)
tyArrow a1 a2 = do
   a1' <- a1
   a2' <- weaken <$> a2
   foldLF (TyPi "_" a1' a2')

kArrow :: LFModel f m => m (f γ TYPE) -> m (f γ KIND) -> m (f γ KIND)
kArrow a k = do
   a' <- a
   k' <- weaken <$> k
   foldLF (KPi "_" a' k')

tyConst :: (WFContext γ, LFModel f m) => LFTypeConst f -> m (f γ TYPE)
tyConst x = liftClosed <$> (foldLF . AType =<< foldLF (TyConst x))

tyApp :: forall f m γ. LFModel f m => m (f γ TYPE) -> m (f γ TERM) -> m (f γ TYPE)
tyApp a m = join (go1 <$> a <*> m)
 where
  go1 :: forall γ. f γ TYPE -> f γ TERM -> m (f γ TYPE)
  go1 a' m' =
   case (unfoldLF a', unfoldLF m') of
     (Weak a'', Weak m'') -> weaken <$> go1 a'' m''
     _ -> go2 a' m' id

  go2 :: forall γ γ'. f γ TYPE -> f γ' TERM -> (f γ ATYPE -> f γ' ATYPE) -> m (f γ' TYPE)
  go2 a' m' w =
   case unfoldLF a' of
     Weak a'' -> go2 a'' m' (w . weaken)
     AType p -> foldLF . AType =<< foldLF (TyApp (w p) m')
     TyPi _ _ _ -> do
        fail $ unwords ["Cannot apply terms to Pi Types"]

{-
    TyPi _ _ _ -> do
       adoc <- displayLF a'
       mdoc <- displayLF m'
       fail $ unwords ["Cannot apply terms to Pi Types", adoc, mdoc]

displayLF :: LFModel f a c m => f s -> m String
displayLF x = show <$> ppLF TopPrec x
-}

mkLam :: LFModel f m => String -> m (f γ TYPE) -> m (f (γ::>()) TERM) -> m (f γ TERM)
mkLam nm a m = do
  a' <- a
  m' <- m
  foldLF (Lam nm a' m')

tmConst :: (WFContext γ, LFModel f m) => LFConst f -> m (f γ TERM)
tmConst x = liftClosed <$> (foldLF . ATerm =<< foldLF (Const x))


app :: forall m f γ. (WFContext γ, LFModel f m)
    => m (f γ TERM)
    -> m (f γ TERM)
    -> m (f γ TERM)
app x y = join (go1 <$> x <*> y)
 where
  go1 :: forall γ. WFContext γ => f γ TERM -> f γ TERM -> m (f γ TERM)
  go1 x' y' =
   case (unfoldLF x', unfoldLF y') of
     (Weak x'', Weak y'') -> weaken <$> go1 x'' y''
     _ -> go2 x' y' id SubstEnd

  go2 :: forall γ γ'. WFContext γ'
                   => f γ TERM
                   -> f γ' TERM
                   -> (forall s. f γ s -> f γ' s)
                   -> (Subst m f γ γ')
                   -> m (f γ' TERM)
  go2 x' y' w s =
   case unfoldLF x' of
     Weak x''  -> go2 x'' y' (w . weaken) (SubstWeak s)
     ATerm r   -> foldLF . ATerm =<< foldLF (App (w r) y')
     Lam _ _ m -> hsubst (SubstApply s (\_ -> return y')) m

{-
cExists :: LFModel f a c m
        => String
        -> m (f TYPE)
        -> (LFVar f -> m (f CON))
        -> m (f CON)
cExists nm tp f = do
  tp' <- autoweaken tp
  v   <- autoVar
  nm' <- freshName nm
  m   <- extendContext nm' QForall tp' $ autoweaken (f v)
  foldLF (Exists nm tp' m)

cForall :: LFModel f a c m
        => String
        -> m (f TYPE)
        -> (LFVar f -> m (f CON))
        -> m (f CON)
cForall nm tp f = do
  tp' <- autoweaken tp
  v   <- autoVar
  nm' <- freshName nm
  m   <- extendContext nm' QForall tp' $ autoweaken (f v)
  foldLF (Forall nm tp' m)

cTrue :: LFModel f a c m
      => m (f CON)
cTrue = conj []      

conj :: forall f a c m
      . LFModel f a c m
     => [m (f CON)]
     -> m (f CON)
conj cs = foldLF . And . concat =<< mapM (f =<<) cs
 where f :: f CON -> m [f CON]
       f (unfoldLF -> (And xs)) = concat <$>  mapM f xs
       f x = (:[]) <$> autoweaken (return x)

unify :: forall f a c m
       . LFModel f a c m
      => m (f TERM) -> m (f TERM) -> m (f CON)
unify x y = join (go <$> (autoweaken x) <*> (autoweaken y))
 where
  go :: f TERM -> f TERM -> m (f CON)
  go x y =
   case (unfoldLF x, unfoldLF y) of
     (ATerm r1, ATerm r2) -> do
         q <- alphaEq r1 r2
         if q then
           cTrue
         else
           foldLF (Unify r1 r2)
     (Lam nm a1 m1, Lam _ a2 m2) -> do
        q <- alphaEq a1 a2
        unless q (fail "Attempting to unify LF terms with unequal types")
        foldLF . Forall nm a1 =<< go m1 m2 
     _ -> fail "Attempting to unify LF terms with unequal types"

sigma :: LFModel f a c m
      => String
      -> m (f TYPE)
      -> (LFVar f -> m (f GOAL))
      -> m (f GOAL)
sigma nm tp f = do
  tp' <- autoweaken tp
  v   <- autoVar
  nm' <- freshName nm
  m   <- extendContext nm' QSigma tp' $ autoweaken (f v)
  foldLF (Sigma nm tp' m)

goal :: LFModel f a c m
     => m (f TERM)
     -> m (f CON)
     -> m (f GOAL)
goal m c = do
   foldLF =<< (Goal <$> (autoweaken m) <*> (autoweaken c))

underGoal :: LFModel f a c m
          => f GOAL
          -> (f TERM -> f CON -> m (f GOAL))
          -> m (f GOAL)
underGoal g cont =
  case unfoldLF g of
    Sigma nm a g' -> do    
      nm' <- freshName nm
      g'' <- extendContext nm' QSigma a $ underGoal g' cont
      foldLF (Sigma nm a g'')
    Goal m c -> cont m c

solve :: LFModel f a c m
      => f GOAL
      -> m (f TERM)
solve g =
  case unfoldLF g of
    Goal m (unfoldLF -> And []) -> return m
    _ -> do
       gstr <- displayLF g
       fail $ unlines ["Goal not completely solved:"
                      , gstr
                      ]

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
-}

mapF :: (Var γ -> Var γ') -> Var (γ ::> b) -> Var (γ' ::> b)
mapF _ (B b) = B b
mapF f (F x) = F (f x)

alphaEqLF :: (WFContext γ, LFModel f m)
          => (Var γ₁ -> Var γ)
          -> (Var γ₂ -> Var γ)
          -> f γ₁ s
          -> f γ₂ s
          -> m Bool
alphaEqLF w₁ w₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak x'     , _)              -> alphaEqLF (w₁ . F) w₂ x' y
    (_           , Weak y')        -> alphaEqLF w₁ (w₂ . F) x y'
    (Type        , Type)           -> return True
    (KPi _ a k   , KPi _ a' k')    -> (&&) <$> alphaEqLF w₁ w₂ a a' <*> alphaEqLF (mapF w₁) (mapF w₂) k k'
    (AType x     , AType x')       -> alphaEqLF w₁ w₂ x x'
    (TyPi _ a1 a2, TyPi _ a1' a2') -> (&&) <$> alphaEqLF w₁ w₂ a1 a1' <*> alphaEqLF (mapF w₁) (mapF w₂) a2 a2'
    (TyConst x   , TyConst x')     -> return $ x == x'
    (TyApp a m   , TyApp a' m')    -> (&&) <$> alphaEqLF w₁ w₂ a a' <*> alphaEqLF w₁ w₂ m m'
    (ATerm x     , ATerm x')       -> alphaEqLF w₁ w₂ x x'
    (Lam _ a m   , Lam _ a' m')    -> (&&) <$> alphaEqLF w₁ w₂ a a' <*> alphaEqLF (mapF w₁) (mapF w₂) m m'
    (Var v       , Var v')         -> return $ w₁ (B v) == w₂ (B v')
    (Const x     , Const x')       -> return $ x == x'
    (App r m     , App r' m')      -> (&&) <$> alphaEqLF w₁ w₂ r r' <*> alphaEqLF w₁ w₂ m m'
    (Unify r1 r2 , Unify r1' r2')  -> (&&) <$> alphaEqLF w₁ w₂ r1 r1' <*> alphaEqLF w₁ w₂ r2 r2'
    (And cs      , And cs')        -> all id <$> (sequence $ zipWith (alphaEqLF w₁ w₂) cs cs')
    (Forall _ a c, Forall _ a' c') -> (&&) <$> alphaEqLF w₁ w₂ a a' <*> alphaEqLF (mapF w₁) (mapF w₂) c c'
    (Exists _ a c, Exists _ a' c') -> (&&) <$> alphaEqLF w₁ w₂ a a' <*> alphaEqLF (mapF w₁) (mapF w₂) c c'
    (Sigma _ a g , Sigma _ a' g')  -> (&&) <$> alphaEqLF w₁ w₂ a a' <*> alphaEqLF (mapF w₁) (mapF w₂) g g'
    (Goal m c    , Goal m' c')     -> (&&) <$> alphaEqLF w₁ w₂ m m' <*> alphaEqLF w₁ w₂ c c'
    _ -> return False

validateKindLF :: LFModel f m
               => Set String
               -> Hyps f γ
               -> f γ KIND
               -> m ()
validateKindLF nms hyps tm =
  case unfoldLF tm of
    Weak x ->
      case hyps of
        HCons hyps' _ _ -> validateKind nms hyps' x
        _ -> error "impossible"
    Type -> return ()
    KPi nm a k -> do
      validateType nms hyps a
      let (nm',nms') = freshName nm nms
      validateKind nms' (extendHyps hyps nm' QPi a) k
      {- subordination check -}

validateTypeLF :: LFModel f m
               => Set String
               -> Hyps f γ
               -> f γ TYPE
               -> m ()
validateTypeLF nms hyps tm =
  case unfoldLF tm of
    Weak x ->
      case hyps of
        HCons hyps' _ _ -> validateType nms hyps' x
    TyPi nm a1 a2 -> do
      validateType nms hyps a1
      let (nm',nms') = freshName nm nms
      validateType nms' (extendHyps hyps nm' QPi a1) a2

    AType p -> do
      k <- inferKind nms hyps p
      case unfoldLF k of
        Type -> return ()
{-
        _ -> do
          kdoc <- displayLF k
          fail $ unwords ["invalid atomic type", kdoc]
-}

{-

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
          runChangeT $ hsubst m2 0 0 (simpleType a2) k1
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
    Var i -> do
        d <- contextDepth
        if d > i then
          lookupVariable (LFVar (d - i - 1))
        else
          fail $ "Unbound variable while inferring type"
    Const c -> constType c
    App r1 m2 -> do
      a <- inferAType r1
      case unfoldLF a of
        TyPi _ a2 a1 -> do
          checkType r m2 a2
          runChangeT $ hsubst m2 0 0 (simpleType a2) a1
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
-}


instantiateVar :: forall f m γ s
                . (LFModel f m)
               => f (γ ::> ()) s
               -> f γ TERM
               -> m (f γ s)
instantiateVar body arg = hsubst sub body
 where sub :: Subst m f (γ ::> ()) γ
       sub = SubstApply SubstEnd (\_ -> return arg)

data Subst m f :: Ctx * -> Ctx * -> * where
  SubstEnd   :: Subst m f γ γ
  SubstApply :: Subst m f γ γ' -> (b -> m (f γ' TERM)) -> Subst m f (γ ::> b) γ'
  SubstWeak  :: Subst m f (γ ::> b) γ' -> Subst m f γ γ'
  SubstSkip  :: Subst m f γ γ' -> Subst m f (γ ::> b) (γ' ::> b)

hsubstLF :: forall f m s γ γ'
          . (LFModel f m)
         => Subst m f γ γ'
         -> f γ s
         -> m (f γ' s)
hsubstLF SubstEnd tm = return tm
hsubstLF (SubstWeak s) tm = hsubst s (weaken tm)
hsubstLF sub tm =
  case unfoldLF tm of
     Weak x ->
       case sub of
         SubstSkip    s -> weaken <$> hsubst s x
         SubstApply s _ -> hsubst s x
         SubstEnd       -> return tm
         SubstWeak s    -> hsubst s (weaken tm)

     Type ->
        case sub of
          SubstEnd    -> return tm
          SubstWeak s -> hsubst s (weaken tm)
          _ -> error "impossible"

     KPi nm a k   -> foldLF =<< (KPi nm <$> hsubst sub a <*> hsubst sub' k)

     AType x      -> foldLF =<< (AType <$> hsubst sub x)
     TyPi nm a a' -> foldLF =<< (TyPi nm <$> hsubst sub a <*> hsubst sub' a')

     TyConst _ ->
        case sub of
          SubstEnd -> return tm
          SubstWeak s -> hsubst s (weaken tm)
          _ -> error "impossible"

     TyApp p m    -> foldLF =<< (TyApp <$> hsubst sub p <*> hsubst sub m)
 
     Lam nm a m   -> foldLF =<< (Lam nm <$> hsubst sub a <*> hsubst sub' m)

     And cs       -> foldLF . And =<< (mapM (hsubst sub) cs)

     Unify r1 r2  -> do
        let f :: Either (f γ' TERM) (f γ' ATERM) -> m (f γ' ATERM)
            f (Left (unfoldLF -> ATerm r)) = return r
            f (Right r) = return r
            f _ = fail "hereditary substitution failed: ill-typed term (in unify)"
        r1' <- f =<< hsubstTm sub r1
        r2' <- f =<< hsubstTm sub r2
        foldLF (Unify r1' r2')

     Forall nm a c -> foldLF =<< (Forall nm <$> hsubst sub a <*> hsubst sub' c)
     Exists nm a c -> foldLF =<< (Exists nm <$> hsubst sub a <*> hsubst sub' c)

     Sigma nm a g  -> foldLF =<< (Sigma nm <$> hsubst sub a <*> hsubst sub' g)
     Goal m c      -> foldLF =<< (Goal <$> hsubst sub m <*> hsubst sub c)

     ATerm x      -> either return (foldLF . ATerm) =<< hsubstTm sub x

     Const _ -> atermErr
     Var _   -> atermErr
     App _ _ -> atermErr

 where
  sub' :: forall b. Subst m f (γ ::> b) (γ' ::> b)
  sub' = SubstSkip sub

  atermErr :: forall x. m x
  atermErr = fail "Do not call hsubst directly on terms of sort ATERM"

hsubstTm :: forall m f γ γ'
          . (LFModel f m)
         => Subst m f γ γ'
         -> f γ ATERM
         -> m (Either (f γ' TERM) (f γ' ATERM))
hsubstTm (SubstWeak s) tm = hsubstTm s (weaken tm)
hsubstTm sub tm =
         case unfoldLF tm of
           Weak x ->
             case sub of
               SubstApply s _ -> hsubstTm s x
               SubstSkip s -> do
                   x' <- hsubstTm s x
                   return $ either (Left. weaken) (Right . weaken) x'
               SubstEnd       -> return (Right tm)
               SubstWeak s    -> hsubstTm s (weaken tm)

           Var v ->
             case sub of
               SubstApply _ f -> Left <$> f v
               SubstSkip _    -> Right <$> foldLF (Var v)
               SubstEnd       -> return $ Right $ tm
               SubstWeak s    -> hsubstTm s (weaken tm)

           Const _ ->
             case sub of
               SubstEnd -> return $ Right $ tm
               SubstWeak s -> hsubstTm s (weaken tm)
               _ -> error "impossible"

           App r1 m2 -> do
             r1' <- hsubstTm sub r1
             m2' <- hsubst sub m2
             case r1' of
               Left (unfoldLF -> Lam _ _ m1') -> do
                 Left <$> instantiateVar m1' m2'
               Right r1'' ->
                 Right <$> foldLF (App r1'' m2')
               _ -> fail "hereditary substitution failed: ill-typed term"

{-
-}
{-
    And cs       -> onChange tm (foldLF . And) (mapM (hsubst tm0 v0 st0) cs)
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
    Forall nm a c -> onChange tm foldLF (Forall nm <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 c)
    Exists nm a c -> onChange tm foldLF (Exists nm <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 c)

    Sigma nm a g  -> onChange tm foldLF (Sigma nm <$> hsubst tm0 v0 st0 a <*> hsubst tm0 (v0+1) st0 g)
    Goal m c      -> onChange tm foldLF (Goal <$> hsubst tm0 v0 st0 m <*> hsubst tm0 v0 st0 c)

-}


{-

         case unfoldLF tm of
           Var v
             | v0 == v   -> do
                   tm0' <- weaken 0 j tm0
                   Changed (return $ Left (tm0', st))
             | v0 <  v   -> Changed (Right <$> (foldLF $! Var $! (v-1)))
             | otherwise -> Unchanged (Right tm)
           Const _       -> Unchanged (Right tm)
           App r1 m2 ->
             case hsubstTm r1 st of
               Unchanged _ ->
                 onChange (Right tm) (\m -> Right <$> foldLF (App r1 m)) (hsubst tm0 v0 st m2)
               m -> do
                 m2' <- hsubst tm0 v0 j st m2
                 m >>= \case
                   Left (unfoldLF -> Lam _ _ m1', SArrow stArg stBody) -> do
                     m' <- hsubst m2' 0 0 stArg m1'
                     Changed (return $ Left (m', stBody))
                   Right r1' ->
                     Changed (Right <$> foldLF (App r1' m2'))
                   _ ->
                     fail "hereditary substitution failed: ill-typed term"
-}


data Prec
  = TopPrec
  | AppLPrec
  | AppRPrec
  | BinderPrec
 deriving (Eq)

data Hyps (f :: Ctx * -> SORT -> *) (c :: Ctx *) where
  HNil   :: Hyps f E
  HCons  :: Hyps f γ -> Quant -> (b -> (String, f γ TYPE)) -> Hyps f (γ ::> b)

lookupHyp :: LFModel f m
          => Hyps f γ
          -> Var γ
          -> (f γ TYPE -> f γ' TYPE)
          -> (String, Quant, f γ' TYPE)
lookupHyp (HCons _ q f) (B b) w =
  let (nm, a) = f b
   in (nm, q, w (weaken a))
lookupHyp (HCons h _ _) (F x) w =
  lookupHyp h x (w . weaken)
lookupHyp HNil _ _ = error "impossible"

lookupVar :: LFModel f m
          => Hyps f γ
          -> Var γ
          -> (String, Quant, f γ TYPE)
lookupVar h v = lookupHyp h v id

getName :: Set String
        -> String
        -> String
getName ss nm = tryName ss (nm : [ nm++show i | i <- [0..] ])
 where
  tryName ss (x:xs)
    | Set.member x ss = tryName ss xs
    | otherwise = x
  tryName _ [] = undefined

freshName :: String
          -> Set String
          -> (String, Set String)
freshName nm nms =
  let nm' = getName nms nm
   in (nm' , Set.insert nm' nms)

extendHyps :: Hyps f γ -> String -> Quant -> f γ TYPE -> Hyps f (γ ::> ())
extendHyps h nm q a = HCons h q (\_ -> (nm,a))

prettyLF
      :: (WFContext γ, LFModel f m)
      => Prec
      -> Set String
      -> Hyps f γ
      -> f γ s
      -> m Doc
prettyLF prec nms hyps x =
  case unfoldLF x of
    Weak x ->
      case hyps of
        HCons h _ _ -> prettyLF prec nms h x
        _ -> error "impossible"

    Type -> return $ text "Type"
    KPi nm a k
      | freeVar (B ()) k -> do
         let (nm',nms') = freshName nm nms
         adoc <- ppLF BinderPrec nms hyps a
         kdoc <- ppLF TopPrec nms' (extendHyps hyps nm' QPi a) k
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> adoc <+> comma <> nest 2 (softline <> kdoc)
      | otherwise -> do
         adoc <- ppLF BinderPrec nms hyps a
         kdoc <- ppLF TopPrec nms (extendHyps hyps "_" QPi (error "unbound name!")) k
         return $ group $ (if prec /= TopPrec then parens else id) $
           align (adoc <+> text "⇒" <> line <> kdoc)
    AType x -> group . (linebreak <>) . hang 2 <$> (ppLF prec nms hyps x)
    TyPi nm a1 a2
      | freeVar (B ()) a2 -> do
         let (nm',nms') = freshName nm nms
         a1doc <- ppLF BinderPrec nms hyps a1
         a2doc <- ppLF TopPrec nms' (extendHyps hyps nm' QPi a1) a2
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> a1doc <> comma <> nest 2 (softline <> a2doc)
      | otherwise -> do
         a1doc <- ppLF BinderPrec nms hyps a1
         a2doc <- ppLF TopPrec nms (extendHyps hyps "_" QPi (error "unbound name!")) a2
         return $! group $ (if prec /= TopPrec then parens else id) $
           (align (a1doc <+> text "⇒" <> softline <> a2doc))
    TyConst x -> return $ pretty x
    TyApp p a -> do
         pdoc <- ppLF AppLPrec nms hyps p
         adoc <- ppLF AppRPrec nms hyps a
         return $! group $ (if prec == AppRPrec then parens else id) $
            (pdoc <> line <> adoc)
    ATerm x
      | prec == TopPrec ->
           group . (linebreak <>) . hang 2 <$> (ppLF prec nms hyps x)
      | otherwise -> hang 2 <$> ppLF prec nms hyps x
    Lam nm a m -> do
         let (nm',nms') = freshName nm nms
         adoc <- ppLF BinderPrec nms hyps a
         mdoc <- ppLF TopPrec nms' (extendHyps hyps nm' QLam a) m
         return $! (if prec /= TopPrec then parens else id) $
           text "λ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> mdoc)
    Const x -> return $ pretty x
    App m1 m2 -> do
         m1doc <- ppLF AppLPrec nms hyps m1
         m2doc <- ppLF AppRPrec nms hyps m2
         return $! group $ (if prec == AppRPrec then parens else id) $
            (m1doc <> line <> m2doc)

    Var v ->
      case hyps of
        HCons _ _ f -> 
          let (nm,_) = f v in return $ text nm
        _ -> error "impossible"

    Unify r1 r2 -> do
         r1doc <- ppLF TopPrec nms hyps r1
         r2doc <- ppLF TopPrec nms hyps r2
         return $ group (r1doc <+> text "=" <> line <> r2doc)

    And [] -> return $ text "⊤"
    And cs -> do
         cs' <- mapM (ppLF TopPrec nms hyps) cs
         return $ align $ cat $ punctuate (text " ∧ ") cs'

    Forall nm a c -> do
         let (nm',nms') = freshName nm nms
         adoc <- ppLF BinderPrec nms hyps a
         cdoc <- ppLF TopPrec nms' (extendHyps hyps nm' QForall a) c
         return $ (if prec /= TopPrec then parens else id) $
           text "∀" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Exists nm a c -> do
         let (nm',nms') = freshName nm nms
         adoc <- ppLF BinderPrec nms hyps a
         cdoc <- ppLF TopPrec nms' (extendHyps hyps nm' QExists a) c
         return $ (if prec /= TopPrec then parens else id) $
           text "∃" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Sigma nm a g -> do
         let (nm',nms') = freshName nm nms
         adoc <- ppLF BinderPrec nms hyps a
         gdoc <- ppLF TopPrec nms' (extendHyps hyps nm' QSigma a) g
         return $ (if prec /= TopPrec then parens else id) $
           text "Σ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> gdoc)

    Goal m c -> do
         mdoc <- ppLF TopPrec nms hyps m
         cdoc <- ppLF TopPrec nms hyps c
         return $ group $
           text "{" <+> mdoc <+> text "|" <> nest 2 (softline <> cdoc <+> text "}")


data Var :: Ctx * -> * where
  F :: Var γ -> Var (γ ::> b)
  B :: b     -> Var (γ ::> b)

deriving instance (Eq (Var γ), Eq b) => Eq (Var (γ::>b))
deriving instance (Ord (Var γ), Ord b) => Ord (Var (γ::>b))
deriving instance (Show (Var γ), Show b) => Show (Var (γ::>b))

data VarSet :: Ctx * -> * where
  VarSetEmpty :: VarSet γ
  VarSetCons  :: VarSet γ -> Set b -> VarSet (γ ::> b)

mergeVarSet :: WFContext γ => VarSet γ -> VarSet γ -> VarSet γ
mergeVarSet VarSetEmpty y = y
mergeVarSet x VarSetEmpty = x
mergeVarSet (VarSetCons v b) (VarSetCons v' b') =
   VarSetCons (mergeVarSet v v') (Set.union b b')

singleVarSet :: WFContext γ => Var γ -> VarSet γ
singleVarSet (F f) = VarSetCons (singleVarSet f) Set.empty
singleVarSet (B b) = VarSetCons VarSetEmpty (Set.singleton b)

emptyVarSet :: VarSet γ
emptyVarSet = VarSetEmpty

inVarSet :: WFContext γ => VarSet γ -> Var γ -> Bool
inVarSet VarSetEmpty _ = False
inVarSet (VarSetCons s _) (F v) = inVarSet s v
inVarSet (VarSetCons _ s) (B b) = Set.member b s

freeVars :: (WFContext γ, LFModel f m)
         => f γ s
         -> VarSet γ
freeVars = foldFree mergeVarSet emptyVarSet singleVarSet 

freeVar :: (WFContext γ, LFModel f m) => Var γ -> f γ s -> Bool
freeVar v tm = inVarSet (freeVars tm) v


foldFree :: forall f m γ a s
          . LFModel f m
         => (a -> a -> a)
         -> a
         -> (Var γ -> a)
         -> f γ s
         -> a
foldFree merge z = go
 where
  go :: forall γ s. (Var γ -> a) -> f γ s -> a
  go f tm =
    let f' :: forall b. (Var (γ ::> b) -> a)
        f' (B _) = z
        f' (F x) = f x
     in
    case unfoldLF tm of
      Weak x -> go (f . F) x
      Type -> z
      KPi _ a k -> go f a `merge` go f' k
      AType x -> go f x
      TyPi _ a1 a2 -> go f a1 `merge` go f' a2
      TyConst _ -> z
      TyApp p a -> go f p `merge` go f a  
      Lam _ a m -> go f a `merge` go f' m
      Const _ -> z
      ATerm x -> go f x
      App r m -> go f r `merge` go f m
      Var v -> f (B v)
      Unify r1 r2 -> go f r1 `merge` go f r2
      And cs -> foldr merge z $ map (go f) cs
      Forall _ a c -> go f a `merge` go f' c
      Exists _ a c -> go f a `merge` go f' c
      Sigma _ a g -> go f a `merge` go f' g
      Goal m c -> go f m `merge` go f c


{-
freeVarLF :: LFModel f a c m
          => Int
          -> f s
          -> Bool
freeVarLF !i tm =
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
    Unify r1 r2 -> freeVar i r1 || freeVar i r2
    And cs -> any (freeVar i) cs
    Forall _ a c -> freeVar i a || freeVar (i+1) c
    Exists _ a c -> freeVar i a || freeVar (i+1) c

    Sigma _ a g -> freeVar i a || freeVar (i+1) g
    Goal m c -> freeVar i m || freeVar i c
-}