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

  Sigma  :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) GOAL) -> LF f γ GOAL
  Goal   :: !(f γ TERM) -> !(f γ CON) -> LF f γ GOAL


weakenHyps :: Hyps f (γ::>b) -> Hyps f γ
weakenHyps (HCons h _ _) = h

data KindView f m γ
 = VType
 | VKPi (forall x.
           (forall γ'. (WFContext (γ'::>()), ?nms :: Set String, ?hyps :: Hyps f (γ'::>()))
                    => (forall s. f γ' s -> f γ s)
                    -> String
                    -> Var (γ'::>())
                    -> f γ' TYPE
                    -> f (γ'::>()) KIND
                    -> x)
           -> x)

kindViewLF :: forall f m γ γ'
            . (WFContext γ', LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
           => (forall s. f γ' s -> f γ s)
           -> f γ' KIND
           -> KindView f m γ
kindViewLF w k =
  case unfoldLF k of
    Weak x -> let ?hyps = weakenHyps ?hyps
               in kindViewLF (w . weaken) x
    Type -> VType
    KPi nm a k -> VKPi $ \cont -> do
       let (nm',nms') = freshName nm ?nms
       let ?nms  = nms'
       let ?hyps = extendHyps ?hyps nm' QPi a
       cont w nm' (B ()) a k

data TypeView f m γ
 = VTyConst (LFTypeConst f) [f γ TERM]
 | VTyPi (forall x.
           (forall   γ'. (WFContext γ', ?nms :: Set String, ?hyps :: Hyps f (γ'::>()))
                      => (forall s. f γ' s -> f γ s)
                      -> String
                      -> Var (γ'::>())
                      -> f γ' TYPE
                      -> f (γ'::>()) TYPE
                      -> x)
           -> x)

typeViewLF :: forall f m γ γ'
            . (WFContext γ', LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
           => (forall s. f γ' s -> f γ s)
           -> f γ' TYPE
           -> TypeView f m γ
typeViewLF w a =
  case unfoldLF a of
    Weak x ->
       let ?hyps = weakenHyps ?hyps
        in typeViewLF (w . weaken) x
    AType p -> go w [] p
    TyPi nm a1 a2 -> VTyPi $ \cont -> do
       let (nm',nms') = freshName nm ?nms
       let ?hyps = extendHyps ?hyps nm' QPi a1
       let ?nms = nms'
       cont w nm' (B ()) a1 a2

  where go :: forall γ γ'
            . WFContext γ'
           => (forall s. f γ' s -> f γ s)
           -> [f γ TERM]
           -> f γ' ATYPE
           -> TypeView f m γ
        go w args x =
          case unfoldLF x of
            Weak x -> go (w . weaken) args x
            TyConst a -> VTyConst a args
            TyApp p m -> go w (w m : args) p

data TermView f m γ
 = VConst (LFConst f) [f γ TERM]
 | VVar (Var γ) [f γ TERM]
 | VLam (forall x.
           (forall   γ'. (WFContext γ', ?nms :: Set String, ?hyps :: Hyps f (γ'::>()))
                      => (forall s. f γ' s -> f γ s)
                      -> String
                      -> Var (γ'::> ())
                      -> f γ' TYPE
                      -> f (γ'::> ()) TERM
                      -> x)
           -> x)

termViewLF :: forall f m γ γ'
            . (WFContext γ', LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ')
           => (forall s. f γ' s -> f γ s)
           -> (Var γ' -> Var γ)
           -> f γ' TERM
           -> TermView f m γ
termViewLF w wv m =
  case unfoldLF m of
    Weak x ->
      let ?hyps = weakenHyps ?hyps
       in termViewLF (w . weaken) (wv . F) x
    ATerm r -> go w wv [] r
    Lam nm a m' -> VLam $ \cont -> do
       let (nm', nms') = freshName nm ?nms
       let ?nms = nms'
       let ?hyps = extendHyps ?hyps nm' QLam a
       cont w nm' (B ()) a m'

 where go :: forall γ γ'
            . WFContext γ'
           => (forall s. f γ' s -> f γ s)
           -> (Var γ' -> Var γ)
           -> [f γ TERM]
           -> f γ' ATERM
           -> TermView f m γ
       go w wv args r =
         case unfoldLF r of
           Weak x   -> go (w . weaken) (wv . F) args x
           Var v    -> VVar (wv (B v)) args
           Const c  -> VConst c args
           App r' m -> go w wv (w m : args) r'


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
  weaken :: f γ s -> f (γ::>b) s

  hsubst :: Subst m f γ γ'
         -> f γ s
         -> m (f γ' s)

  ppLF :: (WFContext γ, ?nms :: Set String, ?hyps :: Hyps f γ)
       => Prec
       -> f γ s
       -> m Doc

  validateKind :: (WFContext γ, ?nms::Set String, ?hyps::Hyps f γ) => f γ KIND  -> m ()
  validateType :: (WFContext γ, ?nms::Set String, ?hyps::Hyps f γ) => f γ TYPE  -> m ()
  inferKind    :: (WFContext γ, ?nms::Set String, ?hyps::Hyps f γ) => f γ ATYPE -> m (f γ KIND)
  inferType    :: (WFContext γ, ?nms::Set String, ?hyps::Hyps f γ) => f γ TERM  -> m (f γ TYPE)
  inferAType   :: (WFContext γ, ?nms::Set String, ?hyps::Hyps f γ) => f γ ATERM -> m (f γ TYPE)
  alphaEq      :: WFContext γ => f γ s -> f γ s -> m Bool
  freeVar      :: WFContext γ => Var γ -> f γ s -> Bool

  constKind :: LFTypeConst f -> m (f E KIND)
  constType :: LFConst f -> m (f E TYPE)

  kindView :: (WFContext γ, ?nms :: Set String, ?hyps :: Hyps f γ)
           => f γ KIND
           -> KindView f m γ

  typeView :: (WFContext γ, ?nms :: Set String, ?hyps :: Hyps f γ)
           => f γ TYPE
           -> TypeView f m γ

  termView :: (WFContext γ, ?nms :: Set String, ?hyps :: Hyps f γ)
           => f γ TERM
           -> TermView f m γ

{-
  underLambda :: f γ TERM
              -> (f γ TERM -> ChangeT m (f γ TERM))
              -> ChangeT m (f γ TERM)
-}


type family CtxAppend γ γ' :: Ctx * where
  CtxAppend γ E = γ
  CtxAppend γ (γ' ::> b) = CtxAppend γ γ' ::> b

type family CtxDiff γ γ' :: Ctx * where
  CtxDiff γ γ = E
  CtxDiff γ (γ' ::> b) = CtxDiff γ γ' ::> b

class (CtxAppend γ diff ~ γ') => AutoWeaken γ diff γ' where
  autoweaken' :: LFModel f m => Proxy diff -> f γ s -> f γ' s

type CtxSub γ γ' = (CtxAppend γ (CtxDiff γ γ') ~ γ', AutoWeaken γ (CtxDiff γ γ') γ')

autoweaken :: forall m f s γ γ'. (CtxSub γ γ', LFModel f m) => f γ s -> f γ' s
autoweaken = autoweaken' (Proxy :: Proxy (CtxDiff γ γ'))

instance AutoWeaken γ E γ where
  autoweaken' _ = id
instance AutoWeaken γ diff γ' => AutoWeaken γ (diff ::> b) (γ' ::> b) where
  autoweaken' _ = weaken . autoweaken' (Proxy :: Proxy diff)

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

displayLF :: (WFContext γ, LFModel f m, ?nms :: Set String, ?hyps::Hyps f γ)
          => f γ s -> m String
displayLF x = show <$> ppLF TopPrec x

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

cExists :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) CON))
        -> m (f γ CON)
cExists nm tp f = do
    tp' <- tp
    k   <- f (B ())
    foldLF (Exists nm tp' k)

cForall :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) CON))
        -> m (f γ CON)
cForall nm tp f = do
    tp' <- tp
    k   <- f (B ())
    foldLF (Forall nm tp' k)

sigma   :: LFModel f m
        => String
        -> m (f γ TYPE)
        -> (forall b. IsBoundVar b => Var (γ::>b) -> m (f (γ::>b) GOAL))
        -> m (f γ GOAL)
sigma nm tp f = do
    tp' <- tp
    g   <- f (B ())
    foldLF (Sigma nm tp' g)

cTrue :: LFModel f m
      => m (f γ CON)
cTrue = conj []

conj :: forall f m γ
      . LFModel f m
     => [m (f γ CON)]
     -> m (f γ CON)
conj cs = foldLF . And . concat =<< mapM (f =<<) cs
 where f :: f γ CON -> m [f γ CON]
       f (unfoldLF -> (And xs)) = concat <$> mapM f xs
       f x = (:[]) <$> (return x)

goal :: LFModel f m
     => m (f γ TERM)
     -> m (f γ CON)
     -> m (f γ GOAL)
goal m c = foldLF =<< (Goal <$> m <*> c)


unify :: forall f m γ
       . (WFContext γ, LFModel f m)
      => m (f γ TERM)
      -> m (f γ TERM)
      -> m (f γ CON)
unify x y = join (go SubstEnd id SubstEnd id <$> x <*> y)
 where
  go :: forall γ₁ γ₂ γ
      . (WFContext γ, LFModel f m)
     => (Subst m f γ₁ γ)
     -> (Var γ₁ -> Var γ)
     -> (Subst m f γ₂ γ)
     -> (Var γ₂ -> Var γ)
     -> f γ₁ TERM
     -> f γ₂ TERM
     -> m (f γ CON)
  go s₁ wv₁ s₂ wv₂ x y =
   case (unfoldLF x, unfoldLF y) of
     (Weak x', _) -> go (SubstWeak s₁) (wv₁ . F) s₂ wv₂ x' y
     (_, Weak y') -> go s₁ wv₁ (SubstWeak s₂) (wv₂ . F) x y'
     (ATerm r1, ATerm r2) -> do
         q <- alphaEqLF wv₁ wv₂ r1 r2
         if q then
           cTrue
         else
           foldLF =<< Unify <$> hsubst s₁ r1 <*> hsubst s₂ r2
     (Lam nm a1 m1, Lam _ a2 m2) -> do
        q <- alphaEqLF wv₁ wv₂ a1 a2
        unless q (fail "Attempting to unify LF terms with unequal types")
        c <- go (SubstSkip s₁) (mapF wv₁) (SubstSkip s₂) (mapF wv₂) m1 m2
        foldLF =<< Forall nm <$> hsubst s₁ a1 <*> return c
     _ -> fail "Attempting to unify LF terms with unequal types"



{-
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

validateKindLF :: forall f m γ
                . (WFContext γ, LFModel f m, ?nms::Set String, ?hyps::Hyps f γ)
               => f γ KIND
               -> m ()
validateKindLF tm =
  case unfoldLF tm of
    Weak x -> let ?hyps = weakenHyps ?hyps
               in validateKind x
    Type -> return ()
    KPi nm a k -> do
      validateType a
      let (nm',nms') = freshName nm ?nms
      let ?nms = nms'
      let ?hyps = extendHyps ?hyps nm' QPi a
      validateKind k
      {- subordination check -}

validateTypeLF :: forall f m γ
                . (WFContext γ, LFModel f m, ?nms::Set String, ?hyps:: Hyps f γ)
               => f γ TYPE
               -> m ()
validateTypeLF tm =
  case unfoldLF tm of
    Weak x -> let ?hyps = weakenHyps ?hyps
               in validateType x
    TyPi nm a1 a2 -> do
      validateType a1
      let (nm',nms') = freshName nm ?nms
      let ?nms = nms'
      let ?hyps = extendHyps ?hyps nm' QPi a1
      validateType a2

    AType p ->
      checkK =<< inferKind p

 where
  checkK :: forall γ. f γ KIND -> m ()
  checkK k =
   case unfoldLF k of
      Weak k' -> checkK k'
      Type -> return ()
      KPi _ _ _ -> fail "invalid atomic type"

inferKindLF :: forall f m γ
             . (WFContext γ, LFModel f m, ?nms::Set String, ?hyps::Hyps f γ)
            => f γ ATYPE
            -> m (f γ KIND)
inferKindLF tm =
  case unfoldLF tm of
    Weak x -> let ?hyps = weakenHyps ?hyps
               in weaken <$> inferKind x
    TyConst x -> constKind x
    TyApp p1 m2 -> do
      k <- inferKind p1
      subK ?hyps SubstEnd id k m2

 where
  subK :: forall γ'. WFContext γ'
       => Hyps f γ'
       -> Subst m f γ' γ
       -> (f γ' TYPE -> f γ TYPE)
       -> f γ' KIND
       -> f γ TERM
       -> m (f γ KIND)
  subK h s w k m =
     case unfoldLF k of
       Weak x -> subK (weakenHyps h) (SubstWeak s) (w . weaken) x m
       KPi _ a2 k1 -> do
         checkType tm m (w a2)
         hsubst (SubstApply s (\_ -> return m)) k1
       _ -> do
         kdoc <- let ?hyps = h in displayLF k
         fail $ unwords ["invalid atomic type family", kdoc]

checkType :: (WFContext γ, LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
          => f γ s
          -> f γ TERM
          -> f γ TYPE
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


inferTypeLF :: forall f m γ
             . (WFContext γ, LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
            => f γ TERM
            -> m (f γ TYPE)
inferTypeLF m =
  case unfoldLF m of
    Weak x -> let ?hyps = weakenHyps ?hyps
               in weaken <$> inferType x
    ATerm r -> do
      a <- inferAType r
      checkTp ?hyps a
      return a

    Lam nm a2 m -> do
      let (nm',nms') = freshName nm ?nms
      let ?nms = nms'
      let ?hyps = extendHyps ?hyps nm' QLam a2
      a1 <- inferType m
      foldLF (TyPi nm a2 a1)

 where
  checkTp :: forall γ'. WFContext γ' => Hyps f γ' -> f γ' TYPE -> m ()
  checkTp h a =
     case unfoldLF a of
       Weak x -> checkTp (weakenHyps h) x
       AType _ -> return ()
       TyPi _ _ _ -> do
           mdoc <- displayLF m
           adoc <- let ?hyps = h in displayLF a
           fail $ unlines ["Term fails to be η-long:"
                          , mdoc ++ " ::"
                          , adoc
                          ]

inferATypeLF :: forall m f γ
              . (WFContext γ, LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ)
             => f γ ATERM
             -> m (f γ TYPE)
inferATypeLF r =
  case unfoldLF r of
    Weak x -> let ?hyps = weakenHyps ?hyps
               in weaken <$> inferAType x
    Var b -> do
      let (_,_,a) = lookupVar ?hyps (B b)
      return a
    Const c -> constType c
    App r1 m2 -> do
      a <- inferAType r1
      checkArg m2 id SubstEnd a

 where
  checkArg :: forall γ'. WFContext γ'
           => f γ TERM
           -> (f γ' TYPE -> f γ TYPE)
           -> Subst m f γ' γ
           -> f γ' TYPE
           -> m (f γ TYPE)
  checkArg m2 w s a =
      case unfoldLF a of
        Weak x ->
          checkArg m2 (w . weaken) (SubstWeak s) x
        TyPi _ a2 a1 -> do
          checkType r m2 (w a2)
          hsubst (SubstApply s (\() -> return m2)) a1
        _ -> do
          adoc <- displayLF (w a)
          fail $ unwords ["Expected function type", adoc]

data Subst m f :: Ctx * -> Ctx * -> * where
  SubstEnd   :: Subst m f γ γ
  SubstApply :: Subst m f γ γ' -> (b -> m (f γ' TERM)) -> Subst m f (γ ::> b) γ'
  SubstWeak  :: Subst m f (γ ::> b) γ' -> Subst m f γ γ'
  SubstSkip  :: Subst m f γ γ' -> Subst m f (γ ::> b) (γ' ::> b)

hsubstLF :: forall f m s γ γ'
          . LFModel f m
         => Subst m f γ γ'
         -> f γ s
         -> m (f γ' s)
hsubstLF SubstEnd tm = return tm
hsubstLF (SubstWeak s) tm = hsubst s (weaken tm)
hsubstLF sub tm =
  case unfoldLF tm of
     Weak x ->
       case sub of
         SubstEnd       -> return tm
         SubstWeak s    -> hsubst s (weaken tm)
         SubstSkip s    -> weaken <$> hsubst s x
         SubstApply s _ -> hsubst s x

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
        r1' <- f =<< hsubstTm sub r1
        r2' <- f =<< hsubstTm sub r2
        foldLF (Unify r1' r2')

     Forall nm a c -> foldLF =<< (Forall nm <$> hsubst sub a <*> hsubst sub' c)
     Exists nm a c -> foldLF =<< (Exists nm <$> hsubst sub a <*> hsubst sub' c)

     Sigma nm a g  -> foldLF =<< (Sigma nm <$> hsubst sub a <*> hsubst sub' g)
     Goal m c      -> foldLF =<< (Goal <$> hsubst sub m <*> hsubst sub c)

     ATerm x      -> either return (foldLF . ATerm) =<< hsubstTm sub x
     Const _      -> f =<< hsubstTm sub tm
     Var _        -> f =<< hsubstTm sub tm
     App _ _      -> f =<< hsubstTm sub tm

 where
  sub' :: forall b. Subst m f (γ ::> b) (γ' ::> b)
  sub' = SubstSkip sub

  f :: Either (f γ' TERM) (f γ' ATERM) -> m (f γ' ATERM)
  f (Left (unfoldLF -> ATerm r)) = return r
  f (Right r) = return r
  f _ = fail "hereditary substitution failed: expected ATERM result"

{- FIXME? rewrite this in continuation passing form
    to avoid repeated matching on Either values. -}
hsubstTm :: forall m f γ γ'
          . (LFModel f m)
         => Subst m f γ γ'
         -> f γ ATERM
         -> m (Either (f γ' TERM) (f γ' ATERM))
hsubstTm SubstEnd tm = return (Right tm)
hsubstTm (SubstWeak s) tm = hsubstTm s (weaken tm)
hsubstTm sub tm =
         case unfoldLF tm of
           Weak x ->
             case sub of
               SubstEnd       -> return (Right tm)
               SubstWeak s    -> hsubstTm s (weaken tm)
               SubstApply s _ -> hsubstTm s x
               SubstSkip s -> do
                   x' <- hsubstTm s x
                   return $ either (Left . weaken) (Right . weaken) x'

           Var v ->
             case sub of
               SubstEnd       -> return $ Right tm
               SubstWeak s    -> hsubstTm s (weaken tm)
               SubstApply _ f -> Left <$> f v
               SubstSkip _    -> Right <$> foldLF (Var v)

           Const _ ->
             case sub of
               SubstEnd -> return $ Right tm
               SubstWeak s -> hsubstTm s (weaken tm)
               _ -> error "impossible"

           App r1 m2 -> do
             r1' <- hsubstTm sub r1
             m2' <- hsubst sub m2
             case r1' of
               Left m1' ->
                 Left <$> gosub1 m1' m2'
               Right r1'' ->
                 Right <$> foldLF (App r1'' m2')

 where
  gosub1 :: forall γ. f γ TERM -> f γ TERM -> m (f γ TERM)
  gosub1 x y =
   case (unfoldLF x, unfoldLF y) of
     (Weak x', Weak y') -> weaken <$> gosub1 x' y'
     _ -> gosub2 x y SubstEnd

  gosub2 :: forall γ γ'. f γ TERM
                      -> f γ' TERM
                      -> (Subst m f γ γ')
                      -> m (f γ' TERM)
  gosub2 x y s =
    case unfoldLF x of
      Weak x'   -> gosub2 x' y (SubstWeak s)
      Lam _ _ m -> hsubst (SubstApply s (\_ -> return y)) m
      _ -> fail "hereditary substitution failed: ill-typed term"


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
      :: (WFContext γ, LFModel f m, ?nms::Set String, ?hyps::Hyps f γ)
      => Prec
      -> f γ s
      -> m Doc
prettyLF prec x =
  case unfoldLF x of
    Weak x -> let ?hyps = weakenHyps ?hyps
               in prettyLF prec x
    Type -> return $ text "Type"
    KPi nm a k
      | freeVar (B ()) k -> do
         let (nm',nms') = freshName nm ?nms
         adoc <- ppLF BinderPrec a
         let ?nms = nms'
         let ?hyps = extendHyps ?hyps nm' QPi a
         kdoc <- ppLF TopPrec k
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> adoc <+> comma <> nest 2 (softline <> kdoc)
      | otherwise -> do
         adoc <- ppLF BinderPrec a
         let ?hyps = extendHyps ?hyps "_" QPi (error "unbound name!")
         kdoc <- ppLF TopPrec k
         return $ group $ (if prec /= TopPrec then parens else id) $
           align (adoc <+> text "⇒" <> line <> kdoc)
    AType x -> group . (linebreak <>) . hang 2 <$> (ppLF prec x)
    TyPi nm a1 a2
      | freeVar (B ()) a2 -> do
         let (nm',nms') = freshName nm ?nms
         a1doc <- ppLF BinderPrec a1
         let ?nms = nms'
         let ?hyps = extendHyps ?hyps nm' QPi a1
         a2doc <- ppLF TopPrec a2
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> a1doc <> comma <> nest 2 (softline <> a2doc)
      | otherwise -> do
         a1doc <- ppLF BinderPrec a1
         let ?hyps = extendHyps ?hyps "_" QPi (error "unbound name!")
         a2doc <- ppLF TopPrec a2
         return $! group $ (if prec /= TopPrec then parens else id) $
           (align (a1doc <+> text "⇒" <> softline <> a2doc))
    TyConst x -> return $ pretty x
    TyApp p a -> do
         pdoc <- ppLF AppLPrec p
         adoc <- ppLF AppRPrec a
         return $! group $ (if prec == AppRPrec then parens else id) $
            (pdoc <> line <> adoc)
    ATerm x
      | prec == TopPrec ->
           group . (linebreak <>) . hang 2 <$> (ppLF prec x)
      | otherwise -> hang 2 <$> ppLF prec x
    Lam nm a m -> do
         let (nm',nms') = freshName nm ?nms
         adoc <- ppLF BinderPrec a
         let ?nms = nms'
         let ?hyps = extendHyps ?hyps nm' QLam a
         mdoc <- ppLF TopPrec m
         return $! (if prec /= TopPrec then parens else id) $
           text "λ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> mdoc)
    Const x -> return $ pretty x
    App m1 m2 -> do
         m1doc <- ppLF AppLPrec m1
         m2doc <- ppLF AppRPrec m2
         return $! group $ (if prec == AppRPrec then parens else id) $
            (m1doc <> line <> m2doc)
    Var v -> 
      let (nm,_,_) = lookupVar ?hyps (B v)
       in return $ text nm

    Unify r1 r2 -> do
         r1doc <- ppLF TopPrec r1
         r2doc <- ppLF TopPrec r2
         return $ group (r1doc <+> text "=" <> line <> r2doc)

    And [] -> return $ text "⊤"
    And cs -> do
         cs' <- mapM (ppLF TopPrec) cs
         return $ align $ cat $ punctuate (text " ∧ ") cs'

    Forall nm a c -> do
         let (nm',nms') = freshName nm ?nms
         adoc <- ppLF BinderPrec a
         let ?nms = nms'
         let ?hyps = extendHyps ?hyps nm' QForall a
         cdoc <- ppLF TopPrec c
         return $ (if prec /= TopPrec then parens else id) $
           text "∀" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Exists nm a c -> do
         let (nm',nms') = freshName nm ?nms
         adoc <- ppLF BinderPrec a
         let ?nms = nms'
         let ?hyps = extendHyps ?hyps nm' QExists a
         cdoc <- ppLF TopPrec c
         return $ (if prec /= TopPrec then parens else id) $
           text "∃" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Sigma nm a g -> do
         let (nm',nms') = freshName nm ?nms
         adoc <- ppLF BinderPrec a
         let ?nms = nms'
         let ?hyps = extendHyps ?hyps nm' QSigma a
         gdoc <- ppLF TopPrec g
         return $ (if prec /= TopPrec then parens else id) $
           text "Σ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> gdoc)

    Goal m c -> do
         mdoc <- ppLF TopPrec m
         cdoc <- ppLF TopPrec c
         return $ group $
           text "{" <+> mdoc <+> text "|" <> nest 2 (softline <> cdoc <+> text "}")


data Var :: Ctx * -> * where
  F :: Var γ -> Var (γ ::> b)
  B :: b     -> Var (γ ::> b)

instance (Eq (Var E)) where
  _ == _ = error "impossible"
instance (Ord (Var E)) where
  compare _ _ = error "impossible"
instance (Show (Var E)) where
  show _ = error "impossible"

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

freeVarLF :: (WFContext γ, LFModel f m) => Var γ -> f γ s -> Bool
freeVarLF v tm = inVarSet (freeVars tm) v

freeVars :: (WFContext γ, LFModel f m)
         => f γ s
         -> VarSet γ
freeVars = foldFree mergeVarSet emptyVarSet singleVarSet

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
