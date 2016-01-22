{-# LANGUAGE UndecidableInstances #-}
module Lang.LF.Internal.Model where

import GHC.Exts ( Constraint )

import           Data.Proxy
import           Data.Set (Set)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF.ChangeT

--import qualified Debug.Trace as Debug

-- | Datakind used to classify the syntactic categories of LF.
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

-- | Indicates, in a context, what type of quantifier originaly gave
--   rise to the accompaning variable.
data Quant
  = QPi
  | QLam
  | QSigma
  | QForall
  | QExists
 deriving (Eq, Ord, Show)

-- | Datakind used to track the free variables in scope in an LF term
data Ctx k = E | Ctx k ::> k

-- | The type used to indicate LF type-level constants
type family LFTypeConst (f :: Ctx * -> SORT -> *) :: *

-- | The type used to indicate LF term-level constants
type family LFConst (f :: Ctx * -> SORT -> *) :: *

-- | The type used to represent unification variables
type family LFUVar (f :: Ctx * -> SORT -> *) :: *

-- | The type used to represent solutions to constraints; these
--   indicate how to set the values of unification variables
type family LFSoln (f :: Ctx * -> SORT -> *) :: *

-- | The syntax algebra of canonical LF terms, parameterized
--   by `γ`, a context of free variables and `s` the syntactic sort
--   of the term.
data LF (f :: Ctx * -> SORT -> *) :: Ctx * -> SORT -> * where
  Weak   :: Weakening γ γ' -> f γ s -> LF f γ' s

  Type   :: LF f E KIND
  KPi    :: !String -> !(f γ TYPE) -> f (γ ::> ()) KIND -> LF f γ KIND

  AType   :: !(f γ ATYPE) -> LF f γ TYPE
  TyPi    :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) TYPE) -> LF f γ TYPE
  TyConst :: !(LFTypeConst f) -> LF f E ATYPE
  TyApp   :: !(f γ ATYPE) -> !(f γ TERM) -> LF f γ ATYPE

  ATerm  :: !(f γ ATERM) -> LF f γ TERM
  Lam    :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) TERM) -> LF f γ TERM
  Var    :: LF f (γ ::> b) ATERM
  Const  :: !(LFConst f) -> LF f E ATERM
  App    :: !(f γ ATERM) -> !(f γ TERM) -> LF f γ ATERM
  UVar   :: LFUVar f -> LF f E ATERM

  Fail   :: LF f E CON
  Unify  :: !(f γ ATERM) -> !(f γ ATERM) -> LF f γ CON
  And    :: [f γ CON] -> LF f γ CON
  Forall :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON
  Exists :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON

  Sigma  :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) GOAL) -> LF f γ GOAL
  Goal   :: !(f γ TERM) -> !(f γ CON) -> LF f γ GOAL


-- | A sequence of hypotheses, giving types to the free variables in γ.
data Hyps (f :: Ctx * -> SORT -> *) (γ :: Ctx *) where
  HNil   :: Hyps f E
  HCons  :: Hyps f γ -> Quant -> String -> f γ TYPE -> Hyps f (γ ::> b)


type IsBoundVar b = (Show b, Ord b, Eq b)

type family WFContextRec (c::Ctx *) :: Constraint where
  WFContextRec E = ()
  WFContextRec (γ ::> b) = (WFContext γ, IsBoundVar b)

type WFContext γ = (LiftClosed γ, Ord (Var γ), WFContextRec γ)

class LiftClosed (γ :: Ctx *) where
  liftWeakening :: Weakening E γ
  liftClosed :: LFModel f m => f E s -> f γ s
  liftClosed = weaken liftWeakening

instance LiftClosed E where
  liftWeakening = WeakRefl
instance LiftClosed γ => LiftClosed (γ ::> b) where
  liftWeakening = WeakR liftWeakening

data Prec
  = TopPrec
  | AppLPrec
  | AppRPrec
  | BinderPrec
 deriving (Eq)


data Var :: Ctx * -> * where
  F :: Var γ -> Var (γ ::> b)
  B ::          Var (γ ::> b)

instance Show (Var γ) where
 showsPrec _d B = ("B" ++)
 showsPrec d (F v) = showParen (d > 10) $ showString "F " . showsPrec 11 v

eqVar :: Var γ -> Var γ -> Bool
eqVar B B = True
eqVar (F x) (F y) = eqVar x y
eqVar B (F _) = False
eqVar (F _) B = False

compareVar :: Var γ -> Var γ -> Ordering
compareVar B B = EQ
compareVar B (F _) = LT
compareVar (F x) (F y) = compareVar x y
compareVar (F _) B = GT

instance Eq (Var γ) where
  (==) = eqVar
instance Ord (Var γ) where
  compare = compareVar

-- | A weakening from γ to γ' represents a function that
--   sends a term in context γ to one in context γ' that
--   operates entirely by inserting new, unreferenced free
--   variables.
data Weakening γ γ' where
  WeakRefl  :: Weakening γ γ
  WeakR     :: Weakening γ γ' -> Weakening γ (γ'::>b)
  WeakL     :: Weakening (γ::>b) γ' -> Weakening γ γ'
  WeakSkip  :: Weakening γ γ' -> Weakening (γ::>b) (γ'::>b)

weakCtx :: WFContext γ'
        => Weakening γ γ'
        -> ((WFContext γ) => x)
        -> x
weakCtx WeakRefl k = k
weakCtx (WeakR w) k = weakCtx w k
weakCtx (WeakL w) k = weakCtx w k
weakCtx (WeakSkip w) k = weakCtx w k

weakenVar :: Weakening γ γ'
          -> Var γ
          -> Var γ'
weakenVar WeakRefl  = id
weakenVar (WeakR w) = F . weakenVar w
weakenVar (WeakL w) = weakenVar w . F
weakenVar (WeakSkip w) = mapF (weakenVar w)

-- Smart constructor.  Replaces (WeakSkip WeakRefl) with WeakRefl
-- Correctness follows from functor/identity law:
--    mapF 1 = 1
weakSkip :: Weakening γ γ' -> Weakening (γ::>b) (γ'::>b)
weakSkip WeakRefl = WeakRefl
weakSkip w        = WeakSkip w

weakTrans :: Weakening γ₁ γ₂
          -> Weakening γ₂ γ₃
          -> Weakening γ₁ γ₃

weakTrans w₁ WeakRefl = w₁
 -- by identity
 --    w₁ ∘ 1 = w₁

weakTrans w₁ (WeakR w₂) = WeakR (weakTrans w₁ w₂)
 -- by associativity
 --    w₁ ∘ (w₂ ∘ weak) = (w₁ ∘ w₂) ∘ weak

weakTrans w₁ (WeakL w₂) = weakTrans (WeakR w₁) w₂
 -- by associativity
 --    w₁ ∘ (weak ∘ w₂) = (w₁ ∘ weak) ∘ w₂
 --
 -- Note: This is the only recursive rule that does not decrease both
 --       arguments.  Termination can be proved via lexicographic
 --       order that decreases w₂ then w₁.

weakTrans WeakRefl w₂ = w₂
 -- by identity
 --    1 ∘ w₂ = w₂

weakTrans (WeakL w₁) w₂ = WeakL (weakTrans w₁ w₂)
 -- by associativity
 --  (weak ∘ w₁) ∘ w₂ = weak ∘ (w₁ ∘ w₂)

weakTrans (WeakR w₁) (WeakSkip w₂) = WeakR (weakTrans w₁ w₂)
 -- by naturality of one-step weakening and assocativity
 --   (w₁ ∘ weak) ∘ mapF w₂
 --    = w₁ ∘ (weak ∘ mapF w₂)
 --    = w₁ ∘ (w₂ ∘ weak)
 --    = (w₁ ∘ w₂) ∘ weak

weakTrans (WeakSkip w₁) (WeakSkip w₂) = WeakSkip (weakTrans w₁ w₂)
 -- by functor law for mapF
 --     mapF w₁ ∘ mapF w₂ = mapF (w₁ ∘ w₂)


weakNormalize :: Weakening γ γ'
              -> Weakening γ γ'
weakNormalize WeakRefl             = WeakRefl
weakNormalize (WeakR w)            = WeakR (weakNormalize w)
weakNormalize (WeakSkip w)         = weakSkip (weakNormalize w)
weakNormalize (WeakL WeakRefl)     = WeakR WeakRefl
weakNormalize (WeakL (WeakR w))    = WeakR (weakNormalize (WeakL w))
weakNormalize (WeakL (WeakSkip w)) = WeakR (weakNormalize w)
weakNormalize (WeakL (WeakL w))    = weakNormalize (WeakL (weakNormalize (WeakL w)))

mergeWeak :: Weakening γ₁ γ
          -> Weakening γ₂ γ
          -> (forall γ'. Weakening γ' γ -> Weakening γ₁ γ' -> Weakening γ₂ γ' -> x)
          -> x
mergeWeak WeakRefl w₂ k = k WeakRefl WeakRefl w₂
mergeWeak w₁ WeakRefl k = k WeakRefl w₁ WeakRefl

mergeWeak (WeakR w₁) (WeakR w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k (WeakR w) w₁' w₂'

mergeWeak (WeakSkip w₁) (WeakSkip w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k (weakSkip w) (weakSkip w₁') (weakSkip w₂')

mergeWeak (WeakL w₁) (WeakL w₂) k =
  mergeWeak w₁ w₂ $ \w w₁' w₂' ->
    k w (WeakL w₁') (WeakL w₂')

mergeWeak w₁ w₂ k =
  k WeakRefl w₁ w₂

-- | A substituion from γ to γ' represents a function that
--   sends a term in context γ to one in context γ' that
--   assigns variables in γ to terms with free variables in γ'.
--   This particular syntactic form of substituions is tailored
--   to the structure of the hereditary substituion algorithm
--   and allows us to recognize certain situations where we can stop early
--   and avoid traversing subtrees.
data Subst m f :: Ctx * -> Ctx * -> * where
  SubstRefl  :: Subst m f γ γ
  SubstApply :: Subst m f γ γ' -> f γ' TERM -> Subst m f (γ ::> b) γ'
  SubstWeak  :: Weakening γ₁ γ₂ -> Subst m f γ₂ γ₃ -> Subst m f γ₁ γ₃
  SubstSkip  :: Subst m f γ γ' -> Subst m f (γ ::> b) (γ' ::> b)

-- | This datastructure represents the ways a canonical LF kind can be viewed.
--   A kind is either the constant 'type' or a Π binder.
data KindView f m γ where
 VType :: KindView f m γ
 VKPi :: forall f m γ
       . (?nms :: Set String, ?hyps :: Hyps f (γ::>()))
      => String
      -> Var (γ::>())
      -> f γ TYPE
      -> f (γ::>()) KIND
      -> KindView f m γ

-- | This datastructure represents the ways a canonical LF type family can be viewed.
--   A type is either a type constant applied to a sequence of arguments or
--   a Π binder.
data TypeView f m γ where
 VTyConst :: LFTypeConst f -> [f γ TERM] -> TypeView f m γ
 VTyPi :: forall f m γ
        . (?nms :: Set String, ?hyps :: Hyps f (γ::>()))
       => String
       -> Var (γ::>())
       -> f γ TYPE
       -> f (γ::>()) TYPE
       -> TypeView f m γ

-- | This datastructure represents the ways a canonical LF term can be viewed.
--   A term is either a term constant applied to a sequence of arguments; a free
--   variable applied to a sequence of arguments; a unification variable applied
--   to a sequence of arguments; or a λ term.
data TermView f m γ where
 VConst :: LFConst f -> [f γ TERM] -> TermView f m γ
 VVar   :: Var γ -> [f γ TERM] -> TermView f m γ
 VUVar  :: LFUVar f -> [f γ TERM] -> TermView f m γ
 VLam   :: forall f m γ γ'
         . (?nms :: Set String, ?hyps :: Hyps f (γ ::> ()))
        => String
        -> Var (γ::> ())
        -> f γ' TYPE
        -> f (γ::> ()) TERM
        -> TermView f m γ

-- | This datastructure represents the ways an LF constraint can be viewed.
--   A constraint is either the failure state; a conjunction of constraints;
--   a unification goal; a ∀ quantifier; or a ∃ quantifier.  In the binder cases,
--   continuations are provided that allow access to the subterms.
data ConstraintView f m γ where
 VFail :: ConstraintView f m γ
 VAnd  :: [f γ CON] -> ConstraintView f m γ
 VUnify :: f γ TERM -> f γ TERM -> ConstraintView f m γ
 VForall :: forall f m γ
          . (?nms :: Set String, ?hyps :: Hyps f (γ::>()))
         => String
         -> Var (γ::> ())
         -> f γ TYPE
         -> f (γ::> ()) CON
         -> ConstraintView f m γ
 VExists :: forall f m γ
          . (?nms :: Set String, ?hyps :: Hyps f (γ::>()))
         => String
         -> Var (γ::> ())
         -> f γ TYPE
         -> f (γ::> ()) CON
         -> ConstraintView f m γ


-- | This datastructure represents the ways a canonical LF term can be viewed.
--   A term is either a goal (consisting of a term and constraints) or is
--   a Σ binder. In the binder case,
--   a continuation is provided that allows access to the subterm.
data GoalView f m γ where
 VGoal :: f γ TERM -> f γ CON -> GoalView f m γ
 VSigma  :: forall f m γ
          . (?nms :: Set String, ?hyps :: Hyps f (γ::>()))
         => String
         -> Var (γ::> ())
         -> f γ TYPE
         -> f (γ::> ()) GOAL
         -> GoalView f m γ

class (Ord (LFTypeConst f), Ord (LFConst f), Ord (LFUVar f),
       Pretty (LFTypeConst f), Pretty (LFConst f), Pretty (LFUVar f),
       Monad m)
  => LFModel (f :: Ctx * -> SORT -> *) m | f -> m, m -> f where

  unfoldLF :: f γ s -> LF f γ s
  foldLF :: LF f γ s -> m (f γ s)
  weaken :: Weakening γ γ' -> f γ s -> f γ' s
  aterm :: f γ ATERM -> f γ TERM
  atype :: f γ ATYPE -> f γ TYPE

  hsubst :: (?soln :: LFSoln f)
         => Subst m f γ γ'
         -> f γ s
         -> m (f γ' s)

  ppLF :: (?nms :: Set String, ?hyps :: Hyps f γ', ?soln :: LFSoln f)
       => Prec
       -> Weakening γ γ'
       -> f γ s
       -> m Doc

  validateKind :: (?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ KIND  -> m ()

  validateType :: (?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ TYPE  -> m ()

  inferKind    :: (?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ ATYPE -> m (f γ' KIND)

  inferType    :: (?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ TERM  -> m (f γ' TYPE)

  inferAType   :: (?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ ATERM -> m (f γ' TYPE)

  validateGoal :: (?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ GOAL  -> m ()

  validateCon  :: (?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ CON   -> m ()

  alphaEq      :: (?soln :: LFSoln f) => f γ s -> f γ s -> Bool
  varCensus    :: (?soln :: LFSoln f) => Var γ -> f γ s -> Int
  freeVar      :: (?soln :: LFSoln f) => Var γ -> f γ s -> Bool

  constKind :: LFTypeConst f -> m (f E KIND)
  constType :: LFConst f -> m (f E TYPE)
  uvarType  :: LFUVar f -> m (f E TYPE)

  kindView :: (?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ KIND
           -> KindView f m γ

  typeView :: (?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ TYPE
           -> TypeView f m γ

  termView :: (?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ TERM
           -> TermView f m γ

  constraintView :: (?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ CON
           -> ConstraintView f m γ

  goalView :: (?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ GOAL
           -> GoalView f m γ

  withCurrentSolution :: ((?soln :: LFSoln f) => m x) -> m x
  commitSolution :: LFSoln f -> m ()
  lookupUVar :: Proxy f -> LFUVar f -> LFSoln f -> Maybe (f E TERM)
  freshUVar :: f E TYPE -> m (LFUVar f)
  extendSolution :: LFUVar f -> f E TERM -> LFSoln f -> m (Maybe (LFSoln f))

  instantiate :: (?soln :: LFSoln f)
              => f γ s -> ChangeT m (f γ s)

  solve :: f E CON -> m (f E CON, LFSoln f)

weak :: LFModel f m
     => f γ s
     -> f (γ::>b) s
weak = weaken (WeakR WeakRefl)

mapF :: (Var γ -> Var γ') -> Var (γ ::> b) -> Var (γ' ::> b)
mapF _ B = B
mapF f (F x) = F (f x)

alphaEqLF :: LFModel f m
          => Weakening γ₁ γ
          -> Weakening γ₂ γ
          -> f γ₁ s
          -> f γ₂ s
          -> Bool
alphaEqLF w₁ w₂ x y =
  case (unfoldLF x, unfoldLF y) of
    (Weak w x'   , _)              -> alphaEqLF (weakTrans w w₁) w₂ x' y
    (_           , Weak w y')      -> alphaEqLF w₁ (weakTrans w w₂) x y'
    (Type        , Type)           -> True
    (KPi _ a k   , KPi _ a' k')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) k k')
    (AType x     , AType x')       -> alphaEqLF w₁ w₂ x x'
    (TyPi _ a1 a2, TyPi _ a1' a2') -> (&&) (alphaEqLF w₁ w₂ a1 a1') (alphaEqLF (weakSkip w₁) (weakSkip w₂) a2 a2')
    (TyConst x   , TyConst x')     -> x == x'
    (TyApp a m   , TyApp a' m')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF w₁ w₂ m m')
    (ATerm x     , ATerm x')       -> alphaEqLF w₁ w₂ x x'
    (Lam _ a m   , Lam _ a' m')    -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) m m')
    (Var         , Var)            -> weakenVar w₁ B == weakenVar w₂ B
    (UVar u      , UVar u')        -> u == u'
    (Const x     , Const x')       -> x == x'
    (App r m     , App r' m')      -> (&&) (alphaEqLF w₁ w₂ r r') (alphaEqLF w₁ w₂ m m')
    (Unify r1 r2 , Unify r1' r2')  -> (&&) (alphaEqLF w₁ w₂ r1 r1') (alphaEqLF w₁ w₂ r2 r2')
    (And cs      , And cs')        -> and (zipWith (alphaEqLF w₁ w₂) cs cs')
    (Forall _ a c, Forall _ a' c') -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) c c')
    (Exists _ a c, Exists _ a' c') -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) c c')
    (Sigma _ a g , Sigma _ a' g')  -> (&&) (alphaEqLF w₁ w₂ a a') (alphaEqLF (weakSkip w₁) (weakSkip w₂) g g')
    (Goal m c    , Goal m' c')     -> (&&) (alphaEqLF w₁ w₂ m m') (alphaEqLF w₁ w₂ c c')
    _ -> False


data VarSet :: Ctx * -> * where
  VarSetEmpty :: VarSet γ
  VarSetCons  :: VarSet γ -> !Int -> VarSet (γ ::> b)

mergeVarSet :: VarSet γ -> VarSet γ -> VarSet γ
mergeVarSet VarSetEmpty y = y
mergeVarSet x VarSetEmpty = x
mergeVarSet (VarSetCons v b) (VarSetCons v' b') =
   VarSetCons (mergeVarSet v v') (b + b')

singleVarSet :: Var γ -> VarSet γ
singleVarSet (F f) = VarSetCons (singleVarSet f) 0
singleVarSet B     = VarSetCons VarSetEmpty 1

emptyVarSet :: VarSet γ
emptyVarSet = VarSetEmpty

inVarSet :: VarSet γ -> Var γ -> Bool
inVarSet s v = lookupVarSet s v > 0

lookupVarSet :: VarSet γ -> Var γ -> Int
lookupVarSet VarSetEmpty _ = 0
lookupVarSet (VarSetCons s _) (F v) = lookupVarSet s v
lookupVarSet (VarSetCons _ x) B = x

varCensusLF :: LFModel f m => Var γ -> f γ s -> Int
varCensusLF v tm = lookupVarSet (countCensus tm) v

freeVarLF :: LFModel f m => Var γ -> f γ s -> Bool
freeVarLF v tm = inVarSet (countCensus tm) v

countCensus :: LFModel f m
         => f γ s
         -> VarSet γ
countCensus = foldFree mergeVarSet emptyVarSet singleVarSet

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
        f' B     = z
        f' (F x) = f x
     in
    case unfoldLF tm of
      Weak w x -> go (f . weakenVar w) x
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
      Var -> f B
      Unify r1 r2 -> go f r1 `merge` go f r2
      And cs -> foldr merge z $ map (go f) cs
      Forall _ a c -> go f a `merge` go f' c
      Exists _ a c -> go f a `merge` go f' c
      Sigma _ a g -> go f a `merge` go f' g
      Goal m c -> go f m `merge` go f c
      Fail -> z
      UVar _ -> z
