{-# LANGUAGE UndecidableInstances #-}
module Lang.LF.Internal.Model where

--import GHC.Exts ( Constraint )

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

  Type   :: LF f γ KIND
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

  Fail   :: LF f γ CON
  Unify  :: !(f γ ATERM) -> !(f γ ATERM) -> LF f γ CON
  UnifyVar :: LFUVar f -> !(f γ ATERM) -> LF f γ CON
  And    :: [f γ CON] -> LF f γ CON
  Forall :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON
  Exists :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON

  Sigma  :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) GOAL) -> LF f γ GOAL
  Goal   :: !(f γ TERM) -> !(f γ CON) -> LF f γ GOAL


-- | A sequence of hypotheses, giving types to the free variables in γ.
data Hyps (f :: Ctx * -> SORT -> *) (γ :: Ctx *) where
  HNil   :: Hyps f E
  HCons  :: Hyps f γ -> Quant -> String -> f γ TYPE -> Hyps f (γ ::> b)

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

-- | A substituion from γ to γ' represents a function that
--   sends a term in context γ to one in context γ' that
--   assigns variables in γ to terms with free variables in γ'.
--   This particular syntactic form of substituions is tailored
--   to the structure of the hereditary substituion algorithm
--   and allows us to recognize certain situations where we can stop early
--   and avoid traversing subtrees.
data Subst f :: Ctx * -> Ctx * -> * where
  SubstRefl  :: Subst f γ γ
  SubstApply :: Subst f γ γ' -> f γ' TERM -> Subst f (γ ::> b) γ'
  SubstWeak  :: Weakening γ₁ γ₂ -> Subst f γ₂ γ₃ -> Subst f γ₁ γ₃
  SubstSkip  :: Subst f γ γ' -> Subst f (γ ::> b) (γ' ::> b)

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
 VLam   :: forall f m γ
         . (?nms :: Set String, ?hyps :: Hyps f (γ ::> ()))
        => String
        -> Var (γ::> ())
        -> f γ TYPE
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
 VUnifyVar :: LFUVar f -> f γ TERM -> ConstraintView f m γ
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
         => Subst f γ γ'
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
  assignUVar :: Proxy f -> LFUVar f -> f E TERM -> LFSoln f -> m (LFSoln f)
  freshUVar :: f E TYPE -> m (LFUVar f)
  extendSolution :: LFUVar f -> f E TERM -> LFSoln f -> Maybe (LFSoln f)

  instantiate :: (?soln :: LFSoln f)
              => f γ s -> ChangeT m (f γ s)

  solve :: f E CON -> m (f E CON, LFSoln f)
