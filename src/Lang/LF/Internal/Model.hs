{-# LANGUAGE UndecidableInstances #-}
module Lang.LF.Internal.Model where

import           Control.Monad.Identity
import           Data.Proxy
import           Data.Map.Strict (Map)
import           Data.Sequence (Seq)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF.ChangeT

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

-- | The type used to represent record indices
type family LFRecordIndex (f :: Ctx * -> SORT -> *) :: *

-- | The type used to represent solutions to constraints; these
--   indicate how to set the values of unification variables
type family LFSoln (f :: Ctx * -> SORT -> *) :: *

data family Hyps (f :: Ctx * -> SORT -> *) :: Ctx * -> *


data FieldSet f
  = PosFieldSet (Set (LFRecordIndex f)) -- means the set X
  | NegFieldSet (Set (LFRecordIndex f)) -- means the set (Fields - X)

instance LFModel f m => Eq (FieldSet f) where
  (PosFieldSet x) == (PosFieldSet y) = x == y
  (NegFieldSet x) == (NegFieldSet y) = x == y
  _ == _ = False

fieldSetComplement 
  :: LFModel f m => FieldSet f -> FieldSet f
fieldSetComplement (PosFieldSet x) = NegFieldSet x
fieldSetComplement (NegFieldSet x) = PosFieldSet x

fieldSetSubset
  :: LFModel f m => FieldSet f -> FieldSet f -> Bool
fieldSetSubset x y = fieldSetNull (fieldSetDifference x y)

fieldSetDisjoint 
  :: LFModel f m => FieldSet f -> FieldSet f -> Bool
fieldSetDisjoint x y = fieldSetNull (fieldSetIntersection x y)

fieldSetNull 
  :: LFModel f m => FieldSet f -> Bool
fieldSetNull (PosFieldSet x) = Set.null x
fieldSetNull (NegFieldSet _) = False

fieldSetUnion
  :: LFModel f m => FieldSet f -> FieldSet f -> FieldSet f
fieldSetUnion (PosFieldSet x) (PosFieldSet y) = PosFieldSet (Set.union x y)
fieldSetUnion (PosFieldSet x) (NegFieldSet y) = NegFieldSet (Set.difference y x)
fieldSetUnion (NegFieldSet x) (PosFieldSet y) = NegFieldSet (Set.difference x y)
fieldSetUnion (NegFieldSet x) (NegFieldSet y) = NegFieldSet (Set.intersection x y)

fieldSetIntersection
  :: LFModel f m => FieldSet f -> FieldSet f -> FieldSet f
fieldSetIntersection (PosFieldSet x) (PosFieldSet y) = PosFieldSet (Set.intersection x y)
fieldSetIntersection (PosFieldSet x) (NegFieldSet y) = PosFieldSet (Set.difference x y)
fieldSetIntersection (NegFieldSet x) (PosFieldSet y) = PosFieldSet (Set.difference y x)
fieldSetIntersection (NegFieldSet x) (NegFieldSet y) = NegFieldSet (Set.union x y)

fieldSetDifference
  :: LFModel f m => FieldSet f -> FieldSet f -> FieldSet f
fieldSetDifference x y = fieldSetIntersection x (fieldSetComplement y)

-- | The syntax algebra of canonical LF terms, parameterized
--   by `γ`, a context of free variables and `s` the syntactic sort
--   of the term.
data LF (f :: Ctx * -> SORT -> *) :: Ctx * -> SORT -> * where
  Weak   :: !(Weakening γ γ') -> !(f γ s) -> LF f γ' s

  Type     :: LF f γ KIND
  KPi      :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) KIND) -> LF f γ KIND

  AType    :: !(f γ ATYPE) -> LF f γ TYPE
  TyPi     :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) TYPE) -> LF f γ TYPE
  TyRecord :: f γ TERM -> LF f γ TYPE
  TyRow    :: FieldSet f -> LF f γ TYPE
                -- This set defines an _overapproximation_ of the
                -- set of fields defined in the row.  Thus, if:
                -- f ∉ fs and r : row fs, then row r does not define field f.
                -- In particular, if r : row ∅, then r must be the empty row.

  TyConst  :: !(LFTypeConst f) -> LF f E ATYPE
  TyApp    :: !(f γ ATYPE) -> !(f γ TERM) -> LF f γ ATYPE

  ATerm    :: !(f γ ATERM) -> LF f γ TERM
  Lam      :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) TERM) -> LF f γ TERM
  Row      :: Map (LFRecordIndex f) (f γ TYPE) -> LF f γ TERM
  RowModify :: !(f γ ATERM)
            -> !(Set (LFRecordIndex f))            -- fields to delete
            -> !(Map (LFRecordIndex f) (f γ TYPE)) -- fields to add
            -> LF f γ TERM
  Record   :: Map (LFRecordIndex f) (f γ TERM) -> LF f γ TERM
  RecordModify :: !(f γ ATERM)
            -> !(Set (LFRecordIndex f))            -- fields to delete
            -> !(Map (LFRecordIndex f) (f γ TERM)) -- fields to add
            -> LF f γ TERM

  Var       :: LF f (γ ::> b) ATERM
  UVar      :: !(LFUVar f) -> LF f E ATERM
  Const     :: !(LFConst f) -> LF f E ATERM
  App       :: !(f γ ATERM) -> !(f γ TERM) -> LF f γ ATERM
  Project   :: !(f γ ATERM) -> !(LFRecordIndex f) -> LF f γ ATERM

  Fail     :: LF f γ CON
  Unify    :: !(f γ ATERM) -> !(f γ ATERM) -> LF f γ CON
  And      :: [f γ CON] -> LF f γ CON
  Forall   :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON
  Exists   :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) CON) -> LF f γ CON

  Sigma    :: !String -> !(f γ TYPE) -> !(f (γ ::> ()) GOAL) -> LF f γ GOAL
  Goal     :: !(f γ TERM) -> !(f γ CON) -> LF f γ GOAL

class LiftClosed (γ :: Ctx *) where
  liftWeakening :: Weakening E γ
  liftClosed :: LFModel f m => f E s -> f γ s
  liftClosed = weaken liftWeakening

instance LiftClosed E where
  liftWeakening = WeakRefl
instance LiftClosed γ => LiftClosed (γ ::> b) where
  liftWeakening = WeakLeft liftWeakening

data Prec
  = TopPrec
  | AppLPrec
  | AppRPrec
  | BinderPrec
  | RecordPrec
  | RowPrec
 deriving (Eq)


data Var :: Ctx * -> * where
  F :: !(Var γ) -> Var (γ ::> b)
  B ::             Var (γ ::> b)

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
  WeakLeft  :: !(Weakening γ γ') -> Weakening γ (γ'::>b)
  WeakRight :: !(Weakening (γ::>b) γ') -> Weakening γ γ'
  WeakSkip  :: !(Weakening γ γ') -> Weakening (γ::>b) (γ'::>b)

-- | A substituion from γ to γ' represents a function that
--   sends a term in context γ to one in context γ' that
--   assigns variables in γ to terms with free variables in γ'.
--   This particular syntactic form of substituions is tailored
--   to the structure of the hereditary substituion algorithm
--   and allows us to recognize certain situations where we can stop early
--   and avoid traversing subtrees.
data Subst f :: Ctx * -> Ctx * -> * where
  SubstRefl  :: Subst f γ γ
  SubstApply :: !(Subst f γ γ')
             -> f γ' TERM -- NB don't make this strict.  'strengthen' puts 'error' here
             -> Subst f (γ ::> b) γ'
  SubstWeak  :: !(Weakening γ₂ γ₃) -> !(Subst f γ₁ γ₂) -> Subst f γ₁ γ₃
  SubstSkip  :: !(Subst f γ γ') -> Subst f (γ ::> b) (γ' ::> b)


-- | An abstraction is a bit lit a substituion in reverse;
--   it lists a sequence of unification variables that
--   are to be replaced by regular deBruijn variables.
data Abstraction f :: Ctx * -> Ctx * -> * where
  AbstractRefl  :: Abstraction f γ γ
  AbstractApply :: !(Abstraction f γ γ')
                -> !(LFUVar f)
                -> Abstraction f γ (γ'::>b)
  AbstractSkip  :: !(Abstraction f γ γ')
                -> Abstraction f (γ::>b) (γ'::>b)

-- | This datastructure represents the ways a canonical LF kind can be viewed.
--   A kind is either the constant 'type' or a Π binder.
data KindView f m γ where
 VType :: KindView f m γ
 VKPi :: forall f m γ
       . (?hyps :: Hyps f (γ::>()))
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
 VTyRecord :: f γ TERM -> TypeView f m γ
 VTyPi :: forall f m γ
        . (?hyps :: Hyps f (γ::>()))
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
 VRecord :: Map (LFRecordIndex f) (f γ TERM) -> TermView f m γ
 VProject :: f γ TERM -> LFRecordIndex f -> [f γ TERM] -> TermView f m γ
 VLam   :: forall f m γ
         . (?hyps :: Hyps f (γ ::> ()))
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
          . (?hyps :: Hyps f (γ::>()))
         => String
         -> Var (γ::> ())
         -> f γ TYPE
         -> f (γ::> ()) CON
         -> ConstraintView f m γ
 VExists :: forall f m γ
          . (?hyps :: Hyps f (γ::>()))
         => String
         -> Var (γ::> ())
         -> f γ TYPE
         -> f (γ::> ()) CON
         -> ConstraintView f m γ

data LFVal f m a
  = ValLam (LFVal f m a -> m (LFVal f m a))
  | ValRecord (Map (LFRecordIndex f) (LFVal f m a))
  | ValRow (Set (LFRecordIndex f))
  | ValBase a

type LFAlgebra f m a =
  LFConst f -> [LFVal f m a] -> m (LFVal f m a)

infixr 0 ::.
infixr 0 :.

data SigDecl f m
  = LFTypeConst f ::. m (f E KIND)
  | LFConst f     :.  m (f E TYPE)

-- | This datastructure represents the ways a canonical LF term can be viewed.
--   A term is either a goal (consisting of a term and constraints) or is
--   a Σ binder. In the binder case,
--   a continuation is provided that allows access to the subterm.
data GoalView f m γ where
 VGoal :: f γ TERM -> f γ CON -> GoalView f m γ
 VSigma  :: forall f m γ
          . (?hyps :: Hyps f (γ::>()))
         => String
         -> Var (γ::> ())
         -> f γ TYPE
         -> f (γ::> ()) GOAL
         -> GoalView f m γ

class (Ord (LFTypeConst f), Ord (LFConst f), Ord (LFUVar f), Ord (LFRecordIndex f),
       Pretty (LFTypeConst f), Pretty (LFConst f), Pretty (LFUVar f), Pretty (LFRecordIndex f),
       Monad m)
  => LFModel (f :: Ctx * -> SORT -> *) m | f -> m, m -> f where

  unfoldLF :: f γ s -> LF f γ s
  foldLF :: LF f γ s -> m (f γ s)

  weaken :: Weakening γ γ' -> f γ s -> f γ' s
  weak   :: f γ s -> f (γ::>b) s
  weak = weaken (WeakLeft WeakRefl)

  aterm :: f γ ATERM -> f γ TERM
  atype :: f γ ATYPE -> f γ TYPE

  hsubst :: (?soln :: LFSoln f)
         => Subst f γ γ'
         -> f γ s
         -> m (f γ' s)

  ppLF :: (?hyps :: Hyps f γ', ?soln :: LFSoln f)
       => Prec
       -> Weakening γ γ'
       -> f γ s
       -> m Doc

  validateKind :: (?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ KIND  -> m ()

  validateType :: (?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ TYPE  -> m ()

  inferKind    :: (?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ ATYPE -> m (f γ' KIND)

  inferType    :: (?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ TERM  -> m (f γ' TYPE)

  inferAType   :: (?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ ATERM -> m (f γ' TYPE)

  validateGoal :: (?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ GOAL  -> m ()

  validateCon  :: (?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ' -> f γ CON   -> m ()

  inEmptyCtx :: ((?hyps :: Hyps f E) => a) -> a

  extendCtx :: (?hyps :: Hyps f γ)
            => String
            -> Quant
            -> f γ TYPE
            -> ((?hyps :: Hyps f (γ::>b)) => x)
            -> x

  lookupCtx :: (?hyps :: Hyps f γ)
            => Var γ
            -> (String, Quant, f γ TYPE)

  alphaEq      :: (?soln :: LFSoln f) => f γ s -> f γ s -> Bool
  varCensus    :: (?soln :: LFSoln f) => Var γ -> f γ s -> Int
  freeVar      :: (?soln :: LFSoln f) => Var γ -> f γ s -> Bool
  freeUVars    :: f γ s -> Set (LFUVar f)

  constKind :: LFTypeConst f -> m (f E KIND)
  constType :: LFConst f -> m (f E TYPE)
  uvarType  :: LFUVar f -> m (f E TYPE)

  kindView :: (?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ KIND
           -> KindView f m γ

  typeView :: (?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ TYPE
           -> TypeView f m γ

  termView :: (?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ TERM
           -> TermView f m γ

  constraintView :: (?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ CON
           -> ConstraintView f m γ

  goalView :: (?hyps :: Hyps f γ, ?soln :: LFSoln f)
           => f γ GOAL
           -> GoalView f m γ

  evaluate :: (?soln :: LFSoln f)
           => LFAlgebra f m a
           -> f γ TERM
           -> Seq (LFVal f m a)
           -> m (LFVal f m a)

  getSignature :: m [SigDecl f Identity]

  extendSignature :: [SigDecl f m] -> m x -> m x
  freshName :: (?hyps :: Hyps f γ) => String -> String

  withCurrentSolution :: ((?soln :: LFSoln f) => m x) -> m x
  commitSolution :: LFSoln f -> m ()
  lookupUVar :: Proxy f -> LFUVar f -> LFSoln f -> Maybe (f E TERM)
  assignUVar :: Proxy f -> LFUVar f -> f E TERM -> LFSoln f -> m (LFSoln f)
  freshUVar :: f E TYPE -> m (LFUVar f)
  emptySolution :: Proxy f -> LFSoln f
  extendSolution :: LFUVar f -> f E TERM -> LFSoln f -> Maybe (LFSoln f)

  instantiate :: (?soln :: LFSoln f)
              => f γ s -> ChangeT m (f γ s)

  abstractUVars :: Abstraction f γ γ'
                -> f γ s
                -> m (f γ' s)

  solve :: f E CON -> m (f E CON, LFSoln f)
