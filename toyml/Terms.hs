module Terms where

import Prelude hiding (pi, abs)

import           Data.String
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF
import           Lang.LF.Tree hiding (M)
import qualified Lang.LF.Tree as Tree

data TyConst
   = TNm String
 deriving (Eq, Ord, Show)

instance Pretty TyConst where
  pretty (TNm x) = pretty x
instance IsString TyConst where
  fromString = TNm

data TmConst
   = CNm String
 deriving (Eq, Ord, Show)

instance Pretty TmConst where
  pretty (CNm x) = pretty x
instance IsString TmConst where
  fromString = CNm


type LF = Tree.LFTree TyConst TmConst
type Sig = Tree.Signature TyConst TmConst
type M = Tree.M TyConst TmConst
type H = Hyps LF

-- Signature for the language λᵁCPS from Andrew Kennedy's
-- "Compiling with Continuations, Continued" (ICFP 2007)
sig :: Sig
sig = buildSignature
  [ "tm"       ::. lf_type
  , "val"      ::. lf_type
  , "ml"       ::. lf_type
  , "v"        ::. lf_type
  , "kv"       ::. lf_type
  , "ty"       ::. lf_type
  , "scheme"   ::. lf_type

  , "unit"      :. ty
  , "arr"       :. ty ==> ty ==> ty
  , "prod"      :. ty ==> ty ==> ty
  , "sum"       :. ty ==> ty ==> ty

  , "scheme_ty"     :. ty ==> scheme
  , "scheme_forall" :. (ty ==> scheme) ==> scheme

  , "letval"   :. val ==> (v ==> tm) ==> tm
  , "letcont"  :. (v ==> tm) ==> (kv ==> tm) ==> tm
  , "let_prj1" :. v ==> (v ==> tm) ==> tm
  , "let_prj2" :. v ==> (v ==> tm) ==> tm
  , "app"      :. v ==> kv ==> v ==> tm
  , "case"     :. v ==> kv ==> kv ==> tm
  , "enter"    :. kv ==> v ==> tm

  , "tt"       :. val
  , "pair"     :. v ==> v ==> val
  , "inl"      :. v ==> val
  , "inr"      :. v ==> val
  , "lam"      :. (kv ==> v ==> tm) ==> val

  , "ml_var"    :. v ==> ml
  , "ml_app"    :. ml ==> ml ==> ml
  , "ml_lam"    :. (v ==> ml) ==> ml
  , "ml_pair"   :. ml ==> ml ==> ml
  , "ml_fst"    :. ml ==> ml
  , "ml_snd"    :. ml ==> ml
  , "ml_tt"     :. ml
  , "ml_inl"    :. ml ==> ml
  , "ml_inr"    :. ml ==> ml
  , "ml_letval" :. ml ==> (v ==> ml) ==> ml
  , "ml_case"   :. ml ==> (v ==> ml) ==> (v ==> ml) ==> ml

  , "tt_CAF" :. v
  , "f" :. v
  , "g" :. v
  , "g'" :. v
  , "g''" :. v
  , "y" :. v
  , "x2" :. v
  , "x3" :. v
  , "halt"     :. kv
  ]


instance LiftClosed γ => IsString (M (LF γ TYPE)) where
  fromString = tyConst . TNm

instance LiftClosed γ => IsString (M (LF γ TERM)) where
  fromString = tmConst . CNm

tm :: LiftClosed γ => M (LF γ TYPE)
tm = tyConst "tm"

val :: LiftClosed γ => M (LF γ TYPE)
val = tyConst "val"

v :: LiftClosed γ => M (LF γ TYPE)
v = tyConst "v"

kv :: LiftClosed γ => M (LF γ TYPE)
kv = tyConst "kv"

ml :: LiftClosed γ => M (LF γ TYPE)
ml = tyConst "ml"

ty :: LiftClosed γ => M (LF γ TYPE)
ty = tyConst "ty"

scheme :: LiftClosed γ => M (LF γ TYPE)
scheme = tyConst "scheme"
