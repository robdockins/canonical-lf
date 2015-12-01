{-# OPTIONS_GHC -Wwarn #-}
module Main where

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import           Lang.LF
import           Lang.LF.Tree


type LF = LFTree String String
type Sig = Signature String String
type M = ReaderT Sig (Except String)

sig :: Sig
sig = buildSignature
  [ TypeDecl "Nat" typ
  , TypeDecl "Prop" typ
  , TypeDecl "Set" typ

  , TermDecl "Z" nat
  , TermDecl "S" $ nat ==> nat
  , TermDecl "True" prop
  , TermDecl "False" prop
  , TermDecl "and" $ prop ==> prop ==> prop
  , TermDecl "or" $ prop ==> prop ==> prop
  , TermDecl "implies" $ prop ==> prop ==> prop
  , TermDecl "arrow" $ set ==> set ==> set
  ]

nat :: M (LF TYPE)
nat = tyConst "Nat"

prop :: M (LF TYPE)
prop = tyConst "Prop"

set :: M (LF TYPE)
set = tyConst "Set"

pand :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
pand x y = tmConst "and" @@ x @@ y

por :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
por x y = tmConst "or" @@ x @@ y

arrow :: M (LF TERM) -> M (LF TERM) -> M (LF TERM)
arrow x y = tmConst "arrow" @@ x @@ y

zero :: M (LF TERM)
zero = tmConst "Z"

suc :: M (LF TERM) -> M (LF TERM)
suc x = tmConst "S" @@ x

--testTerm :: LF TYPE
testTerm = runM sig $
   lam "x" prop (por (var 0) (pand (tmConst "False") (var 0)))
--  lam "x" nat (app (suc (var 0)) (suc (var 0)))
--    nat_iter_type

main = sig `seq` do
   putStrLn $ show $ runM sig $ ppLF Set.empty Seq.empty testTerm
   putStrLn $ show $ runM sig (ppLF Set.empty Seq.empty =<< inferType Seq.empty testTerm)
