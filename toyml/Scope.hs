module Scope where

import           Data.Set (Set)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Lang.LF

import Grammar
import Terms

scopeAnalysis
  :: (LiftClosed γ
     , ?hyps :: Hyps LF γ
     , ?nms :: Set String
     )
  => Map String (Var γ)
  -> AST
  -> M (LF γ TERM)
scopeAnalysis symbolTable t =
  case t of
    Ident nm ->
      case Map.lookup nm symbolTable of
        Just v  ->
          "ml_var" @@ var v
        Nothing ->
          fail $ concat ["identifier '", nm, "' not in scope"]

    Fn nm m ->
      "ml_lam" @@ (λ nm v $ \x -> do
        let symbolTable' = Map.insert nm x $ fmap F symbolTable
        scopeAnalysis symbolTable' m)

    Letval nm m body ->
      "ml_letval"
        @@ (scopeAnalysis symbolTable m)
        @@ (λ nm v $ \x -> do
              let symbolTable' = Map.insert nm x $ fmap F symbolTable
              scopeAnalysis symbolTable' body)

    Tt -> "ml_tt"

    App a b ->
      "ml_app"
        @@ scopeAnalysis symbolTable a
        @@ scopeAnalysis symbolTable b

    Case e (lnm,lbranch) (rnm, rbranch) ->
      "ml_case"
        @@ scopeAnalysis symbolTable e
        @@ (λ lnm v $ \x -> do
              let symbolTable' = Map.insert lnm x $ fmap F symbolTable
              scopeAnalysis symbolTable' lbranch)
        @@ (λ rnm v $ \x -> do
              let symbolTable' = Map.insert rnm x $ fmap F symbolTable
              scopeAnalysis symbolTable' rbranch)

    Pair a b ->
      "ml_pair"
        @@ scopeAnalysis symbolTable a
        @@ scopeAnalysis symbolTable b

    Inl a ->
      "ml_inl"
        @@ scopeAnalysis symbolTable a

    Inr a ->
      "ml_inr"
        @@ scopeAnalysis symbolTable a

    Fst a ->
      "ml_fst"
        @@ scopeAnalysis symbolTable a

    Snd a ->
      "ml_snd"
        @@ scopeAnalysis symbolTable a
