module Lang.LF.Internal.Hyps where

import Data.Set (Set)
import qualified Data.Set as Set

import Lang.LF.Internal.Model


-- | A sequence of hypotheses, giving types to the free variables in γ.
data LFHyps (f :: Ctx * -> SORT -> *) (γ :: Ctx *) where
  HNil   :: LFHyps f E
  HCons  :: !(LFHyps f γ) -> !Quant -> !String -> !(f γ TYPE) -> LFHyps f (γ ::> b)

getName :: Set String
        -> String
        -> String
getName ss nm = tryName ss (nm : [ nm++show i | i <- [0..] ])
 where
  tryName ss (x:xs)
    | Set.member x ss = tryName ss xs
    | otherwise = x
  tryName _ [] = undefined

freshName :: Set String
          -> String
          -> String
freshName nms nm = getName nms nm

lookupHyp :: LFModel f m
          => LFHyps f γ
          -> Var γ
          -> Weakening γ γ'
          -> (String, Quant, f γ' TYPE)
lookupHyp (HCons _ q nm a) B w =
  (nm, q, weaken (WeakRight w) a)
lookupHyp (HCons h _ _ _) (F x) w =
  lookupHyp h x (WeakRight w)
lookupHyp HNil _ _ = error "impossible"

lookupVar :: LFModel f m
          => LFHyps f γ
          -> Var γ
          -> (String, Quant, f γ TYPE)
lookupVar h v = lookupHyp h v WeakRefl

extendHyps :: LFHyps f γ -> String -> Quant -> f γ TYPE -> LFHyps f (γ ::> b)
extendHyps h nm q a = HCons h q nm a

{-
inEmptyCtx :: ((?nms :: Set String, ?hyps :: Hyps f E) => a)
           -> a
inEmptyCtx f =
  let ?nms = Set.empty in
  let ?hyps = HNil in
  f

extendCtx :: (?nms :: Set String, ?hyps :: Hyps f γ)
          => String
          -> Quant
          -> f γ TYPE
          -> ((?nms :: Set String, ?hyps :: Hyps f (γ::>b)) => x)
          -> x
extendCtx nm q a f =
  let nm' = freshName nm in
  let ?nms = Set.insert nm' ?nms in
  let ?hyps = extendHyps ?hyps nm' q a in
  f
-}
