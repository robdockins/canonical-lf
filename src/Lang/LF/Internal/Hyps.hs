module Lang.LF.Internal.Hyps where

import Data.Set (Set)
import qualified Data.Set as Set

import Lang.LF.Internal.Model


getName :: Set String
        -> String
        -> String
getName ss nm = tryName ss (nm : [ nm++show i | i <- [0..] ])
 where
  tryName ss (x:xs)
    | Set.member x ss = tryName ss xs
    | otherwise = x
  tryName _ [] = undefined

freshName :: (?nms :: Set String)
          => String
          -> String
freshName nm = getName ?nms nm

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

extendHyps :: Hyps f γ -> String -> Quant -> f γ TYPE -> Hyps f (γ ::> b)
extendHyps h nm q a = HCons h q (\_ -> (nm,a))


weakenHyps :: Hyps f (γ::>b) -> Hyps f γ
weakenHyps (HCons h _ _) = h


inEmptyCtx :: ((?nms :: Set String, ?hyps :: Hyps f E) => a)
           -> a
inEmptyCtx f =
  let ?nms = Set.empty in
  let ?hyps = HNil in
  f

weakenCtx :: (?hyps :: Hyps f (γ ::> b))
          => ((?hyps :: Hyps f γ) => a)
          -> a
weakenCtx f =
  let ?hyps = weakenHyps ?hyps in
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
