module Lang.LF.Internal.Solve where

import Lang.LF.ChangeT
import Lang.LF.Internal.Model
import Lang.LF.Internal.Build

solveLF :: forall f m
         . (LFModel f m)
        => f E CON
        -> m (f E CON, LFSoln f)
solveLF c0 = withCurrentSolution $ go (c0, ?soln)
 where
  go :: (LFModel f m)
        => (f E CON, LFSoln f)
        -> m (f E CON, LFSoln f)
  go (c, soln) =
    case doSolve c soln of
      Unchanged _ -> return (c, soln)
      Changed m -> do
        (mxs, soln') <- m
        case mxs of
          Nothing -> do
            x <- liftClosed <$> foldLF Fail
            return (x, soln')
          Just xs -> do
            let ?soln = soln'
            x <- foldLF (And xs)
            x' <- runChangeT $ instantiate x
            go (x', soln')
            --return (x', soln')
            --b <- alphaEq c x'
            --if b then
            --  return (x', soln')
            --else
            --  go (x', soln')

doSolve :: (LFModel f m)
        => f E CON
        -> LFSoln f
        -> ChangeT m (Maybe [f E CON], LFSoln f)
doSolve c soln =
  case unfoldLF c of
    Fail -> Unchanged (Nothing, soln)

    Unify r1 r2 ->
      let ?soln = soln in
      let res = unifyATm SubstRefl SubstRefl r1 r2 in
      case res of
        UnifyDefault -> Unchanged (Just [c], soln)
        UnifyDecompose xs -> Changed (xs >>= \xs' -> return (xs', soln))
        UnifySolve u r -> Changed $ do
          m <- aterm <$> r
          extendSolution u m soln >>= \case
            Nothing    -> return (Just [c], soln)
            Just soln' -> return (Just [], soln')

    And cs -> go cs soln
     where go [] s = return (Just [], s)
           go (x:xs) s = do
             (cs1, s') <- doSolve x s
             (cs2, s'') <- go xs s'
             let mcs = case (cs1, cs2) of
                         (Nothing, _) -> Nothing
                         (_, Nothing) -> Nothing
                         (Just as, Just bs) -> Just (as++bs)
             return (mcs, s'')

    Forall _ _ _ -> error "doSolve : forall quantifier"
    Exists _ _ _ -> error "doSolve : exists quantifier"
