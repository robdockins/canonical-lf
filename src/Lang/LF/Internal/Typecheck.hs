module Lang.LF.Internal.Typecheck where

import Data.Set (Set)

import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Print
import Lang.LF.Internal.Weak

validateKindLF :: forall f m γ γ'
                . (LFModel f m, ?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ'
               -> f γ KIND
               -> m ()
validateKindLF w tm =
  case unfoldLF tm of
    Weak w' x -> validateKind (weakCompose w w') x
    Type -> return ()
    KPi nm a k -> do
      validateType w a
      extendCtx nm QPi (weaken w a) $ do
        validateKind (WeakSkip w) k
      {- subordination check -}

validateTypeLF :: forall f m γ γ'
                . (LFModel f m, ?nms::Set String, ?hyps:: Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ'
               -> f γ TYPE
               -> m ()
validateTypeLF w tm =
  case unfoldLF tm of
    Weak w' x -> validateType (weakCompose w w') x
    TyPi nm a1 a2 -> do
      validateType w a1
      extendCtx nm QPi (weaken w a1) $ validateType (WeakSkip w) a2
    AType p ->
      checkK =<< inferKind w p

 where
  checkK :: forall γ. f γ KIND -> m ()
  checkK k =
   case unfoldLF k of
      Weak _ k' -> checkK k'
      Type -> return ()
      KPi _ _ _ -> fail "invalid atomic type"

inferKindLF :: forall f m γ γ'
             . (LFModel f m, ?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
            => Weakening γ γ'
            -> f γ ATYPE
            -> m (f γ' KIND)
inferKindLF w tm =
  case unfoldLF tm of
    Weak w' x -> inferKind (weakCompose w w') x
    TyConst x -> weaken w <$> constKind x
    TyApp p1 m2 -> do
      k <- inferKind w p1
      subK WeakRefl k (weaken w m2)

 where
  subK :: forall γ
        . Weakening γ γ'
       -> f γ KIND
       -> f γ' TERM
       -> m (f γ' KIND)
  subK subw k m =
     case unfoldLF k of
       Weak w' x -> subK (weakCompose subw w') x m
       KPi _ a2 k1 -> do
         checkType (weaken w tm) m (weaken subw a2)
         hsubst (SubstApply (SubstWeak subw SubstRefl) m) k1
       _ -> do
         kdoc <- displayLF (weaken subw k)
         fail $ unwords ["invalid atomic type family", kdoc]

checkType :: (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
          => f γ s
          -> f γ TERM
          -> f γ TYPE
          -> m ()
checkType z m a = do
  a' <- inferType WeakRefl m
  if alphaEq a a' then return ()
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


inferTypeLF :: forall f m γ γ'
             . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ', ?soln :: LFSoln f)
            => Weakening γ γ'
            -> f γ TERM
            -> m (f γ' TYPE)
inferTypeLF w m =
  case unfoldLF m of
    Weak w' x -> inferType (weakCompose w w') x
    ATerm r -> do
      a <- inferAType w r
      checkTp WeakRefl a
      return a
    Lam nm a2 m -> do
      let a2' = weaken w a2
      extendCtx nm QLam a2' $ do
        a1 <- inferType (WeakSkip w) m
        foldLF (TyPi nm a2' a1)

 where
  checkTp :: forall γ. Weakening γ γ' -> f γ TYPE -> m ()
  checkTp subw a =
     case unfoldLF a of
       Weak w' x -> checkTp (weakCompose subw w') x
       AType _ -> return ()
       TyPi _ _ _ -> do
           mdoc <- displayLF (weaken w m)
           adoc <- displayLF (weaken subw a)
           fail $ unlines ["Term fails to be η-long:"
                          , mdoc ++ " ::"
                          , adoc
                          ]

inferATypeLF :: forall m f γ γ'
              . (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ', ?soln :: LFSoln f)
             => Weakening γ γ'
             -> f γ ATERM
             -> m (f γ' TYPE)
inferATypeLF w r =
  case unfoldLF r of
    Weak w' x -> inferAType (weakCompose w w') x
    Var -> do
      let (_,_,a) = lookupVar ?hyps (weakenVar w B)
      return a
    UVar u -> weaken w <$> uvarType u
    Const c -> weaken w <$> constType c
    App r1 m2 -> do
      a <- inferAType w r1
      checkArg (weaken w m2) WeakRefl a

 where
  checkArg :: forall γ
            . f γ' TERM
           -> Weakening γ γ'
           -> f γ TYPE
           -> m (f γ' TYPE)
  checkArg m2 wsub a =
      case unfoldLF a of
        Weak w' x -> checkArg m2 (weakCompose wsub w') x
        TyPi _ a2 a1 -> do
          checkType (weaken w r) m2 (weaken wsub a2)
          hsubst (SubstApply (SubstWeak wsub SubstRefl) m2) a1
        _ -> do
          adoc <- displayLF (weaken wsub a)
          fail $ unwords ["Expected function type", adoc]


validateGoalLF :: forall f m γ γ'
                . (LFModel f m, ?nms::Set String, ?hyps:: Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ'
               -> f γ GOAL
               -> m ()
validateGoalLF w g =
  case unfoldLF g of
    Weak w' x -> validateGoal (weakCompose w w') x
    Sigma nm a g' -> do
      validateType w a
      extendCtx nm QSigma (weaken w a) $ validateGoal (WeakSkip w) g'
    Goal m c -> do
      _ <- inferType w m
      validateCon w c


validateConLF :: forall f m γ γ'
                . (LFModel f m, ?nms::Set String, ?hyps:: Hyps f γ', ?soln :: LFSoln f)
               => Weakening γ γ'
               -> f γ CON
               -> m ()
validateConLF w c =
  case unfoldLF c of
    Weak w' x -> validateCon (weakCompose w w') x
    Fail -> return ()
    Unify r1 r2 -> do
      -- FIXME? directly check for accecptability?
      _ <- inferAType w r1
      _ <- inferAType w r2
      return ()
    Forall nm a c' -> do
      validateType w a
      extendCtx nm QForall (weaken w a) $ validateCon (WeakSkip w) c'
    Exists nm a c' -> do
      validateType w a
      extendCtx nm QExists (weaken w a)  $ validateCon (WeakSkip w) c'
    And cs ->
      mapM_ (validateCon w) cs
