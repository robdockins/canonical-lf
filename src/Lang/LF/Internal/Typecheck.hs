module Lang.LF.Internal.Typecheck where

import Data.Set (Set)

import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Print

validateKindLF :: forall f m γ
                . (WFContext γ, LFModel f m, ?nms::Set String, ?hyps::Hyps f γ, ?soln :: LFSoln f)
               => f γ KIND
               -> m ()
validateKindLF tm =
  case unfoldLF tm of
    Weak x -> weakenCtx $ validateKind x
    Type -> return ()
    KPi nm a k -> do
      validateType a
      extendCtx nm QPi a $ do
        validateKind k
      {- subordination check -}


validateTypeLF :: forall f m γ
                . (WFContext γ, LFModel f m, ?nms::Set String, ?hyps:: Hyps f γ, ?soln :: LFSoln f)
               => f γ TYPE
               -> m ()
validateTypeLF tm =
  case unfoldLF tm of
    Weak x -> weakenCtx $ validateType x
    TyPi nm a1 a2 -> do
      validateType a1
      extendCtx nm QPi a1 $ validateType a2
    AType p ->
      checkK =<< inferKind p

 where
  checkK :: forall γ. f γ KIND -> m ()
  checkK k =
   case unfoldLF k of
      Weak k' -> checkK k'
      Type -> return ()
      KPi _ _ _ -> fail "invalid atomic type"

inferKindLF :: forall f m γ
             . (WFContext γ, LFModel f m, ?nms::Set String, ?hyps::Hyps f γ, ?soln :: LFSoln f)
            => f γ ATYPE
            -> m (f γ KIND)
inferKindLF tm =
  case unfoldLF tm of
    Weak x -> weakenCtx (weaken <$> inferKind x)
    TyConst x -> constKind x
    TyApp p1 m2 -> do
      k <- inferKind p1
      subK ?hyps SubstRefl id k m2

 where
  subK :: forall γ'. WFContext γ'
       => Hyps f γ'
       -> Subst m f γ' γ
       -> (f γ' TYPE -> f γ TYPE)
       -> f γ' KIND
       -> f γ TERM
       -> m (f γ KIND)
  subK h s w k m =
     case unfoldLF k of
       Weak x -> subK (weakenHyps h) (SubstWeak s) (w . weaken) x m
       KPi _ a2 k1 -> do
         checkType tm m (w a2)
         hsubst (SubstApply s (\_ -> return m)) k1
       _ -> do
         kdoc <- let ?hyps = h in displayLF k
         fail $ unwords ["invalid atomic type family", kdoc]

checkType :: (WFContext γ, LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
          => f γ s
          -> f γ TERM
          -> f γ TYPE
          -> m ()
checkType z m a = do
  a' <- inferType m
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


inferTypeLF :: forall f m γ
             . (WFContext γ, LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
            => f γ TERM
            -> m (f γ TYPE)
inferTypeLF m =
  case unfoldLF m of
    Weak x -> weakenCtx (weaken <$> inferType x)
    ATerm r -> do
      a <- inferAType r
      checkTp ?hyps a
      return a
    Lam nm a2 m -> do
      extendCtx nm QLam a2 $ do
        a1 <- inferType m
        foldLF (TyPi nm a2 a1)

 where
  checkTp :: forall γ'. WFContext γ' => Hyps f γ' -> f γ' TYPE -> m ()
  checkTp h a =
     case unfoldLF a of
       Weak x -> checkTp (weakenHyps h) x
       AType _ -> return ()
       TyPi _ _ _ -> do
           mdoc <- displayLF m
           adoc <- let ?hyps = h in displayLF a
           fail $ unlines ["Term fails to be η-long:"
                          , mdoc ++ " ::"
                          , adoc
                          ]

inferATypeLF :: forall m f γ
              . (WFContext γ, LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
             => f γ ATERM
             -> m (f γ TYPE)
inferATypeLF r =
  case unfoldLF r of
    Weak x -> weakenCtx (weaken <$> inferAType x)
    Var b -> do
      let (_,_,a) = lookupVar ?hyps (B b)
      return a
    UVar u -> uvarType u
    Const c -> constType c
    App r1 m2 -> do
      a <- inferAType r1
      checkArg m2 id SubstRefl a

 where
  checkArg :: forall γ'. WFContext γ'
           => f γ TERM
           -> (f γ' TYPE -> f γ TYPE)
           -> Subst m f γ' γ
           -> f γ' TYPE
           -> m (f γ TYPE)
  checkArg m2 w s a =
      case unfoldLF a of
        Weak x ->
          checkArg m2 (w . weaken) (SubstWeak s) x
        TyPi _ a2 a1 -> do
          checkType r m2 (w a2)
          hsubst (SubstApply s (\() -> return m2)) a1
        _ -> do
          adoc <- displayLF (w a)
          fail $ unwords ["Expected function type", adoc]


validateGoalLF :: forall f m γ
                . (WFContext γ, LFModel f m, ?nms::Set String, ?hyps:: Hyps f γ, ?soln :: LFSoln f)
               => f γ GOAL
               -> m ()
validateGoalLF g =
  case unfoldLF g of
    Weak x -> weakenCtx $ validateGoal x
    Sigma nm a g' -> do
      validateType a
      extendCtx nm QSigma a $ validateGoal g'
    Goal m c -> do
      _ <- inferType m
      validateCon c


validateConLF :: forall f m γ
                . (WFContext γ, LFModel f m, ?nms::Set String, ?hyps:: Hyps f γ, ?soln :: LFSoln f)
               => f γ CON
               -> m ()
validateConLF c =
  case unfoldLF c of
    Weak x -> weakenCtx $ validateCon x
    Fail -> return ()
    Unify r1 r2 -> do
      _ <- inferAType r1
      _ <- inferAType r2
      return ()
    Forall nm a c' -> do
      validateType a
      extendCtx nm QForall a $ validateCon c'
    Exists nm a c' -> do
      validateType a
      extendCtx nm QExists a $ validateCon c'
    And cs ->
      mapM_ validateCon cs
