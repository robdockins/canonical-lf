module Lang.LF.Internal.Typecheck where

import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Internal.Basics
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
      extendCtx nm QPi (weaken w a1) $
        validateType (WeakSkip w) a2
    TyRow _ -> do
      return ()
    TyRecord row -> do
      checkRow =<< inferType w row
    AType p ->
      checkK =<< inferKind w p

 where
  checkRow :: forall γ. f γ TYPE -> m ()
  checkRow t =
    case unfoldLF t of
      Weak _ t' -> checkRow t'
      TyRow _ -> return ()
      TyRecord _ -> fail "invalid row type"
      TyPi _ _ _ -> fail "invalid row type"
      AType _    -> fail "invalid row type"

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

-- | Here we check for a very limited form of subtyping.  We are really only
--   interested in checking subsumption of row types; that is, that any
--   disjointness conditions we assume about row variables are upheld.
checkSubtype
          :: (LFModel f m, ?soln :: LFSoln f)
          => Weakening γ₁ γ
          -> f γ₁ TYPE -- expected subtype
          -> Weakening γ₂ γ
          -> f γ₂ TYPE -- expected supertype
          -> m Bool
checkSubtype w₁ sub w₂ super =
  case (unfoldLF sub, unfoldLF super) of
    (Weak w' x, _) -> checkSubtype (weakCompose w₁ w') x w₂ super
    (_, Weak w' y) -> checkSubtype w₁ sub (weakCompose w₂ w') y
    (TyPi _ a1 b1, TyPi _ a2 b2) ->
        (&&) <$> checkSubtype w₂ a2 w₁ a1 -- NB: contravariant in arguments!
             <*> checkSubtype (WeakSkip w₁) b1 (WeakSkip w₂) b2
    (TyRecord row1, TyRecord row2) -> checkRowSubtype w₁ row1 w₂ row2
    (TyRow flds1, TyRow flds2) ->
      -- NB: this really the only interesing case.  A row type is a subtype of
      -- another iff the fields it declares are a subset.
      return $ fieldSetSubset flds1 flds2
    (AType r1, AType r2) ->
      -- FIXME: is this too strong?
      return $ alphaEq (weaken w₁ r1) (weaken w₂ r2)
    _ -> return False

checkRowSubtype
          :: (LFModel f m, ?soln :: LFSoln f)
          => Weakening γ₁ γ
          -> f γ₁ TERM -- expected row subtype
          -> Weakening γ₂ γ
          -> f γ₂ TERM -- expected row supertype
          -> m Bool
checkRowSubtype w₁ sub w₂ super =
  case (unfoldLF sub, unfoldLF super) of
    (Weak w' x, _) -> checkRowSubtype (weakCompose w₁ w') x w₂ super
    (_, Weak w' y) -> checkRowSubtype w₁ sub (weakCompose w₂ w') y
    (Row flds1, Row flds2) -> minimum <$> (sequence $ mergeFlds flds1 flds2)
    (RowModify r1 del1 ins1, RowModify r2 del2 ins2) -> do
       let br = alphaEq (weaken w₁ r1) (weaken w₂ r2)
       let bdel = del1 == del2
       bins <- minimum <$> (sequence $ mergeFlds ins1 ins2)
       return (br && bdel && bins)
    _ -> return False

 where mergeFlds = Map.mergeWithKey
           (\_k t1 t2 -> Just $ checkSubtype w₁ t1 w₂ t2)
           (fmap (const $ return False))
           (fmap (const $ return False))


checkType :: (LFModel f m, ?nms :: Set String, ?hyps :: Hyps f γ, ?soln :: LFSoln f)
          => f γ s    -- ^ context of the term
          -> f γ TERM -- ^ term to check
          -> f γ TYPE -- ^ expected type
          -> m ()
checkType z m a = do
  a' <- inferType WeakRefl m
  b <- checkSubtype WeakRefl a' WeakRefl a
  if b then return ()
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
    Row flds -> do
      let flds' = Map.keysSet flds
      foldLF (TyRow (PosFieldSet flds'))
    RowModify r delSet insMap -> do
      rset <- checkRowTy WeakRefl =<< inferAType w r
      let rset'    = fieldSetDifference rset (PosFieldSet delSet)
      let insSet   = PosFieldSet (Map.keysSet insMap)
      let finalset = fieldSetUnion rset' insSet
      let PosFieldSet conflictset = fieldSetIntersection insSet rset'
      if Set.null conflictset then
        foldLF (TyRow finalset)
      else do
        let msg = text "Field insertions confilct with possibly existing fields:"
                    <$$>
                    (indent 2 $ vcat $ map pretty $ Set.toList conflictset)
        fail $ show msg

    Record flds -> do
      flds' <- traverse (inferType w) flds
      foldLF . TyRecord =<< foldLF (Row flds')

    RecordModify r delSet insMap -> do
      row <- checkRecordTy WeakRefl =<< inferAType w r
      insMap' <- traverse (inferType w) insMap
      row' <- rowModify row WeakRefl delSet insMap'
      foldLF (TyRecord row')

    Lam nm a2 m -> do
      let a2' = weaken w a2
      extendCtx nm QLam a2' $ do
        a1 <- inferType (WeakSkip w) m
        foldLF (TyPi nm a2' a1)

 where
  checkRecordTy :: forall γ. Weakening γ γ' -> f γ TYPE -> m (f γ' TERM)
  checkRecordTy subw a =
    case unfoldLF a of
      Weak w' x  -> checkRecordTy (weakCompose subw w') x
      TyRecord row -> return (weaken subw row)
      TyRow _    -> fail "Expected record type"
      TyPi _ _ _ -> fail "Expected record type"
      AType _    -> fail "Expected record type"

  checkRowTy :: forall γ. Weakening γ γ' -> f γ TYPE -> m (FieldSet f)
  checkRowTy subw a =
    case unfoldLF a of
      Weak w' x  -> checkRowTy (weakCompose subw w') x
      TyRow flds -> return flds
      TyRecord _ -> fail "Expected row type"
      TyPi _ _ _ -> fail "Expected row type"
      AType _    -> fail "Expected row type"

  checkTp :: forall γ. Weakening γ γ' -> f γ TYPE -> m ()
  checkTp subw a =
     case unfoldLF a of
       Weak w' x -> checkTp (weakCompose subw w') x
       AType _ -> return ()
       TyRecord _ -> return ()
       TyRow _ -> return ()
       TyPi _ _ _ -> do
           mdoc <- ppLF TopPrec w m
           adoc <- ppLF TopPrec subw a
           fail $ unlines ["Term fails to be η-long:"
                          , show $ indent 2 $ group $ hang 2 $
                               mdoc <+> text "::" <> line <> adoc
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
    Project r fld -> do
      a <- inferAType w r
      checkRecordProject a WeakRefl fld

 where
  checkRecordProject
           :: forall γ
            . f γ TYPE
           -> Weakening γ γ'
           -> LFRecordIndex f
           -> m (f γ' TYPE)
  checkRecordProject a wsub fld =
    case unfoldLF a of
      Weak w' x -> checkRecordProject x (weakCompose wsub w') fld
      TyRecord row -> checkRowProject row wsub fld
      _ -> do
          adoc <- ppLF TopPrec wsub a
          fail $ unwords ["Expected record type", show adoc]

  checkRowProject :: forall γ
            . f γ TERM
           -> Weakening γ γ'
           -> LFRecordIndex f
           -> m (f γ' TYPE)
  checkRowProject row wsub fld =
    case unfoldLF row of
      Weak w' x -> checkRowProject x (weakCompose wsub w') fld
      RowModify _ _ insFields ->
        case Map.lookup fld insFields of
          Just ty -> return (weaken wsub ty)
          Nothing -> do
            rowdoc <- ppLF RecordPrec wsub row
            fail $ unwords ["Could not prove field exists", show (pretty fld), show rowdoc]
      Row flds ->
        case Map.lookup fld flds of
          Just ty -> return (weaken wsub ty)
          Nothing -> do
            rowdoc <- ppLF RecordPrec wsub row
            fail $ unwords ["Record missing expected field", show (pretty fld), show rowdoc]
      ATerm _ -> do
            rowdoc <- ppLF RecordPrec wsub row
            fail $ unwords ["Could not prove field exists", show (pretty fld), show rowdoc]
      Lam _ _ _ -> fail "expected row value"
      Record _ ->  fail "expected row value"
      RecordModify{} ->  fail "expected row value"

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
