module Lang.LF.Internal.Print where

import           Data.Set (Set)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps


displayLF :: (WFContext γ, LFModel f m, ?nms :: Set String, ?hyps::Hyps f γ, ?soln :: LFSoln f)
          => f γ s -> m String
displayLF x = show <$> ppLF TopPrec x

prettyLF
      :: (WFContext γ, LFModel f m, ?nms::Set String, ?hyps::Hyps f γ, ?soln :: LFSoln f)
      => Prec
      -> f γ s
      -> m Doc
prettyLF prec x =
  case unfoldLF x of
    Weak x -> weakenCtx (prettyLF prec x)
    Type -> return $ text "Type"
    KPi nm a k
      | freeVar (B ()) k -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec a
         kdoc <- extendCtx nm QPi a $ ppLF TopPrec k
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> adoc <+> comma <> nest 2 (softline <> kdoc)
      | otherwise -> do
         adoc <- ppLF BinderPrec a
         let ?hyps = extendHyps ?hyps "_" QPi (error "unbound name!")
         kdoc <- ppLF TopPrec k
         return $ group $ (if prec /= TopPrec then parens else id) $
           align (adoc <+> text "⇒" <> line <> kdoc)
    AType x -> group . (linebreak <>) . hang 2 <$> (ppLF prec x)
    TyPi nm a1 a2
      | freeVar (B ()) a2 -> do
         let nm' = freshName nm
         a1doc <- ppLF BinderPrec a1
         a2doc <- extendCtx nm QPi a1 $ ppLF TopPrec a2
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> a1doc <> comma <> nest 2 (softline <> a2doc)
      | otherwise -> do
         a1doc <- ppLF BinderPrec a1
         let ?hyps = extendHyps ?hyps "_" QPi (error "unbound name!")
         a2doc <- ppLF TopPrec a2
         return $! group $ (if prec /= TopPrec then parens else id) $
           (align (a1doc <+> text "⇒" <> softline <> a2doc))
    TyConst x -> return $ pretty x
    TyApp p a -> do
         pdoc <- ppLF AppLPrec p
         adoc <- ppLF AppRPrec a
         return $! group $ (if prec == AppRPrec then parens else id) $
            (pdoc <> line <> adoc)
    ATerm x
      | prec == TopPrec ->
           group . (linebreak <>) . hang 2 <$> (ppLF prec x)
      | otherwise -> hang 2 <$> ppLF prec x
    Lam nm a m -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec a
         mdoc <- extendCtx nm QLam a $ ppLF TopPrec m
         return $! (if prec /= TopPrec then parens else id) $
           text "λ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> mdoc)
    Const x -> return $ pretty x
    App m1 m2 -> do
         m1doc <- ppLF AppLPrec m1
         m2doc <- ppLF AppRPrec m2
         return $! group $ (if prec == AppRPrec then parens else id) $
            (m1doc <> line <> m2doc)
    Var v ->
      let (nm,_,_) = lookupVar ?hyps (B v)
       in return $ text nm

    UVar u -> return (text "#" <> pretty u)

    Unify r1 r2 -> do
         r1doc <- ppLF TopPrec r1
         r2doc <- ppLF TopPrec r2
         return $ group (r1doc <+> text "=" <> line <> r2doc)

    And [] -> return $ text "⊤"
    And cs -> do
         cs' <- mapM (ppLF TopPrec) cs
         return $ align $ cat $ punctuate (text " ∧ ") cs'

    Forall nm a c -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec a
         cdoc <- extendCtx nm QForall a $ ppLF TopPrec c
         return $ (if prec /= TopPrec then parens else id) $
           text "∀" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Exists nm a c -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec a
         cdoc <- extendCtx nm QExists a $ ppLF TopPrec c
         return $ (if prec /= TopPrec then parens else id) $
           text "∃" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Sigma nm a g -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec a
         gdoc <- extendCtx nm QSigma a $ ppLF TopPrec g
         return $ (if prec /= TopPrec then parens else id) $
           text "Σ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> gdoc)

    Fail -> do
         return $ text "⊥"

    Goal m c -> do
         mdoc <- ppLF TopPrec m
         cdoc <- ppLF TopPrec c
         return $ group $
           text "{" <+> mdoc <+> text "|" <> nest 2 (softline <> cdoc <+> text "}")
