module Lang.LF.Internal.Print where

import           Control.Arrow ( (***) )
import           Data.Set (Set)
import qualified Data.Map.Strict as Map
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.LF.Internal.Model
import Lang.LF.Internal.Hyps
import Lang.LF.Internal.Weak

displayLF :: (LFModel f m, ?nms :: Set String, ?hyps::Hyps f γ, ?soln :: LFSoln f)
          => f γ s -> m String
displayLF x = show <$> ppLF TopPrec WeakRefl x

prettyRecord :: Monad m => [(Doc, m Doc)] -> m Doc
prettyRecord flds = do
   flds' <- go flds
   return $ group $ align $ text "{" <+> flds' <> text "}"
 where go [] = return softline
       go [x] = go1 x
       go (x:xs) = do
             x' <- go1 x
             xs' <- go xs
             return (x' <> softline <> text "," <+> xs')

       go1 (nm,x) = do
             x' <- x
             return $ nm <+> text ":"  <+> x'

prettyLF
      :: (LFModel f m, ?nms::Set String, ?hyps::Hyps f γ', ?soln :: LFSoln f)
      => Prec
      -> Weakening γ γ'
      -> f γ s
      -> m Doc
prettyLF prec w x =
  case unfoldLF x of
    Weak w' x -> ppLF prec (weakCompose w w') x
    Type -> return $ text "Type"
    KPi nm a k
      | freeVar B k -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec w a
         kdoc <- extendCtx nm QPi (weaken w a) $ ppLF TopPrec (WeakSkip w) k
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> adoc <+> comma <> nest 2 (softline <> kdoc)
      | otherwise -> do
         adoc <- ppLF BinderPrec w a
         let ?hyps = extendHyps ?hyps "_" QPi (error "unbound name!")
         kdoc <- ppLF TopPrec (WeakSkip w) k
         return $ group $ (if prec /= TopPrec then parens else id) $
           align (adoc <+> text "⇒" <> line <> kdoc)
    AType x -> group . (linebreak <>) . hang 2 <$> (ppLF prec w x)
    TyPi nm a1 a2
      | freeVar B a2 -> do
         let nm' = freshName nm
         a1doc <- ppLF BinderPrec w a1
         a2doc <- extendCtx nm QPi (weaken w a1) $ ppLF TopPrec (WeakSkip w) a2
         return $ (if prec /= TopPrec then parens else id) $
           text "Π" <> text nm' <+> colon <+> a1doc <> comma <> nest 2 (softline <> a2doc)
      | otherwise -> do
         a1doc <- ppLF BinderPrec w a1
         let ?hyps = extendHyps ?hyps "_" QPi (error "unbound name!")
         a2doc <- ppLF TopPrec (WeakSkip w) a2
         return $! group $ (if prec /= TopPrec then parens else id) $
           (align (a1doc <+> text "⇒" <> softline <> a2doc))
    TyRecord flds -> do
      prettyRecord $ map (pretty *** ppLF TopPrec w) $ Map.toList flds

    TyConst x -> return $ pretty x
    TyApp p a -> do
         pdoc <- ppLF AppLPrec w p
         adoc <- ppLF AppRPrec w a
         return $! group $ (if prec == AppRPrec then parens else id) $
            (pdoc <> line <> adoc)
    ATerm x
      | prec == TopPrec ->
           group . (linebreak <>) . hang 2 <$> (ppLF prec w x)
      | otherwise -> hang 2 <$> ppLF prec w x
    Lam nm a m -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec w a
         mdoc <- extendCtx nm QLam (weaken w a) $ ppLF TopPrec (WeakSkip w) m
         return $! (if prec /= TopPrec then parens else id) $
           text "λ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> mdoc)
    Record flds -> do
      prettyRecord $ map (pretty *** ppLF TopPrec w) $ Map.toList flds
    Const x -> return $ pretty x
    App m1 m2 -> do
         m1doc <- ppLF AppLPrec w m1
         m2doc <- ppLF AppRPrec w m2
         return $! group $ (if prec == AppRPrec then parens else id) $
            (m1doc <> line <> m2doc)
    Var ->
      let (nm,_,_) = lookupVar ?hyps (weakenVar w B)
       in return $ text nm

    UVar u -> return (text "#" <> pretty u)

    Project x fld -> do
         xdoc <- ppLF AppLPrec w x
         return $ xdoc <> text "->" <> pretty fld

    Unify r1 r2 -> do
         r1doc <- ppLF TopPrec w r1
         r2doc <- ppLF TopPrec w r2
         return $ group (r1doc <+> text "=" <> line <> r2doc)

    And [] -> return $ text "⊤"
    And cs -> do
         cs' <- mapM (ppLF TopPrec w) cs
         return $ align $ cat $ punctuate (text " ∧ ") cs'

    Forall nm a c -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec w a
         cdoc <- extendCtx nm QForall (weaken w a) $ ppLF TopPrec (WeakSkip w) c
         return $ (if prec /= TopPrec then parens else id) $
           text "∀" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Exists nm a c -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec w a
         cdoc <- extendCtx nm QExists (weaken w a) $ ppLF TopPrec (WeakSkip w) c
         return $ (if prec /= TopPrec then parens else id) $
           text "∃" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> cdoc)

    Sigma nm a g -> do
         let nm' = freshName nm
         adoc <- ppLF BinderPrec w a
         gdoc <- extendCtx nm QSigma (weaken w a) $ ppLF TopPrec (WeakSkip w) g
         return $ (if prec /= TopPrec then parens else id) $
           text "Σ" <> text nm' <+> colon <+> adoc <> comma <> nest 2 (softline <> gdoc)

    Fail -> do
         return $ text "⊥"

    Goal m c -> do
         mdoc <- ppLF TopPrec w m
         cdoc <- ppLF TopPrec w c
         return $ group $
           text "{" <+> mdoc <+> text "|" <> nest 2 (softline <> cdoc <+> text "}")
