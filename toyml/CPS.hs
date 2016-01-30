module CPS where

import Prelude hiding (pi, abs)

import           Data.Set (Set)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import           Lang.LF
import           Terms

cps_ml :: (LiftClosed γ, ?nms :: Set String, ?hyps :: H γ, ?soln :: LFSoln LF)
       => LF γ TERM -- ^ ML term to transform  :: ml
       -> LF γ TERM -- ^ static continuation :: (v ==> tm)
       -> M (LF γ TERM) -- ^ cps transformed term :: tm
cps_ml (termView -> VConst (CNm "ml_var") [x]) k_top =
  (return k_top) @@ (return x)

cps_ml (termView -> VConst "ml_tt" []) k_top =
  "letval" @@ "tt" @@ (return $ k_top)

cps_ml (termView -> VConst "ml_app" [e1,e2]) k_top =
 "letcont" @@ (return k_top)
           @@ (λ "k" kv $ \k ->
   cps_ml (weak e1) =<< (λ "z1" v $ \z1 ->
     cps_ml (weak $ weak e2) =<< (λ "z2" v $ \z2 ->
                      "app" @@ (weak <$> var z1)
                            @@ (weak . weak <$> var k)
                            @@ (var z2))))

cps_ml (termView -> VConst "ml_pair" [e1,e2]) k_top =
  cps_ml e1 =<< (λ "z1" v $ \z1 ->
    cps_ml (weak e2) =<< (λ "z2" v $ \z2 ->
      "letval" @@ ("pair" @@ (weak <$> var z1) @@ (var z2))
               @@ (return $ weak $ weak k_top)))

cps_ml (termView -> VConst "ml_inl" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "letval" @@ ("inl" @@ var z)
              @@ (return $ weak k_top))

cps_ml (termView -> VConst "ml_inr" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "letval" @@ ("inr" @@ var z)
              @@ (return $ weak k_top))

cps_ml (termView -> VConst "ml_fst" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "let_prj1" @@ var z
                @@ (return $ weak k_top))

cps_ml (termView -> VConst "ml_snd" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "let_prj2" @@ var z
                @@ (return $ weak k_top))

cps_ml (termView -> VConst "ml_lam" [e]) k_top =
  "letval" @@ ("lam" @@ (λ "k" kv $ \k ->
                          (λ "x" v $ \x -> do
                            x' <- (return $ weak $ weak $ e) @@ (var x)
                            tailcps_ml x' =<< (weak <$> var k))))
           @@ (return k_top)

cps_ml (termView -> VConst "ml_letval" [e1,e2]) k_top =
  "letcont" @@ (λ "x" v $ \x -> do
                   x' <- (return $ weak $ e2) @@ (var x)
                   cps_ml x' (weak k_top))
            @@ (λ "j" kv $ \j -> do
                   tailcps_ml (weak $ e1) =<< (var j))

cps_ml (termView -> VConst "ml_case" [e,el,er]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
    "letcont" @@ (return $ weak $ k_top)
      @@ (λ "j" kv $ \j ->
      "letcont" @@ (λ "x1" v $ \x1 -> do
                         el' <- (return $ weak $ weak $ weak el) @@ var x1
                         tailcps_ml el' =<< (weak <$> var j))
        @@ (λ "k1" kv $ \k1 ->
          "letcont" @@ (λ "x2" v $ \x2 -> do
                           er' <- (return $ weak $ weak $ weak $ weak er) @@ var x2
                           tailcps_ml er' =<< (weak . weak <$> var j))
            @@ (λ "k2" kv $ \k2 ->
               "case" @@ (weak . weak . weak <$> var z) @@ (weak <$> var k1) @@ var k2))))

cps_ml tm _ = do
  tm_doc <- ppLF TopPrec WeakRefl tm
  fail $ show $ vcat
     [ text "Unexpected term in cps_ml:"
     , indent 2 tm_doc
     ]

tailcps_ml :: (LiftClosed γ, ?nms :: Set String, ?hyps :: H γ, ?soln :: LFSoln LF)
       => LF γ TERM -- ^ ML term to transform :: ml
       -> LF γ TERM -- ^ a continuation variable :: kv
       -> M (LF γ TERM) -- ^ result :: tm

tailcps_ml (termView -> VConst "ml_var" [x]) k_top =
  "enter" @@ return k_top @@ return x

tailcps_ml (termView -> VConst "ml_app" [e1,e2]) k_top =
  cps_ml e1 =<< (λ "x1" v $ \x1 ->
    cps_ml (weak e2) =<< (λ "x2" v $ \x2 ->
      "app" @@ (weak <$> var x1) @@ (return $ weak $ weak k_top) @@ (var x2)))

tailcps_ml (termView -> VConst "ml_lam" [e]) k_top =
  "letval" @@ ("lam" @@ (λ "j" kv $ \j -> λ "x" v $ \x -> do
                           e' <- (return $ weak $ weak e) @@ (var x)
                           tailcps_ml e' =<< (weak <$> var j)))
           @@ (λ "f" v $ \f -> "enter" @@ (return $ weak $ k_top) @@ (var f))

tailcps_ml (termView -> VConst "ml_pair" [e1,e2]) k_top =
  cps_ml e1 =<< (λ "x1" v $ \x1 ->
    cps_ml (weak e2) =<< (λ "x2" v $ \x2 ->
      "letval" @@ ("pair" @@ (weak <$> var x1) @@ (var x2))
               @@ (λ "x" v $ \x ->
                     "enter" @@ (return $ weak $ weak $ weak $ k_top) @@ (var x))))

tailcps_ml (termView -> VConst "ml_inl" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "letval" @@ ("inl" @@ var z)
              @@ (λ "x" v $ \x ->
                    "enter" @@ (return $ weak $ weak k_top) @@ var x))

tailcps_ml (termView -> VConst "ml_inr" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "letval" @@ ("inr" @@ var z)
              @@ (λ "x" v $ \x ->
                    "enter" @@ (return $ weak $ weak k_top) @@ var x))

tailcps_ml (termView -> VConst "ml_tt" []) k_top =
  "letval" @@ "tt"
           @@ (λ "x" v $ \x ->
                "enter" @@ (return $ weak k_top) @@ var x)

tailcps_ml (termView -> VConst "ml_fst" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "let_prj1" @@ var z
                @@ (λ "x" v $ \x ->
                     "enter" @@ (return $ weak $ weak k_top) @@ var x))

tailcps_ml (termView -> VConst "ml_snd" [e]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
     "let_prj2" @@ var z
                @@ (λ "x" v $ \x ->
                     "enter" @@ (return $ weak $ weak k_top) @@ var x))

tailcps_ml (termView -> VConst "ml_letval" [e1,e2]) k_top =
  "letcont" @@ (λ "x" v $ \x -> do
                   e2' <- (return $ weak $ e2) @@ (var x)
                   tailcps_ml e2' (weak k_top))
            @@ (λ "j" kv $ \j -> do
                   tailcps_ml (weak e1) =<< (var j))

tailcps_ml (termView -> VConst "ml_case" [e,el,er]) k_top =
  cps_ml e =<< (λ "z" v $ \z ->
    "letcont" @@ (λ "x1" v $ \x1 -> do
                     el' <- (return $ weak $ weak el) @@ (var x1)
                     tailcps_ml el' (weak $ weak k_top))
      @@ (λ "k1" kv $ \k1 ->
        "letcont" @@ (λ "x2" v $ \x2 -> do
                        er' <- (return $ weak $ weak $ weak er) @@ (var x2)
                        tailcps_ml er' (weak $ weak $ weak k_top))
           @@ (λ "k2" kv $ \k2 ->
                "case" @@ (weak . weak <$> var z)
                       @@ (weak <$> var k1)
                       @@ (var k2))))

tailcps_ml tm _ = do
  tm_doc <- ppLF TopPrec WeakRefl tm
  fail $ show $ vcat
     [ text "Unexpected term in tailcps_ml:"
     , indent 2 tm_doc
     ]

