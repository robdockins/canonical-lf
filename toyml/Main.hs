import           System.IO
import qualified Data.Map as Map
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.LF
import           Lang.LF.Tree hiding (M)

import           CPS
import           Grammar
import           Lexer
import           Scope
import           Simplify
import           Terms
import           ToyTC

main :: IO ()
main = do
  str <- hGetContents stdin
  print $ runlexer str
  let (errs, mast) = toyMLParser "<stdin>" str
  print (errs, mast)
  case mast of
    Nothing -> putStrLn "Parse failed"
    Just ast -> do
      let mlTerm  = mkTerm sig $ scopeAnalysis Map.empty ast
      let g       = runM sig $ runTC mlTerm
      let cpsTerm = mkTerm sig $ tailcps_ml mlTerm =<< "halt"
      let x       = mkTerm sig $ do
                      let ?ischeap = InlineHeuristic (\_ -> True)
                      simplifier BindEmpty cpsTerm

      showTm mlTerm
      showGoal g
      showTm cpsTerm
      showTm x

showGoal :: LF E GOAL -> IO ()
showGoal g = inEmptyCtx $ do
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $
      ppLF TopPrec WeakRefl g
   putStrLn ""

showTm :: LF E TERM -> IO ()
showTm x = inEmptyCtx $ do
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $
      ppLF TopPrec WeakRefl x
   putStrLn ""
   displayIO stdout $ renderSmart 0.7 80 $ runM sig $
      (ppLF TopPrec WeakRefl =<< inferType WeakRefl x)
   putStrLn ""

{-

--  "letval" @@ "tt" @@ (λ "x" v $ \x -> "tm_var" @@ var x)

testTerm :: LF E TERM
testTerm = mkTerm sig $

 --  "ml_app" @@ ("ml_var" @@ "g'")
 --           @@ ("ml_app" @@ ("ml_var" @@ "g")
 --                        @@ ("ml_app" @@ body
 --                                     @@ ("ml_var" @@ "y")))
 -- where
 --  body = inEmptyCtx $
 --   "ml_lam" @@ (λ "x" v $ \x ->
 --     "ml_case" @@ ("ml_var" @@ var x)
 --               @@ (λ "l" v $ \l ->
 --                      "ml_pair" @@ ("ml_var" @@ var l) @@ ("ml_var" @@ "x3")
 --                  )
 --               @@ (λ "r" v $ \_r ->
 --                      "ml_app" @@ ("ml_var" @@ "g''") @@ ("ml_var" @@ var x)
 --                  )
 --   )

  "ml_fst" @@
     ("ml_app" @@ ("ml_lam" @@ (λ "x" v $ \x ->
                      "ml_pair" @@ ("ml_app" @@ ("ml_var" @@ "g")
                                             @@ ("ml_var" @@ var x))
                                @@ ("ml_var" @@ var x)
                  ))
               @@ ("ml_var" @@ "y"))

  -- "ml_lam" @@ (λ "x" v $ \x ->
  --                "ml_app" @@ ("ml_var" @@ "f")
  --                         @@ ("ml_pair" @@ ("ml_var" @@ (var x)) @@ ("ml_var" @@ "y")))

cpsTerm :: LF E TERM
cpsTerm = mkTerm sig $ do
  tailcps_ml testTerm =<< "halt"

simplTerm :: LF E TERM
simplTerm = mkTerm sig $ do
  let ?ischeap = InlineHeuristic (\_ -> False)
  simplifier BindEmpty cpsTerm

-}
