import           System.IO
import qualified Data.Map as Map
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Ucps
import           Lexer
import           Grammar
import           ToyTC
import           Scope

import           Lang.LF
import           Lang.LF.Tree hiding (M)

main :: IO ()
main = do
  str <- hGetContents stdin
  print $ runlexer str
  let (errs, mast) = toyMLParser "<stdin>" str
  print (errs, mast)
  case mast of
    Nothing -> putStrLn "Parse failed"
    Just ast -> inEmptyCtx $ do
      let mlTerm  = mkTerm sig $ scopeAnalysis Map.empty ast
      let g       = runM sig $ inEmptyCtx $ runTC mlTerm
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

