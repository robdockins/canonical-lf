import           System.IO
--import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

--import           Ucps
import           Lexer

--import           Lang.LF
--import           Lang.LF.Tree hiding (M)

main :: IO ()
main = do
  str <- hGetContents stdin
  print $ runlexer str

-- main = inEmptyCtx $ do
   -- let x :: LF E TERM
   --     x = simplTerm
   -- displayIO stdout $ renderSmart 0.7 80 $ runM sig $ ppLF TopPrec WeakRefl x
   -- putStrLn ""
   -- displayIO stdout $ renderSmart 0.7 80 $ runM sig $ (ppLF TopPrec WeakRefl =<< inferType WeakRefl x)
   -- putStrLn ""

