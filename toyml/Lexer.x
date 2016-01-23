{
{-# OPTIONS_GHC -Wwarn #-}

module Lexer
( alexMonadScan
, Token(..)
, runlexer
)where

import Control.Monad

import Debug.Trace
}

%wrapper "monadUserState"

$digit = 0-9
$alpha = [A-Z a-z]
$lower = [a-z]
$upper = [A-Z]
$hexdigit = [$digit a-f A-F]


tokens :-

<comment> \(\*                       { pushComment }
<comment> \*\)                       { popComment }
<comment> [$white]+                  { skip }
<comment> . [^\)\(\*]*               { skip }

<0>  \(\*                            { pushComment }
<0>  \*\)                            { popComment }
<0>  [$white]+                       { skip }
<0>  $lower [$alpha $digit \_]*      { raw }



{
data Token
  = Raw String
  | EOF
 deriving Show

type AlexUserState = Int -- Comment depth
alexInitUserState = 0

raw :: AlexAction Token
raw (_,_,_,str) _len =
   return $ Raw str

pushComment :: AlexAction Token
pushComment _ _ = do
  n <- alexGetUser
  alexSetUser (n+1)
  trace ("push: " ++ show (n+1)) $ do
    alexSetStartCode comment
    alexMonadScan

popComment :: AlexAction Token
popComment _ _ = do
  n <- alexGetUser
  if n > 0 then do
    alexSetUser (n-1)
    trace ("push: " ++ show (n-1)) $ do
      when (n == 1) (alexSetStartCode 0)
      alexMonadScan
  else
    fail "Unexpected end of comment"

alexGetUser :: Alex AlexUserState
alexGetUser = Alex $ \s -> Right (s, alex_ust s)

alexSetUser :: AlexUserState -> Alex ()
alexSetUser u = Alex $ \s -> Right (s{ alex_ust = u} , ())

alexEOF :: Alex Token
alexEOF = do
  sc <- alexGetStartCode
  when (sc == comment) (alexError "unterminated comment")
  return EOF

-- | Initialize the parser with the given input string.
initAlexState :: String -> AlexState
initAlexState input = 
  AlexState {alex_pos = alexStartPos,
             alex_inp = input,
             alex_chr = '\n',
             alex_bytes = [],
             alex_ust = alexInitUserState,
             alex_scd = 0}

-- | Testing procedure that generates a list of tokens from a string input.
runlexer :: String -> [Token]
runlexer str = go (initAlexState str)
  where go st =
          case unAlex alexMonadScan st of
	        Left msg -> error msg
		Right (st',EOF) -> []
		Right (st',tok) -> tok : go st'

}
