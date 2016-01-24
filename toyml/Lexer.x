{
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wwarn #-}

module Lexer
( alexMonadScan
, Token(..)
, AlexState(..)
, Alex(..)
, runlexer
, initAlexState
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
$identchar = [$alpha $digit _ \']

@ident = $alpha ($identchar)*

tokens :-

<comment> \(\*                       { pushComment }
<comment> \*\)                       { popComment }
<comment> [$white]+                  { skip }
<comment> . [^\)\(\*]*               { skip }

<0>  \(\*                            { pushComment }
<0>  \*\)                            { popComment }
<0>  $white+                         { skip }
<0>  "fn"                            { emit FN }
<0>  "case"                          { emit CASE }
<0>  "of"                            { emit OF }
<0>  "end"                           { emit END }
<0>  "inl"                           { emit INL }
<0>  "inr"                           { emit INR }
<0>  "fst"                           { emit FST }
<0>  "snd"                           { emit SND }
<0>  "let"                           { emit LET }
<0>  "in"                            { emit IN }
<0>  "()"                            { emit TT }
<0>  "=>"                            { emit FATARROW }
<0>  "->"                            { emit ARROW }
<0>  "="                             { emit EQUAL }
<0>  "|"                             { emit VBAR }
<0>  ","                             { emit COMMA }
<0>  "("                             { emit LPAREN }
<0>  ")"                             { emit RPAREN }
<0>  @ident                          { ident }

{
data Token
  = IDENT String
  | FN
  | CASE
  | OF
  | LET
  | IN
  | END
  | INL
  | INR
  | FST
  | SND
  | VBAR
  | ARROW
  | COMMA
  | FATARROW
  | EQUAL
  | LPAREN
  | RPAREN
  | TT
  | EOF
 deriving Show

emit :: Token -> AlexAction Token
emit t _ _ = return t

type AlexUserState = Int -- Comment depth
alexInitUserState = 0

ident :: AlexAction Token
ident (_,_,_,str) len =
    return $ IDENT (take len str)

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

deriving instance Show AlexState
}
