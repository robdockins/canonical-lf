{
module Grammar
( toyMLParser
, AST(..)
) where

import Lexer
}

%tokentype{ Token }
%error { parseError }

%token IDENT     { IDENT _ }
%token FN        { FN }
%token CASE      { CASE }
%token OF        { OF }
%token END       { END }
%token INL       { INL }
%token INR       { INR }
%token FST       { FST }
%token SND       { SND }
%token LET       { LET }
%token IN        { IN }
%token '='       { EQUAL }
%token '|'       { VBAR }
%token '->'      { ARROW }
%token ','       { COMMA }
%token '=>'      { FATARROW }
%token '('       { LPAREN }
%token ')'       { RPAREN }
%token '()'      { TT }
%token EOF       { EOF }

%monad { P }{ thenP }{ returnP }
%lexer { lexer } { EOF }

%name exprParser expr

%%

atomexpr :: { AST }
  : '(' expr ')'              { $2 }
  | IDENT                     { Ident (ident $1) }
  | '(' expr ',' expr ')'     { Pair $2 $4 }
  | '()'                      { Tt }
  | CASE expr OF
     INL IDENT '=>' expr
     '|'
     INR IDENT '=>' expr
     END                      { Case $2 (ident $5,$7) (ident $10,$12)}

appexpr :: { AST }
  : atomexpr                  { $1 }
  | appexpr atomexpr          { App $1 $2 }


expr :: { AST }
  : appexpr                   { $1 }
  | FN IDENT '=>' expr        { Fn (ident $2) $4 }
  | LET IDENT '=' expr
    IN expr                   { Letval (ident $2) $4 $6 }
  | INL expr                  { Inl $2 }
  | INR expr                  { Inr $2 }
  | FST expr                  { Fst $2 }
  | SND expr                  { Snd $2 }

{
data AST
  = Fn String AST
  | Ident String
  | Letval String AST AST
  | Tt
  | App AST AST
  | Case AST (String,AST) (String,AST)
  | Pair AST AST
  | Inl AST
  | Inr AST
  | Fst AST
  | Snd AST
 deriving (Show)

-- | Parser state record
data ParseState
 = ParseState
   { alex_state    :: AlexState       -- ^ Internal state of the lexer
   , parse_file    :: FilePath        -- ^ Name of the file we are parsing
   , parse_errors  :: [String]        -- ^ Accumulated list of parse errors
   , lexical_error :: Bool            -- ^ Did the lexer give us an error?
   }
 deriving (Show)

initParseState :: FilePath -> String -> ParseState
initParseState fp input =
  ParseState
  { alex_state    = initAlexState input
  , parse_file    = fp
  , parse_errors  = []
  , lexical_error = False
  }

newtype P a = P { unP :: ParseState -> (ParseState, Maybe a) }

thenP m f = P $ \st ->
    let (st', x) = unP m st
     in case x of
          Nothing -> (st', Nothing)
          Just a  -> unP (f a) st'

returnP x = P $ \st -> (st, Just x)

failP msg = P $ \st ->
   (st{ parse_errors = parse_errors st ++ [msg]}, Nothing)

errorP :: String -> P a
errorP msg = P $ \st -> (st{ parse_errors = parse_errors st ++ [msg]}, Nothing)

parseError :: Token -> P a
parseError _tk = errorP "syntax error"

instance Monad P where
  (>>=) = thenP
  return = returnP
  fail = failP

instance Applicative P where
  pure = returnP

instance Functor P where
  fmap f m = m >>= return . f

ident :: Token -> String
ident (IDENT x) = x

lexer :: (Token -> P a) -> P a
lexer k = P $ \st ->
  case unAlex alexMonadScan (alex_state st) of
    Left msg ->
      let st' = st{ parse_errors = parse_errors st ++ [msg]
                  , lexical_error = True
                  }
       in (st', Nothing)
    Right (ast', tok) ->
      let st' = st{ alex_state = ast' }
       in unP (k tok) st'

toyMLParser
   :: FilePath
   -> String
   -> ([String], Maybe AST)
toyMLParser fp str =
  let (st', x) = unP exprParser (initParseState fp str)
   in (parse_errors st', x)
}
