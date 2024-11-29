module LambdaC.Parser

import Data.List
import Derive.Show
import Generics.Derive
import LambdaC.Effect
import LambdaC.File
import LambdaC.Lexer
import System
import System.File
import Text.Parser

%default total
%language ElabReflection

%hide Generics.Derive.Show

token : Token -> Grammar _ Token True Token
token tok = terminal "unexpected token" (\t => if t == tok then pure t else Nothing)

bracket : Side -> BracketType -> Grammar _ Token True Bracket
bracket side ty = let brac = Brac side ty in ignore (token (TBrac brac)) >> pure brac

keyword : Keyword -> Grammar _ Token True Keyword
keyword key = ignore (token (TKeyword key)) >> pure key

anyKeyword : Grammar _ Token True Keyword
anyKeyword = terminal "expected a keyword" (\t =>
  case t of
    TKeyword key => pure key
    _ => Nothing)

identifier : Grammar _ Token True String
identifier = terminal "expected an identifier" (\t =>
  case t of
    TID id => pure id
    _ => Nothing)

nat : Grammar _ Token True Nat
nat = terminal "expected a natural number" (\t =>
  case t of
    TNat n => pure n
    _ => Nothing)

double : Grammar _ Token True Double
double = terminal "expected a floating-point number" (\t =>
  case t of
    TDouble n => pure n
    _ => Nothing)

parenthesized : {consumes : Bool} -> Grammar s Token consumes a -> Grammar s Token True a
parenthesized = between (bracket Open Par) (bracket Close Par)
bracketed : {consumes : Bool} -> Grammar s Token consumes a -> Grammar s Token True a
bracketed = between (bracket Open Square) (bracket Close Square)
braced : {consumes : Bool} -> Grammar s Token consumes a -> Grammar s Token True a
braced = between (bracket Open Curly) (bracket Close Curly)

||| A sort of "pre-syntax." Notably, this is a first-order named representation.
||| Basically, these are s-expressions.
public export
data PreSyntax = PSKeyword Keyword | PSID String | PSNat Nat | PSList (Maybe BracketType) (List PreSyntax) | PSDouble Double

%runElab derive "PreSyntax" [Generic, Meta, Show]

form : Grammar _ Token True PreSyntax
form = assert_total $ -- TODO
  map PSKeyword anyKeyword <|>
  map PSID identifier <|>
  map PSNat nat <|>
  map PSDouble double <|>
  map (PSList $ Just Par) (parenthesized (many form)) <|>
  map (PSList $ Just Square) (bracketed (many form)) <|>
  map (PSList $ Just Curly) (braced (many form))

grammar : Grammar _ Token False PreSyntax
grammar = map (PSList Nothing) (many form)

export
parse : List (WithBounds Token) -> Either (List1 (ParsingError Token)) PreSyntax
parse toks = do
  (ps, []) <- parse grammar toks
  | (ps, remaining@(tok :: _)) => Left $ (Error "unexpected input remaining: \{show remaining}" (Just tok.bounds)) ::: [Error "parsed so far: \{show ps}" Nothing]
  pure ps

covering
main : IO ()
main = do
  input <- readAllInput
  tokens <- case getTokens input of
    Left err => die err
    Right tokens => pure tokens
  case parse (withoutComments tokens) of
    Left errs => die (show errs)
    Right preSyntax => printLn preSyntax
