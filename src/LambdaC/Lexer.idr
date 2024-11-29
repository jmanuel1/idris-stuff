module LambdaC.Lexer

import Data.List
import Derive.Eq
import Derive.Show
import Generics.Derive
import LambdaC.File
import System
import Text.Lexer

%default total
%language ElabReflection

%hide Generics.Derive.Eq
%hide Generics.Derive.Show

public export
data Side = Open | Close

%runElab derive "Side" [Generic, Meta, Eq, Show]

public export
data BracketType = Par | Square | Curly

%runElab derive "BracketType" [Generic, Meta, Eq, Show]

export
prettyPrintLeftBrac : Maybe BracketType -> String
prettyPrintLeftBrac Nothing = ""
prettyPrintLeftBrac (Just Par) = "("
prettyPrintLeftBrac (Just Square) = "["
prettyPrintLeftBrac (Just Curly) = "{"

export
prettyPrintRightBrac : Maybe BracketType -> String
prettyPrintRightBrac Nothing = ""
prettyPrintRightBrac (Just Par) = ")"
prettyPrintRightBrac (Just Square) = "]"
prettyPrintRightBrac (Just Curly) = "}"

public export
data Bracket = Brac Side BracketType

%runElab derive "Bracket" [Generic, Meta, Eq, Show]

public export
data Keyword = KEffect | KFunArrow | KTail | KDef | KStr | KExtern | KAmp | KFun | KInt | KHandle | KLambda | KBool | KVoid | KIf

%runElab derive "Keyword" [Generic, Meta, Eq, Show]

export
prettyPrint : Keyword -> String
prettyPrint KEffect = "effect"
prettyPrint KFunArrow = "->"
prettyPrint KTail = "tail"
prettyPrint KDef = "def"
prettyPrint KStr = "str"
prettyPrint KExtern = "extern"
prettyPrint KAmp = "&"
prettyPrint KFun = "fun"
prettyPrint KInt = "int"
prettyPrint KHandle = "handle"
prettyPrint KLambda = "lambda"
prettyPrint KBool = "bool"
prettyPrint KVoid = "void"
prettyPrint KIf = "if"

public export
data Token = TBrac Bracket | TKeyword Keyword | TID String | TNat Nat | TComment String | TDouble Double

%runElab derive "Token" [Generic, Meta, Eq, Show]

leftPar : Lexer
leftPar = exact "("
rightPar : Lexer
rightPar = exact ")"
leftSquare : Lexer
leftSquare = exact "["
rightSquare : Lexer
rightSquare = exact "]"
leftCurly : Lexer
leftCurly = exact "{"
rightCurly : Lexer
rightCurly = exact "}"

bracket : TokenMap Bracket
bracket = [
  (leftPar, const (Brac Open Par)),
  (rightPar, const (Brac Close Par)),
  (leftSquare, const (Brac Open Square)),
  (rightSquare, const (Brac Close Square)),
  (leftCurly, const (Brac Open Curly)),
  (rightCurly, const (Brac Close Curly))
]

identifierStart : Lexer
identifierStart = non (space <|> digit <|> oneOf "()[]{}\",'`;#|\\")

keyword : TokenMap Keyword
keyword = map (mapFst (<+> reject (digit <|> identifierStart))) [
  (exact "effect", const KEffect),
  (exact "->", const KFunArrow),
  (exact "tail", const KTail),
  (exact "def", const KDef),
  (exact "str", const KStr),
  (exact "extern", const KExtern),
  (exact "&", const KAmp),
  (exact "fun", const KFun),
  (exact "int", const KInt),
  (exact "handle", const KHandle),
  (exact "lambda", const KLambda),
  (exact "bool", const KBool),
  (exact "void", const KVoid),
  (exact "if", const KIf)
]

whitespace : Recognise ?
whitespace = opt spaces

||| Allowed characters are based on
||| https://docs.racket-lang.org/guide/symbols.html#:~:text=For%20reader%20input%2C%20any%20character%20can%20appear%20directly%20in%20an%20identifier%2C%20except%20for%20whitespace%20and%20the%20following%20special%20characters%3A.
identifier : TokenMap String
identifier = [
  (identifierStart <+> many (digit <|> identifierStart), id)
]

number : TokenMap $ Either Nat Double
number = [
  (digits <+> exact "." <+> digits, Right . cast),
  (digits, Left . cast)
]

lineComment : TokenMap String
lineComment = [
  (lineComment $ exact ";", id)
]

tokenGrammar : TokenMap Token
tokenGrammar = map (mapSnd (TBrac .)) bracket ++ map (mapSnd (TKeyword .)) keyword ++ map (mapSnd (TID .)) identifier ++ map (mapSnd (either TNat TDouble .)) number ++ map (mapSnd (TComment .)) lineComment

tokenGrammarIncludingWhitespace : TokenMap (Maybe Token)
tokenGrammarIncludingWhitespace = map (mapSnd (\f, t => Just (f t))) tokenGrammar ++ [(spaces, const Nothing)]

Interpolation Int where
  interpolate = show

catWithBoundsMaybes : List (WithBounds (Maybe Token)) -> List (WithBounds Token)
catWithBoundsMaybes [] = []
catWithBoundsMaybes (x :: xs) =
  let rest = catWithBoundsMaybes xs in
  case x.val of
    Just tok => { val := tok } x :: rest
    Nothing => rest

export
getTokens : String -> Either String (List (WithBounds Token))
getTokens str =
  let (tokens, line, col, rest) = lex tokenGrammarIncludingWhitespace str in
  if (rest == "") then pure $ catWithBoundsMaybes tokens else Left "bad token at \{line + 1}:\{col + 1}"

export
isComment : Token -> Bool
isComment (TComment _) = True
isComment _ = False

export
withoutComments : List (WithBounds Token) -> List (WithBounds Token)
withoutComments = filter (not . isComment . val)

covering
main : IO ()
main = do
  input <- readAllInput
  case getTokens input of
    Left err => die err
    Right tokens => printLn (map (.val) tokens)
