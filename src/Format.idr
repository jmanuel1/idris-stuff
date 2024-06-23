||| Type-safe format function, with and without dependent types.
module Format

%default total

||| Dependently typed patterns.
data DepPat : Type where
  LitP : String -> DepPat
  EolP : DepPat
  IntP : DepPat
  StrP : DepPat

-- Inspired by Brian McKenna's type-safe printf:
-- https://gist.github.com/puffnfresh/11202637 and
-- https://www.youtube.com/watch?v=fVBck2Zngjo
recCurryType : List DepPat -> Type
recCurryType [] = String
recCurryType (LitP str :: pats) = recCurryType pats
recCurryType (EolP :: pats) = recCurryType pats
recCurryType (IntP :: pats) = Integer -> recCurryType pats
recCurryType (StrP :: pats) = String -> recCurryType pats

formatDep' : (pats : List DepPat) -> String -> recCurryType pats
formatDep' [] acc = acc
formatDep' (LitP str :: pats) acc = formatDep' pats (acc ++ str)
formatDep' (EolP :: pats) acc = formatDep' pats (acc ++ "\n")
formatDep' (IntP :: pats) acc = \n => formatDep' pats (acc ++ cast n)
formatDep' (StrP :: pats) acc = \str => formatDep' pats (acc ++ str)

formatDep : (pats : List DepPat) -> recCurryType pats
formatDep pats = formatDep' pats ""

{-
Type-safe printf without dependent types:

Functional Unparsing
Olivier Danvy
https://www.brics.dk/RS/98/12/BRICS-RS-98-12.pdf
-}

-- Patterns
-- TODO: Use a indexed/delimited continuation monad

lit : String -> (String -> a) -> String -> a
lit str k acc = k (acc ++ str)

eol : (String -> a) -> String -> a
eol k acc = k (acc ++ "\n")

int : (String -> a) -> String -> Integer -> a
int k acc n = k (acc ++ cast n)

str : (String -> a) -> String -> String -> a
str k acc s = k (acc ++ s)

-- Patterns are composed with function composition (.)

formatNonDep : ((String -> String) -> String -> a) -> a
formatNonDep p = p id ""

%unbound_implicits off
nonDepExample : formatNonDep (int . lit " is " . str . eol) 5 "five" = "5 is five\n"
depExample : formatDep [IntP, LitP " is ", StrP, EolP] 5 "five" = "5 is five\n"
