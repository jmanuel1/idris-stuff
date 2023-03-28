||| Type-safe format function, with and without dependent types.
module Format

%default total

||| Dependently typed patterns.
data DepPat : Type where
  LitP : String -> DepPat
  EolP : DepPat
  IntP : DepPat
  StrP : DepPat

formatType : List DepPat -> Type
formatType [] = ()
formatType (LitP str :: pats) = formatType pats
formatType (EolP :: pats) = formatType pats
formatType (IntP :: pats) = (Integer, formatType pats)
formatType (StrP :: pats) = (String, formatType pats)

formatDep' : (pats : List DepPat) -> formatType pats -> String
formatDep' [] _ = ""
formatDep' (LitP str :: pats) args = str ++ formatDep' pats args
formatDep' (EolP :: pats) args = "\n" ++ formatDep' pats args
formatDep' (IntP :: pats) (i, args) = cast i ++ formatDep' pats args
formatDep' (StrP :: pats) (str, args) = str ++ formatDep' pats args

-- TODO: Use HVect so that this isn't a repeat of formatType
-- TODO: this
-- recCurryType : List DepPat -> Type -> Type
-- recCurryType [] t = t
-- recCurryType (LitP str :: pats) t = recCurryType pats t
-- recCurryType (EolP :: pats) t = recCurryType pats t
-- recCurryType (IntP :: pats) t = (Integer -> recCurryType pats t)
-- recCurryType (StrP :: pats) t = (String -> recCurryType pats t)
--
-- formatDep : (pats : List DepPat) -> recCurryType pats String
-- formatDep' [] = formatDep' [] ()
-- formatDep' (LitP str :: pats) =

-- TODO: There is a Cont monad impl in src\Dual\Computation.idr

{-
Type-safe printf without dependent types:

Functional Unparsing
Olivier Danvy
https://www.brics.dk/RS/98/12/BRICS-RS-98-12.pdf
-}

-- Patterns

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

{-
Format> formatDep' [IntP, LitP " is ", StrP, EolP] (5, "five", ())
"5 is five\n"
Format> formatNonDep (int . lit " is " . str . eol) 5 "five"
"5 is five\n"
-}
