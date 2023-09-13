module LambdaC.Resolve

import Control.Monad.State
import Control.Relation
import Data.List
import Data.SortedMap
import Data.String
import Data.Zippable
-- import Deriving.Monoid
import Generics.Derive
import LambdaC.Effect
import LambdaC.FFI
import LambdaC.File
import LambdaC.Lexer
import LambdaC.Parser
import System
import Text.Parser

%default total
%language ElabReflection

-- %hide Generics.Derive.Monoid

record Env (0 stage : CompilationStage) where
  constructor MkEnv
  boundNames : SortedMap String (Expr stage)
  boundTyNames : SortedMap String (Ty stage)

-- %runElab derive "Env" [Generic, Generics.Derive.Monoid]

-- Semigroup (Env stage) where
--   env1 <+> env2 = { boundNames $= (<+> env2.boundNames), boundTyNames $= (<+> env2.boundTyNames) } env1

-- Monoid (Env stage) where
--   neutral = MkEnv { boundNames = neutral, boundTyNames = neutral }

emptyEnv : Env stage
emptyEnv = MkEnv { boundNames = empty, boundTyNames = empty }

extendTyEnv : String -> Ty stage -> Env stage -> Env stage
extendTyEnv name ty env = { boundTyNames $= insert name ty } env

covering
previewList : List PreSyntax -> String

covering
preview : PreSyntax -> String
preview (PSKeyword key) = prettyPrint key
preview (PSID ident) = ident
preview (PSList brac ps) = "\{prettyPrintLeftBrac brac}\{previewList (take 1 ps)} ...\{prettyPrintRightBrac brac}"
preview (PSNat n) = show n

previewList ps = joinBy " " $ map preview (take 5 ps)

-- export
covering
resolve : {auto 0 _ : stage `AtLeast` Effect} -> PreSyntax -> List PreSyntax -> Either String (Env stage -> Expr stage)

covering
effect : {auto 0 _ : stage `AtLeast` Effect} -> List PreSyntax -> List PreSyntax -> Either String (Env stage -> Expr stage)
effect [PSID name] rest = do
  restFun <- resolve (PSList Nothing rest) []
  pure $ \env => TyDecl (EffectTy []) (\eff => restFun (extendTyEnv name (NamedTy eff) env))
effect ps _ = Left "bad syntax in effect signature: unexpected \{previewList ps}"

resolve (PSList (Just Par) (PSKeyword KEffect :: ps)) rest = effect ps rest
resolve ps _ = Left "bad syntax: unexpected \{preview ps}"

Interpolation Nat where
  interpolate = show

fresh : State Nat String
fresh = do
  name <- pure "#gen\{!get}"
  modify (+ 1)
  pure name

covering
printType : Ty Print -> State Nat String

covering
printCType : CType (Ty Print) -> State Nat String
printCType (TInt Signed Size8) = pure "(int 8)"
printCType (TInt Signed Size16) = pure "(int 16)"
printCType (TInt Signed Size32) = pure "(int 32)"
printCType (TInt Signed Size64) = pure "(int 64)"
printCType (TInt Signed SizeShort) = pure "(int short)"
printCType (TInt Signed SizeDefault) = pure "int"
printCType (TInt Signed SizeLong) = pure "(int long)"
printCType (TInt Signed SizeLongLong) = pure "(int long long)"
printCType (TInt Unsigned Size8) = pure "(int unsigned 8)"
printCType (TInt Unsigned Size16) = pure "(int unsigned 16)"
printCType (TInt Unsigned Size32) = pure "(int unsigned 32)"
printCType (TInt Unsigned Size64) = pure "(int unsigned 64)"
printCType (TInt Unsigned SizeShort) = pure "(int unsigned short)"
printCType (TInt Unsigned SizeDefault) = pure "(int unsigned)"
printCType (TInt Unsigned SizeLong) = pure "(int unsigned long)"
printCType (TInt Unsigned SizeLongLong) = pure "(int unsigned long long)"
printCType TChar = pure "char"
printCType (TFloat FSize32) = pure "(float 32)"
printCType (TFloat FSize64) = pure "(float 64)"
printCType TString = pure "str"
printCType (TPtr x) = pure "(& \{!(printType x)})"
printCType TAnyPtr = pure "&"
-- FIXME: Show might not roundtrip with the syntax
printCType (TRawType str) = pure "(raw-type \{show str})"
printCType (xs :->* x) = pure "(->* \{joinBy " " !(traverse printCType xs)} \{!(printCType x)})"
printCType (TStruct xs) = ?pt_15
printCType (TUnion xs) = ?pt_16

printType (CTy t) = printCType t
printType UnitTy = ?pt_1
printType (SumTy xs) = ?pt_2
printType (x :* y) = ?pt_3
printType (xs :-> x) = ?pt_4
printType (EffectTy xs) = ?pt_5
printType (NamedTy str) = ?pt_6

joinBy : String -> Vect n String -> String
joinBy s [] = ""
joinBy s (x :: xs) = "\{x}\{s}\{joinBy s xs}"

covering
printExpr : Expr Print -> State Nat String

covering
printAlternative : (n : Nat ** (String, Vect n (Ty Print), Vect n (varRep Print) -> Expr Print)) -> State Nat String
printAlternative ((fst ** (x, y, z))) = do
  names <- traverse (const fresh) y
  bindings <- traverse (\(name, ty) => pure "(\{name} \{!(printType ty)})") (zip names y)
  pure "(\{x} \{joinBy " " bindings})\n\{!(printExpr (z names))}"

covering
printHandler : Handler Print -> State Nat String
printHandler (MkHandler op arg argType resumeArgType body) = do
  resumeName <- fresh
  pure "(\{op} (\{arg} \{!(printType argType)}) \{!(printType resumeArgType)} \{!(printExpr (body (MkArgAndResume arg resumeName)))})"

covering
printClause : Clause Print -> State Nat String
printClause (Return x f) = do
  argName <- fresh
  pure "(return (\{argName} \{!(printType x)}) \{!(printExpr (f argName))})"
printClause (OpHandler x y) = pure "\{!(printHandler x)}\n\{!(printClause y)}"

printExpr (x :$ y) = do
  x <- printExpr x
  y <- printExpr y
  pure "(\{x} \{y})"
printExpr (Val x t f) = do
  t <- printType t
  x <- printExpr x
  name <- fresh
  f <- printExpr (f name)
  pure "(def \{name} \{t} \{x})\n\{f}"
printExpr (Handle x y) = do
  -- TODO: Effect name
  pure "(handle\n[\{!(printClause x)}]\n\{!(printExpr y)})"
printExpr (LocalVar x) = pure x
printExpr (FreeVar str) = pure str
printExpr (Extern str x) = pure "(extern \{str} \{!(printCType x)})"
printExpr (Export x y) = ?pe_6
printExpr (Op str x) = ?pe_7
printExpr (x :\ f) = ?pe_8
printExpr (Fix x y f) = ?pe_9
printExpr (TyDecl x f) = do
  name <- fresh
  -- TODO: Type name in declaration
  pure "\{!(printType x)}\n\{!(printExpr (f name))}"
printExpr (Constructor str) = pure str
printExpr (Case x xs) =
  pure "(case \{!(printExpr x)}\n[\{joinBy "\n" !(traverse printAlternative xs)}])"

covering
main : IO ()
main = do
  input <- readAllInput
  tokens <- case getTokens input of
    Left err => die err
    Right tokens => pure tokens
  preSyntax <- case parse tokens of
    Left errs => die (show errs)
    Right preSyntax => pure preSyntax
  case resolve {stage = Print} preSyntax [] of
    Left err => die err
    Right expr => putStrLn (evalState 0 $ printExpr (expr emptyEnv))
