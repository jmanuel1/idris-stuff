module LambdaC.Test

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State
import Data.SortedMap
import LambdaC
import System
import System.File.Handle
import System.File.ReadWrite


data EvalError = TypeError

Show EvalError where
  show _ = "TypeError"

eval : MonadError EvalError m => LC -> m LC
eval v@(Var _) = pure v
eval (App f y) = do
  f' <- eval f
  case f' of
    (Abs var _ body) => do
      y' <- eval y
      eval (sub var y' body)
    -- how 2 if????
    -- | (Extern "prim_if" _) => do
    -- | (Extern "prim_to_bool" _) => do
    --   (Extern n _) <- eval y
    --   if cast n == 0 then
    (Extern "prim_succ" _) => do
      (Extern n _) <- eval y
      | _ => throwError TypeError
      pure (Extern (cast (cast n + 1)) "int")
    (Extern "prim_pred" _) => do
      (Extern n _) <- eval y
      | _ => throwError TypeError
      pure (Extern (cast (cast n - 1)) "int")
    _ => throwError TypeError
eval abs@(Abs _ _ _) = pure abs
eval fix@(Fix fVar body fArgType fRetType) =
  pure (Abs "x" fArgType (((Abs fVar (FunType fArgType fRetType "") body) `App` fix) `App` Var "x"))
-- eval e@(Extern prim (FunType "int" "int" "empty_closure")) = e
eval e@(Extern _ _) = pure e -- throwError NoExternAllowedError

-- metafunctions

namespace Meta
  export
  true : LC
  true = Extern "true" "bool"

  export
  false : LC
  false = Extern "false" "bool"

  export
  iter : Nat -> LC -> LC -> LC
  iter Z f a = a
  iter (S n) f a = f `App` iter n f a

  export
  int : Int -> LC
  int n = Extern (cast n) "int"

  export
  toInt : LC -> Maybe Int
  toInt (Extern n _) = Just (cast n)
  toInt _ = Nothing

-- test cases

main : IO ()
main = do
  let zero = iter 3 (Extern "prim_succ" (FunType "int" "int" "struct prim_fun_closure")) (iter 3 (Extern "prim_pred" (FunType "int" "int" "struct prim_fun_closure")) (int 0))
  let prims = [
    Struct [] "empty_closure_env",
    Fun "int" "prim_succ_fun" [MkCArg "int" "n", MkCArg "struct empty_closure_env" "unused"] [RawStmt "return n + 1"],
    Fun "int" "prim_pred_fun" [MkCArg "int" "n", MkCArg "struct empty_closure_env" "unused"] [RawStmt "return n - 1"],
    Struct [FunPtr "int" "function" ["int", "struct empty_closure_env"], Var "struct empty_closure_env" "env" Nothing] "prim_fun_closure",
    Var "struct prim_fun_closure" "prim_succ" (Just "{prim_succ_fun, {}}"),
    Var "struct prim_fun_closure" "prim_pred" (Just "{prim_pred_fun, {}}")
  ]
  interpResult <- eitherT (die . show) pure $ the (EitherT EvalError IO LC) (eval zero)
  interpResult' <- case toInt interpResult of
    Just n => pure n
    Nothing => die "zero didn't evaluate to an int"
  when (interpResult' /= 0)
    (die "zero should evaluate to 0")
  compiledZero <- eitherT die pure (evalStateT (Z, the (SortedMap String CType) empty) $ lcToCProgram zero)
  let zeroWithPrims = prims ++ compiledZero
  ignore $ withFile "test.c" WriteTruncate
    (die . show)
    (\file => the (IO (Either () ())) $ map Right $ writeC file zeroWithPrims)
  ccExitCode <- System.system "cc ./test.c -o test"
  when (ccExitCode /= 0)
    (die "C compilation failed")
  testExitCode <- System.system "./test"
  when (testExitCode /= 0)
    (die "compiled program did not return 0")

-- true : CType -> LC
-- true t = Abs "t" t (Abs "f" t (Var "t"))
--
-- false : CType -> LC
-- false t = Abs "t" t (Abs "f" t (Var "f"))
--

--
-- nat : CType -> Nat -> LC
-- nat t n = Abs "s" (FunType t t "") (Abs "z" t (iter n (Var "s") (Var "z")))
--
-- natCType : CType -> CType
-- natCType t = FunType (FunType t t "") (FunType t t "") ""
--
-- mult : CType -> LC
-- mult t = Abs "m" (natCType t) (Abs "n" (natCType t) (Abs "f" (FunType t t "") (Var "m" `App` (Var "n" `App` Var "f"))))
--
-- pred : CType -> LC
-- pred t = Abs "n" (natCType t) (Abs "f" (FunType t t "") (Abs "x" t
--   (((Var "n" `App` (Abs "g" (FunType (FunType t t "") ?h0 "") (Abs "h" (FunType ?h0 (FunType t t "") "") (Var "h" `App` (Var "g" `App` Var "f")))))
--     `App` (Abs "u" ?h2 (Var "x"))) `App` (Abs "u" ?h3 (Var "u")))
--   ))
