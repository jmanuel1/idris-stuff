module Typecase

import System
import System.File
import Data.String
import Format

readTy : String -> IO Type
readTy "String" = pure String
readTy "Int" = pure Int
readTy "Char" = pure Char
readTy "DepPat" = pure DepPat
readTy "fun" = pure ((x : Bool) -> ifThenElse x DepPat String)
readTy _ = die "unsupported"

enumTy : Type -> IO Nat
enumTy String = pure 0
enumTy Int = pure 1
enumTy Char = pure 2
enumTy DepPat = pure 3
enumTy (Bool -> _) = pure 4
enumTy _ = die "unsupported"

main : IO ()
main = do
  Right input <- fGetLine stdin
  | Left err => die $ show err
  ty <- readTy $ trim input
  i <- enumTy ty
  printLn i
