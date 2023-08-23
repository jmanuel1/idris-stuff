module LambdaC.File

import System
import System.File

export
covering
readAllInput : IO String
readAllInput = do
  Right input <- fRead stdin
  | Left err => die (show err)
  pure input
