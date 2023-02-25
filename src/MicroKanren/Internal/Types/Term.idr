module MicroKanren.Internal.Types.Term

import Data.Fin
import MicroKanren.Internal.Types.Variable

%default total

public export
data Term : Nat -> Type -> Type where
  Var : Variable n -> Term n a
  Val : a -> Term n a
  Pair : Term n a -> Term n a -> Term n a

export
fromInteger : Num a => Integer -> Term n a
fromInteger a = Val (fromInteger a)
