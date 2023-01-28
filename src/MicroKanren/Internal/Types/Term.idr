module MicroKanren.Internal.Types.Term

import MicroKanren.Internal.Types.Variable

%default total

public export
data Term : Type -> Type where
  Var : Variable -> Term a
  Val : a -> Term a
  Pair : Term a -> Term a -> Term a

export
fromInteger : Num a => Integer -> Term a
fromInteger a = Val (fromInteger a)
