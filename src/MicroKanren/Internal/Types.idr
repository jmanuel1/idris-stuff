module MicroKanren.Internal.Types

import Data.SortedMap

public export
Variable : Type
Variable = Integer

public export
data Term : Type -> Type where
  Var : Variable -> Term a
  Val : a -> Term a
  Pair : Term a -> Term a -> Term a

export
fromInteger : Num a => Integer -> Term a
fromInteger a = Val (fromInteger a)

public export
Substitution : Type -> Type
Substitution a = SortedMap Variable (Term a)

public export
record State a where
  constructor MkState
  substitution : Substitution a
  nextVar : Variable
