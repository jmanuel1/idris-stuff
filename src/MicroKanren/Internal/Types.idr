module MicroKanren.Internal.Types

import Data.SortedMap
import public MicroKanren.Internal.Types.Term
import public MicroKanren.Internal.Types.Variable

public export
Substitution : Type -> Type
Substitution a = List (Variable, Term a)

public export
record State a where
  constructor MkState
  substitution : Substitution a
  nextVar : Variable
