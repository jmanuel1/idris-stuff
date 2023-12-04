module MicroKanren.Internal.Types

import Data.Fin
import Data.SortedMap
import public MicroKanren.Internal.Types.Term
import public MicroKanren.Internal.Types.Variable

public export
Substitution : Nat -> Nat -> Type -> Type
Substitution m n a = SortedMap (Variable m) (Term n a)

public export
record State a where
  constructor MkState
  substitution : Substitution n m a
  nextVar : Variable theNextVar
