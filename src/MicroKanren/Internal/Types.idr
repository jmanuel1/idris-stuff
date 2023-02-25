module MicroKanren.Internal.Types

import Data.Fin
import Data.Nat
import Data.SortedMap
import public MicroKanren.Internal.Types.Term
import public MicroKanren.Internal.Types.Variable

%default total

public export
Substitution : Nat -> Nat -> Type -> Type
Substitution m n a = Variable m -> Term n a

public export
data IndSub : (0 m, n : Nat) -> Type -> Type where
  Nil : IndSub n n a
  (::) : (xt : (Variable (S m), Term m a)) -> IndSub m n a -> IndSub (S m) n a
  -- Done : IndSub m n a -> LTE m o =

public export
record State a where
  constructor MkState
  {n, m : Nat}
  substitution : IndSub n m a
  -- {auto 0 nextVarBounded : LTE n nextVarBound}
  {nextVarBound : Nat}
  nextVar : Variable nextVarBound
