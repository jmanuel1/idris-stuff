module MicroKanren.Internal.Reify

import Data.Colist
import Data.Fuel
import Data.List.Lazy
import Data.SortedMap
import Data.Vect
import MicroKanren.Internal
import MicroKanren.Internal.Control
import MicroKanren.Internal.Types

%hide Prelude.Stream.Stream

%default total

covering
walkRecursively : Term a -> Substitution a -> Term a
walkRecursively v s = let v = walk v s in
  case v of
    Var _ => v
    Pair carV cdrV => Pair (walkRecursively carV s) (walkRecursively cdrV s)
    _ => v

-- Note: Without reify-name, reify-s doesn't change the substitution

covering
reifyStateFirstVar : State a -> Term a
reifyStateFirstVar state = walkRecursively (Var 0) state.substitution

covering
mkReify : List (State a) -> List (Term a)
mkReify states = map reifyStateFirstVar states

covering
pull : Stream a -> Colist a
pull (Immature xs) = pull xs
pull [] = []
pull (x :: xs) = x :: pull xs

covering
take' : Fuel -> Colist a -> List a
take' Dry stream = []
take' (More n) stream = case stream of
  [] => []
  (x :: xs) => x :: take' n xs

export covering
take : Fuel -> Stream a -> List a
take n stream = take' n (pull stream)

export
callEmptyState : Goal a -> Stream (State a)
callEmptyState g = g emptyState

export covering
run : Fuel -> {m : Nat} -> (Vect m (Term a) -> LazyList (Goal a)) -> List (Term a)
run n gs = mkReify (take n (callEmptyState (fresh gs)))
