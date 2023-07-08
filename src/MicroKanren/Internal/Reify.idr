module MicroKanren.Internal.Reify

import Data.Colist
import Data.Fuel
import Data.List.Lazy
import Data.SortedMap
import Data.Vect
import MicroKanren.Internal
import MicroKanren.Internal.Control
import MicroKanren.Internal.Types
import Syntax.WithProof

%hide Prelude.Stream.Stream

%default total

-- XXX: walkRecursively: walk is already recursive

-- Note: Without reify-name, reify-s doesn't change the substitution

reifyStateFirstVar : (state : State a) -> {auto 0 prf : state.n = S _} -> Term (state.m) a
reifyStateFirstVar state = walk (sub state.substitution) (Var (rewrite prf in FZ))

mkReify : List (State a) -> List (n : Nat ** Term n a)
mkReify states = map (\state => case @@(state.n) of
  (Z ** _) => (1 ** Var 0)
  (S _ ** _) => (_ ** reifyStateFirstVar state)) states

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
run : Fuel -> {m : Nat} -> ({o : Nat} -> Vect m (Term o a) -> LazyList (Goal a)) -> List (n : Nat ** Term n a)
run n gs = mkReify (take n (callEmptyState (fresh gs)))
