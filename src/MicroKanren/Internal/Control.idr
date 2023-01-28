module MicroKanren.Internal.Control

import Data.List.Lazy
import Data.Vect
import MicroKanren.Internal
import MicroKanren.Internal.Types

%default total

export
zzz : Lazy (Goal a) -> Goal a
zzz g = \state => Immature (g state)

export
conjMany : LazyList (Goal a) -> Goal a
conjMany [] = pure
conjMany (g :: gs) = conj (zzz g) (conjMany gs)

export
disjMany : LazyList (Goal a) -> Goal a
disjMany [] = const []
disjMany (g :: gs) = disj (zzz g) (disjMany gs)

export
conde : LazyList (LazyList (Goal a)) -> Goal a
conde gs = disjMany (map conjMany gs)

export
fresh : {m : Nat} -> (Vect m (Term a) -> LazyList (Goal a)) -> Goal a
fresh {m = Z} gs = conjMany (gs [])
fresh {m = S m} gs = callFresh $ \x => fresh {m} $ \xs => gs (x :: xs)
