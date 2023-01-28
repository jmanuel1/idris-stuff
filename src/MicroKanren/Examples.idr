module MicroKanren.Examples

import Data.Fuel
import Data.List.Lazy
import Data.Vect
import MicroKanren

%hide Builtin.(===)
%hide Prelude.Stream.Stream

%default total

covering
qEquals5 : List (Term Integer)
qEquals5 = run forever (\[q] => [q === 5])

covering
fives : Vect 1 (Term Integer) -> Goal Integer
fives [x] = disj (x === 5) (zzz (fives [x]))

covering
infiniteStream : List (Term Integer)
infiniteStream = run forever ((\g => [g]) . fives)

covering
finiteStream : List (Term Integer)
finiteStream = run (limit 5) ((\g => [g]) . fives)

covering
disjExample : List (Term Integer)
disjExample = run forever aAndB where
  aAndB : Vect ? (Term Integer) -> LazyList (Goal Integer)
  aAndB [q, a, b] = [conj (a === 7) (disj (b === 5) (b === 6)), q === Pair a b]
