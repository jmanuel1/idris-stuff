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

data ListElement = End | El Integer

Eq ListElement where
  End == End = True
  El n == El m = n == m
  _ == _ = False

Nil : Term ListElement
Nil = Val End

(::) : Term ListElement -> Term ListElement -> Term ListElement
(::) = Pair

fromInteger : Integer -> Term ListElement
fromInteger = Val . El

covering
appendo : Term ListElement -> Term ListElement -> Term ListElement -> Goal ListElement
appendo xs ys zs = conde [
  [xs === [], zs === ys],
  [fresh {m = 3} $ \[x, xs', zs'] => [xs === (x :: xs'), zs === (x :: zs'), appendo xs' ys zs']]
]

covering
appendBackwards : List (Term ListElement)
appendBackwards = run (limit 10) $ \[q, p, r] => [appendo p r [4, 5, 6], q === (Pair p r)]

covering
circular : Eq a => List (Term a)
circular = run (limit 1) {m = 1} $ \[q] => [q === Pair q q]
