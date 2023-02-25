module MicroKanren.Examples

import Data.Fuel
import Data.List.Lazy
import Data.Vect
import MicroKanren

%hide Builtin.(===)
%hide Prelude.Stream.Stream

%default total

covering
qEquals5 : List (n : Nat ** Term n Integer)
qEquals5 = run forever (\[q] => [q === 5])

{-
covering
fives : {n : Nat} -> Vect 1 (Term n Integer) -> Goal Integer
fives [x] = disj (x === 5) (zzz (fives [x]))

covering
infiniteStream : List (n : Nat ** Term n Integer)
infiniteStream = run forever ((\g => [g]) . fives)

covering
finiteStream : List (n : Nat ** Term n Integer)
finiteStream = run (limit 5) ((\g => [g]) . fives)

covering
disjExample : List (n : Nat ** Term n Integer)
disjExample = run forever aAndB where
  aAndB : {m : Nat} -> Vect ? (Term m Integer) -> LazyList (Goal Integer)
  aAndB [q, a, b] = [conj (a === 7) (disj (b === 5) (b === 6)), q === Pair a b]

data ListElement = End | El Integer

Eq ListElement where
  End == End = True
  El n == El m = n == m
  _ == _ = False

Nil : Term n ListElement
Nil = Val End

(::) : Term n ListElement -> Term n ListElement -> Term n ListElement
(::) = Pair

fromInteger : Integer -> Term n ListElement
fromInteger = Val . El

covering
appendo : Term n ListElement -> Term n ListElement -> Term n ListElement -> Goal ListElement
appendo xs ys zs = conde [
  [xs === [], zs === ys],
  [fresh {m = 3} $ \[x, xs', zs'] => [xs === (x :: xs'), zs === (x :: zs'), appendo xs' ys zs']]
]

covering
appendBackwards : List (n : Nat ** Term n Integer)
appendBackwards = run (limit 10) $ \[q, p, r] => [appendo p r [4, 5, 6], q === (Pair p r)]

covering
circular : Eq a => List (n : Nat ** Term n a)
circular = run (limit 1) {m = 1} $ \[q] => [q === Pair q q]
