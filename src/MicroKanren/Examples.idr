import Data.SortedMap

%hide Prelude.Stream.Stream

%default total

Variable : Type
Variable = Integer

data Term : Type -> Type where
  Val : a -> Term a

fromInteger : Num a => Integer -> Term a
fromInteger a = Val (fromInteger a)

Substitution : Type -> Type
Substitution a = SortedMap Variable (Term a)

record State a where
  constructor MkState
  substitution : Substitution a
  nextVar : Variable

data Stream a = (::) a (Stream a) | Nil | Immature (Inf (Stream a))

Goal : Type -> Type
Goal a = State a -> Stream (State a)

emptyState : State a
emptyState = MkState empty 0

callFresh : (Term a -> Goal a) -> Goal a

(===) : Term a -> Term a -> Goal a

disj : Goal a -> Goal a -> Goal a

conj : Goal a -> Goal a -> Goal a

zzz : Lazy (Goal a) -> Goal a

qEquals5 : Stream (State Integer)
qEquals5 = callFresh (\q => q === 5) emptyState

covering
infiniteStream : Stream (State Integer)
infiniteStream = callFresh fives emptyState where
  fives : Term Integer -> Goal Integer
  fives x = disj (x === 5) (zzz (fives x))

disjExample : Stream (State Integer)
disjExample = aAndB emptyState where
  aAndB : Goal Integer
  aAndB = conj (callFresh (\a => a === 7)) (callFresh (\b => disj (b === 5) (b === 6)))
