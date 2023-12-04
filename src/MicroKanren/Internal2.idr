module MicroKanren.Internal

import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import Deriving.Functor
import MicroKanren.Internal.Types

%language ElabReflection

%hide Prelude.Stream.Stream

%default total

data Stream a = (::) a (Stream a) | Nil | Immature (Inf (Stream a))

Semigroup (Stream a) where
  [] <+> b = b
  -- This might not be lawful
  (Immature as) <+> b = Immature (b <+> as)
  (a :: as) <+> b = a :: (b <+> as)

Monoid (Stream a) where
  neutral = []

%hint
streamFunctor : Functor Stream
streamFunctor = %runElab derive

Applicative Stream where
  pure a = [a]
  (<*>) (f :: fs) a = map f a <+> (fs <*> a)
  (<*>) [] a = []
  (<*>) (Immature fs) a = Immature (fs <*> a)

Monad Stream where
  [] >>= f = neutral
  (Immature fas) >>= f = Immature (fas >>= f)
  (fa :: fas) >>= f = f fa <+> (fas >>= f)

export
Goal : Type -> Type
Goal a = State a -> Stream (State a)

emptyState : State a
emptyState = MkState {subMap = the (Substitution' a) empty, substitution = Empty, nextVar = 0}

-- QUESTION: Is Idris so smart that it can determine totality?
extendSubstitution : Variable -> Term a -> (s : Substitution' a ** Substitution s) -> Maybe (s : Substitution' a ** Substitution s)
extendSubstitution x v (s ** prf) = case choose (occurs x v s) of
  Left doesOccur => Nothing
  Right doesNotOccur => Just (insert x v s ** Extend x v prf doesNotOccur)

totalWalk : Term a -> (s : Substitution' a ** Substitution s) -> Term a
totalWalk u (s ** prf) = walk u s

covering
unify : Eq a => Term a -> Term a -> (s : Substitution' a ** Substitution s) -> Maybe (s : Substitution' a ** Substitution s)
unify u v sub@(s ** prf) = --?holeunify
  let
    u = totalWalk u sub
    v = totalWalk v sub
  in case (u, v) of
    (Var u, Var v) => if u == v then Just sub else extendSubstitution u (Var v) sub
    (Var u, v) => extendSubstitution u v sub
    (u, Var v) => extendSubstitution v u sub
    (Pair carU cdrU, Pair carV cdrV) => do
      sub <- unify carU carV sub
      unify cdrU cdrV sub
    (Val u, Val v) => if u == v then Just sub else Nothing
    _ => Nothing

export
callFresh : (Term a -> Goal a) -> Goal a
callFresh f = \state => let c = state.nextVar in f (Var c) ({ nextVar $= (+ 1) } state)

export covering
(===) : Eq a => Term a -> Term a -> Goal a
u === v = \state => let s = unify u v (state.subMap ** state.substitution) in
  case s of
    Just (s ** prf) => pure ({ subMap := s, substitution := prf } state)
    Nothing => neutral

export
disj : Goal a -> Goal a -> Goal a
disj g1 g2 = \state => g1 state <+> g2 state

export
conj : Goal a -> Goal a -> Goal a
conj g1 g2 = \state => g1 state >>= g2
