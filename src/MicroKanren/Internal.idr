module MicroKanren.Internal

import Data.SortedMap
import Deriving.Functor
import MicroKanren.Internal.Types

%language ElabReflection

%hide Prelude.Stream.Stream

%default total

-- export
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

-- export
emptyState : State a
emptyState = MkState empty 0

covering
walk : Term a -> Substitution a -> Term a
walk u s = case u of
  Var u => case lookup u s of
    Just term => walk term s
    Nothing => Var u
  _ => u

extendSubstitution : Variable -> Term a -> Substitution a -> Substitution a
extendSubstitution x v s = insert x v s

-- TODO: Disallow circular substitutions
covering
unify : Eq a => Term a -> Term a -> Substitution a -> Maybe (Substitution a)
unify u v s =
  let
    u = walk u s
    v = walk v s
  in case (u, v) of
    (Var u, Var v) => Just $ if u == v then s else extendSubstitution u (Var v) s
    (Var u, v) => Just $ extendSubstitution u v s
    (u, Var v) => Just $ extendSubstitution v u s
    (Pair carU cdrU, Pair carV cdrV) => do
      s <- unify carU carV s
      unify cdrU cdrV s
    (Val u, Val v) => if u == v then Just s else Nothing
    _ => Nothing

export
callFresh : (Term a -> Goal a) -> Goal a
callFresh f = \state => let c = state.nextVar in f (Var c) ({ nextVar $= (+ 1) } state)

export covering
(===) : Eq a => Term a -> Term a -> Goal a
u === v = \state => let s = unify u v state.substitution in
  case s of
    Just s => pure (MkState {substitution = s, nextVar = state.nextVar})
    Nothing => neutral

export
disj : Goal a -> Goal a -> Goal a
disj g1 g2 = \state => g1 state <+> g2 state

export
conj : Goal a -> Goal a -> Goal a
conj g1 g2 = \state => g1 state >>= g2
