module MicroKanren.Internal

import Data.Fin
import Data.SortedMap
import Deriving.Functor
import MicroKanren.Internal.Types
import Syntax.WithProof

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

emptyState : State a
emptyState = MkState (the (IndSub 0 0 a) []) (the (Fin 1) FZ)

%hide MicroKanren.Internal.Types.State.m
%hide MicroKanren.Internal.Types.State.n

-- public export
-- applySub : Substitution m n a -> Term m a -> Term n a
-- applySub s (Var x) = fromMaybe (r (Var x)) ?ashole_0
-- applySub s (Val x) = ?ashole_1
-- applySub s (Pair x y) = ?ashole_2

weakenN : (0 n : Nat) -> Term m a -> Term (m + n) a
weakenN n (Var x) = Var (weakenN n x)
weakenN n (Val x) = Val x
weakenN n (Pair x y) = Pair (weakenN n x) (weakenN n y)

weaken : Term m a -> Term (S m) a
weaken (Var x) = Var (weaken x)
weaken (Val x) = Val x
weaken (Pair x y) = Pair (weaken x) (weaken y)

thick : {n : Nat} -> Fin (S n) -> Fin (S n) -> Maybe (Fin n)
thick FZ FZ = Nothing
thick FZ (FS x) = Just x
thick {n = S n} (FS x) FZ = Just FZ
thick {n = S n} (FS x) (FS y) = map FS (thick x y)

thickTerm : {n : Nat} -> Fin (S n) -> Term (S n) a -> Maybe (Term n a)
thickTerm u (Var x) = pure $ Var !(thick u x)
thickTerm u (Val x) = pure $ Val x
thickTerm u (Pair x y) = pure $ Pair !(thickTerm u x) !(thickTerm u y)

thickSub : {m : Nat} -> Fin (S (S m)) -> SortedMap (Fin (S (S m))) (Term (S m) a) -> SortedMap (Fin (S m)) (Term m a)
thickSub u s =
  let
    pairs = SortedMap.toList s
    -- Removing RHSs containing u is fine, because if we hit those during a
    -- walk, either we haven't seen u yet, or we have and we are in a cycle.
    thickPairs = mapMaybe {b = (Fin (S m), Term m a)} (\(k, v) => do
      u <- thick u k
      pure (u, !(thickTerm u v))) pairs
  in fromList thickPairs

thin : {n : Nat} -> Fin (S n) -> Fin n -> Fin (S n)
thin FZ y = FS y
thin {n = S n} (FS x) FZ = FZ
thin {n = S n} (FS x) (FS y) = FS (thin x y)

thinTerm : {n : Nat} -> Fin (S n) -> Term n a -> Term (S n) a
thinTerm u (Var x) = Var (thin u x)
thinTerm u (Val x) = Val x
thinTerm u (Pair x y) = Pair (thinTerm u x) (thinTerm u y)

walk : {n : Nat} -> (s : Substitution m n a) -> (u : Term m a) -> Term n a
walk s (Var x) = s x
walk s (Val x) = Val x
walk s (Pair x y) = Pair (walk s x) (walk s y)

occurs : {n : Nat} -> Variable (S n) -> Term (S n) a -> Bool
occurs x v = isNothing (thickTerm x v)

weakenSubKey : Substitution m n a -> Substitution (S m) n a
-- weakenSubKey s =
--   let
--     pairs = SortedMap.toList s
--     weakenedPairs = map (\(k, v) => (weaken k, v)) pairs
--   in fromList weakenedPairs

-- SubWithInd : (m, n : Nat) -> Type -> Type
-- SubWithInd m n a = (s : Substitution m n a ** IndSub m n s)

-- extendSubstitution : Variable (S n) -> Term m a -> SubWithInd n m a -> SubWithInd (S n) m a
-- extendSubstitution x v (s ** i) = (insert x v (weakenSubKey s) ** SubCons x v i)
-- subUnCons : (s : SubstitutNaion (S m) m a) -> Maybe (Variable (S m), Term m a, Substitution (S m) (pred m) a)
-- subUnCons s = do
--   (x, t) <- rightMost s
--   ?h4

-- sub : Fin (S n) -> Term n a -> Term (S n) a -> Term n a
-- sub x t y = case thickTerm x t of
--   Just y =>

for : {n : Nat} -> Term n a -> Variable (S n) -> Substitution (S n) n a
for t x y = case thick x y of
  Just y => Var y
  Nothing => t

(<=<) : {n : Nat} -> Substitution m n a -> Substitution l m a -> Substitution l n a
(<=<) f g = walk f . g

sub : {m, n : Nat} -> IndSub m n a -> Substitution m n a
sub [] = Var
sub ((x, t) :: s) = sub s <=< (t `for` x)

||| The RHS of the substitutions thickens away variables from the LHS.
unify : Eq a => {n : Nat} -> Term n a -> Term n a -> {m : Nat} -> (s : IndSub n m a) -> Maybe (m' : Nat ** IndSub n m' a)
unify {n} (Val u) (Val v) s = if u == v then Just (_ ** s) else Nothing
unify {n} (Val _) (Pair _ _) s = Nothing
unify {n} (Pair _ _) (Val _) s = Nothing
unify {n} (Pair carU cdrU) (Pair carV cdrV) s = do
  (_ ** s) <- unify carU carV s
  unify cdrU cdrV s
unify {n = S m} (Var u) (Var v) [] = case thick u v of
  Just v => Just $ (m ** [(u, (Var v))])
  Nothing => Just (S m ** [])
unify {n = S m} (Var u) v [] = case thickTerm u v of
  Just v => Just $ (m ** [(u, v)])
  Nothing => Nothing
unify {n = S m} u (Var v) [] = case thickTerm v u of
  Just u => Just $ (m ** [(v, u)])
  Nothing => Nothing
unify {n = S n} u v ((x, t) :: s) = do
  (_ ** s') <- unify {a} (walk (t `for` x) u) (walk (t `for` x) v) s
  Just (_ ** ((x, t) :: s'))

export
callFresh : ({n : Nat} -> Term n a -> Goal a) -> Goal a
callFresh f = \state => let c = state.nextVar in f (Var c) ({ nextVar $= FS } state)

export
(===) : Eq a => {n : Nat} -> Term n a -> Term n a -> (state : State a) -> {auto 0 prf : state.n === n} -> Stream (State a)
(===) @{_} u v state @{prf} =
  let
    sub = state.substitution
    s = unify u v {m = state.m} (rewrite sym prf in sub)
  in case s of
    Just (_ ** s) => pure ({substitution := s} state)
    Nothing => neutral

export
disj : Goal a -> Goal a -> Goal a
disj g1 g2 = \state => g1 state <+> g2 state

export
conj : Goal a -> Goal a -> Goal a
conj g1 g2 = \state => g1 state >>= g2
