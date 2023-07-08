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
emptyState = MkState (empty {k = Variable 0, v = Term 0 a}) (FZ {k = 1})

%hide MicroKanren.Internal.Types.State.n
%hide MicroKanren.Internal.Types.State.m

data VarAbsentInSub : Term n a -> Substitution n _ a -> Type where
  Absence : lookup u s === Nothing -> VarAbsentInSub (Var u) s

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

walk : {n : Nat} -> (u : Term (S n) a) -> (s : Substitution (S n) n a) -> Maybe (Term (S n) a)
walk {n = Z} u s = pure $ case u of
  Var u => case lookup u s of
    Just term => weaken term
    Nothing => Var u
  Val u => Val u
  Pair u v => Pair u v
walk {n = S m} u s = case u of
  Var u => case lookup u s of
    Just term => do
      term' <- thickTerm u (weaken term)
      pure $ thinTerm u !(walk {n = m} term' (thickSub u s))
    Nothing => pure $ Var u
  _ => pure u

occurs : {n : Nat} -> Variable (S n) -> Term (S n) a -> Bool
occurs x v = isNothing (thickTerm x v)

weakenSub : Substitution m n a -> Substitution (S m) (S n) a
weakenSub s =
  let
    pairs = SortedMap.toList s
    weakenedPairs = map (\(k, v) => (weaken k, weaken v)) pairs
  in fromList weakenedPairs

weakenSubKey : Substitution m n a -> Substitution (S m) n a
weakenSubKey s =
  let
    pairs = SortedMap.toList s
    weakenedPairs = map (\(k, v) => (weaken k, v)) pairs
  in fromList weakenedPairs

data IndSub : (0 m, n : Nat) -> Substitution m n a -> Type where
  SubNil : IndSub n n SortedMap.empty
  SubCons : (x : Variable (S m)) -> (t : Term n a) -> IndSub m n s -> IndSub (S m) n (insert x t (weakenSubKey s))

SubWithInd : (m, n : Nat) -> Type -> Type
SubWithInd m n a = (s : Substitution m n a ** IndSub m n s)

extendSubstitution : Variable (S n) -> Term m a -> SubWithInd n m a -> SubWithInd (S n) m a
extendSubstitution x v (s ** i) = (insert x v (weakenSubKey s) ** SubCons x v i)
-- subUnCons : (s : SubstitutNaion (S m) m a) -> Maybe (Variable (S m), Term m a, Substitution (S m) (pred m) a)
-- subUnCons s = do
--   (x, t) <- rightMost s
--   ?h4

||| The RHS of the substitutions thickens away variables from the LHS.
partial
unify : Eq a => {n : Nat} -> Term n a -> Term n a -> {m : Nat} -> (s : Substitution n m a) -> IndSub n m s -> Maybe (m' : Nat ** s' : Substitution n m' a ** IndSub n m' s')
-- u' <- walk u s
-- v' <- walk v s
unify {n} (Val u) (Val v) s i = if u == v then Just (_ ** s ** i) else Nothing
unify {n} (Val _) (Pair _ _) s _ = Nothing
unify {n} (Pair _ _) (Val _) s _ = Nothing
unify {n} (Pair carU cdrU) (Pair carV cdrV) s i = do
  (_ ** s ** i) <- unify carU carV s i
  unify cdrU cdrV s i
unify {n = S m} (Var u) (Var v) _ SubNil = case thick u v of
  Just v => Just $ (m ** extendSubstitution u (Var v) (empty ** SubNil))
  Nothing => Just (S m ** empty ** SubNil)
unify {n = S m} (Var u) v _ SubNil = case thickTerm u v of
  Just v => Just $ (m ** extendSubstitution u v (empty ** SubNil))
  Nothing => Nothing
unify {n = S m} u (Var v) _ SubNil = case thickTerm v u of
  Just u => Just $ (m ** extendSubstitution v u (empty ** SubNil))
  Nothing => Nothing
unify {n = S n} u v s@_ (SubCons x t i) = do
  -- (_ ** s' ** i') <- unify {a} {n} (?sub x t u) (?sub1 x t v) {m = n} ?shole ?ihole
  ?h3

{-
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
