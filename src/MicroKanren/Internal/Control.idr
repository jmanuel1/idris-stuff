module MicroKanren.Internal.Control

import Data.Fin
import Data.List.Lazy
import Data.Vect
import MicroKanren.Internal
import MicroKanren.Internal.Types

%default total

%hide MicroKanren.Internal.Types.State.m
%hide MicroKanren.Internal.Types.State.n

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

weakenMax : (m : Nat) -> {n : Nat} -> Variable n -> Variable (maximum m n)
weakenMax m w =
  let r = maximumRightUpperBound m n in weakenLTE w r

weakenTermMax : (m : Nat) -> {n : Nat} -> Term n a -> Term (maximum m n) a
weakenTermMax m (Var x) = Var (weakenMax m x)
weakenTermMax m (Val x) = Val x
weakenTermMax m (Pair x y) = Pair (weakenTermMax m x) (weakenTermMax m y)

-- Use `corece`
varMaxBoundCommute : Variable (maximum m n) -> Variable (maximum n m)
varMaxBoundCommute v = rewrite maximumCommutative n m in v

termMaxBoundCommute : Term (maximum m n) a -> Term (maximum n m) a
termMaxBoundCommute (Var x) = Var (varMaxBoundCommute x)
termMaxBoundCommute (Val x) = Val x
termMaxBoundCommute (Pair x y) = Pair (termMaxBoundCommute x) (termMaxBoundCommute y)

export
fresh : {m : Nat} -> ({o : Nat} -> Vect m (Term o a) -> LazyList (Goal a)) -> Goal a
fresh {m = Z} gs = conjMany (gs {o = 0} [])
fresh {m = S m} gs = callFresh $ \x => fresh {m} $ \xs => gs (termMaxBoundCommute (weakenTermMax _ x) :: map (weakenTermMax _) xs)
