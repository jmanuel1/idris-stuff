module MicroKanren.Internal.Constraint

import Control.WellFounded
import Data.List
import Data.Nat
import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat
import Frexlet.Monoid.Commutative.Notation.Core
import MicroKanren.Internal.Types

%default total

%language ElabReflection

public export
fv : Term a -> List Variable
fv (Var i) = [i]
fv (Val x) = []
fv (Pair x y) = fv x `union` fv y

public export
Sized (Term a) where
  size (Var i) = 1
  size (Val x) = 1
  size (Pair x y) = 1 + size x + size y

public export
EqualityConstraint : Type -> Type
EqualityConstraint a = (Term a, Term a)

public export
eqCon : Term a -> Term a -> EqualityConstraint a
eqCon t s = (t, s)

public export
fvCon : EqualityConstraint a -> List Variable
fvCon (t, s) = fv t `union` fv s

public export
data ConstraintList : Type -> Type where
  Nil : ConstraintList a
  (::) : EqualityConstraint a -> ConstraintList a -> ConstraintList a

export
makeConstraintList : List (EqualityConstraint a) -> ConstraintList a
makeConstraintList = foldr (::) []

public export
fvConList : ConstraintList a -> List Variable
fvConList [] = []
fvConList (con :: c) = fvConList c `union` fvCon con

-- Sized impls for EqualityConstraint a is just the impl in Control.WellFounded

||| Sized impl for List (EqualityConstraint a) in Control.WellFounded is the
||| length of the list. We want the sum of the sizes of the constraints.
public export
Sized (ConstraintList a) where
  size [] = 0
  size (con :: c) = size c + size con

||| Lemma 1
public export
splitPairConstraintDecreasesSize : {t1, t1', t2, t2' : Term a} -> (c : ConstraintList a) -> Smaller ((t1 `eqCon` t1') :: (t2 `eqCon` t2') :: c) ((Pair t1 t2 `eqCon` Pair t1' t2') :: c)
splitPairConstraintDecreasesSize [] =
  let rewriteRight : (size t1 + size t2) + S (size t1' + size t2') === S (size t2 + size t2') + (size t1 + size t1')
      rewriteRight = Frex.solve 4 (Monoid.Commutative.Frex Nat.Additive)
        $ (Dyn 0 .+. Dyn 2) .+. (Sta 1 .+. (Dyn 1 .+. Dyn 3)) =-= Sta 1 .+. ((Dyn 2 .+. Dyn 3) .+. (Dyn 0 .+. Dyn 1)) in
  LTESucc $
  rewrite rewriteRight in
  lteSuccRight reflexive
splitPairConstraintDecreasesSize (x :: xs) =
  let xsDecreasesSize = splitPairConstraintDecreasesSize xs
      plusSizeX = plusLteMonotoneRight (size x) _ _ xsDecreasesSize
      -- Order of Dyns: x, xs, t1, t1', t2, t2'
      rewriteLeft : S (((size xs + size x) + (size t2 + size t2')) + (size t1 + size t1')) === S (((size xs + (size t2 + size t2')) + (size t1 + size t1')) + size x)
      rewriteLeft = Frex.solve 6 (Monoid.Commutative.Frex Nat.Additive)
        $ Sta 1 .+. (((Dyn 1 .+. Dyn 0) .+. (Dyn 4 .+. Dyn 5)) .+. (Dyn 2 .+. Dyn 3)) =-= Sta 1 .+. (((Dyn 1 .+. (Dyn 4 .+. Dyn 5)) .+. (Dyn 2 .+. Dyn 3)) .+. Dyn 0)
      rewriteRight : (size xs + size x) + S ((size t1 + size t2) + S (size t1' + size t2')) === (size xs + S ((size t1 + size t2) + S (size t1' + size t2'))) + size x
      rewriteRight = Frex.solve 6 (Monoid.Commutative.Frex Nat.Additive)
        $ (Dyn 1 .+. Dyn 0) .+. (Sta 1 .+. ((Dyn 2 .+. Dyn 4) .+. (Sta 1 .+. (Dyn 3 .+. Dyn 5)))) =-= (Dyn 1 .+. (Sta 1 .+. ((Dyn 2 .+. Dyn 4) .+. (Sta 1 .+. (Dyn 3 .+. Dyn 5))))) .+. Dyn 0 in
  rewrite rewriteLeft in rewrite rewriteRight in plusSizeX

||| Lemma 2
public export
removeConstraintDecreasesSize : (t, t' : Term a) -> {c : ConstraintList a} -> Smaller (size c) (size ((t `eqCon` t') :: c))
removeConstraintDecreasesSize (Var v) t' =
  rewrite sym $ plusSuccRightSucc (size c) (size t') in
  LTESucc $
  lteAddRight (size c)
removeConstraintDecreasesSize (Val v) t' =
  rewrite sym $ plusSuccRightSucc (size c) (size t') in
  LTESucc $
  lteAddRight (size c)
removeConstraintDecreasesSize (Pair t s) t' =
  rewrite sym $ plusSuccRightSucc (size c) ((size t + size s) + size t') in
  LTESucc $
  lteAddRight (size c)
