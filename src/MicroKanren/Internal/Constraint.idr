module MicroKanren.Internal.Constraint

import Control.WellFounded
import Data.List
import Data.Nat
import MicroKanren.Internal.Types

%default total

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

public export
fvConList : ConstraintList a -> List Variable
fvConList [] = []
fvConList (con :: c) = fvConList c `union` fvCon con

-- Sized impls for EqualityConstraint a is just the impl in Control.WellFounded

||| Sized impl for List (EqualityConstraint a) in Control.WellFounded is the
||| length of the list. We want the sume of the sizes of the constraints.
public export
Sized (ConstraintList a) where
  size [] = 0
  size (con :: c) = size c + size con

||| Lemma 1
public export
splitPairConstraintDecreasesSize : {t1, t1', t2, t2' : Term a} -> (c : ConstraintList a) -> Smaller ((t1 `eqCon` t1') :: (t2 `eqCon` t2') :: c) ((Pair t1 t2 `eqCon` Pair t1' t2') :: c)
splitPairConstraintDecreasesSize [] =
  -- LTE
  --  (S (plus (plus (size t1) (size t1')) (plus (size t2) (size t2'))))
  --  (S (plus (plus (size t1) (size t2)) (S (plus (size t1') (size t2')))))
  LTESucc $
  -- LTE
  --  (plus (plus (size t2) (size t2')) (plus (size t1) (size t1')))
  --  (plus (plus (size t1) (size t2)) (S (plus (size t1') (size t2'))))
  rewrite sym $ plusSuccRightSucc (size t1 + size t2) (size t1' + size t2') in
  -- LTE
  --  (plus (plus (size t2) (size t2')) (plus (size t1) (size t1')))
  --  (S (plus (plus (size t1) (size t2)) (plus (size t1') (size t2'))))
  rewrite plusCommutative (size t2 + size t2') (size t1 + size t1') in
  rewrite plusAssociative (size t1 + size t2) (size t1') (size t2') in
  -- LTE
  --  (plus (plus (size t1) (size t1')) (plus (size t2) (size t2')))
  --  (S (plus (plus (plus (size t1) (size t2)) (size t1')) (size t2')))
  rewrite sym $ plusAssociative (size t1) (size t2) (size t1') in
  -- LTE
  --  (plus (plus (size t1) (size t1')) (plus (size t2) (size t2')))
  --  (S (plus (plus (size t1) (plus (size t2) (size t1'))) (size t2')))
  rewrite plusCommutative (size t2) (size t1') in
  -- LTE
  --  (plus (plus (size t1) (size t1')) (plus (size t2) (size t2')))
  --  (S (plus (plus (size t1) (plus (size t1') (size t2))) (size t2')))
  rewrite plusAssociative (size t1) (size t1') (size t2) in
  rewrite plusAssociative (size t1 + size t1') (size t2) (size t2') in
  lteSuccRight reflexive
splitPairConstraintDecreasesSize (x :: xs) =
  let xsDecreasesSize = splitPairConstraintDecreasesSize xs in
  -- LTE
  --  (S (plus (plus (plus (cListSize xs) (plus (size ?t2) (size ?t2'))) (plus (size ?t1) (size ?t1'))) (size x)))
  --  (plus (plus (cListSize xs) (S (plus (plus (size ?t1) (size ?t2)) (S (plus (size ?t1') (size ?t2')))))) (size x))
  let plusSizeX = plusLteMonotoneRight (size x) _ _ xsDecreasesSize in
  -- LTE
  --  (S (plus (plus (plus (cListSize xs) (size x)) (plus (size t2) (size t2'))) (plus (size t1) (size t1'))))
  --  (plus (plus (cListSize xs) (size x)) (S (plus (plus (size t1) (size t2)) (S (plus (size t1') (size t2'))))))
  rewrite sym $ plusAssociative (size xs) (size x) (size t2 + size t2') in
  rewrite plusCommutative (size x) (size t2 + size t2') in
  rewrite plusAssociative (size xs) (size t2 + size t2') (size x) in
  -- LTE
  --  (S (plus (plus (plus (cListSize xs) (plus (size t2) (size t2'))) (size x)) (plus (size t1) (size t1'))))
  --  (plus (plus (cListSize xs) (size x)) (S (plus (plus (size t1) (size t2)) (S (plus (size t1') (size t2'))))))
  rewrite sym $ plusAssociative (size xs + (size t2 + size t2')) (size x) (size t1 + size t1') in
  rewrite plusCommutative (size x) (size t1 + size t1') in
  -- LTE
  --  (S (plus (plus (cListSize xs) (plus (size t2) (size t2'))) (plus (plus (size t1) (size t1')) (size x))))
  --  (plus (plus (cListSize xs) (size x)) (S (plus (plus (size t1) (size t2)) (S (plus (size t1') (size t2'))))))
  rewrite plusAssociative (size xs + (size t2 + size t2')) (size t1 + size t1') (size x) in
  -- NOTE: Idris 0.6.0-87ebe7d93 doesn't terminate when you remove sym below.
  rewrite sym $ plusAssociative (size xs) (size x) (S ((size t1 + size t2) + S (size t1' + size t2'))) in
  rewrite plusCommutative (size x) (S ((size t1 + size t2) + S (size t1' + size t2'))) in
  rewrite plusAssociative (size xs) (S ((size t1 + size t2) + S (size t1' + size t2'))) (size x) in
  plusSizeX

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
