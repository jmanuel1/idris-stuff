--- https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Data/SortedMap/Dependent.idr

||| An inductive view of `SortedMap`. Written for Idris 2 TODO: <<version>>.
||| This module pokes into the implementation of `SortedMap`, which is not
||| public export.
module Data.SortedMap.Dependent.Inductive

-- import Data.Fin
import Data.So
import Data.SortedMap.Dependent
import Decidable.Equality
import Syntax.WithProof

%default total

-- import MicroKanren.Internal.Types

-- %hide MicroKanren.Internal.Types.State.n
-- %hide MicroKanren.Internal.Types.State.m

interface EqCompat t (eq : Eq t) where
  toEq : (a, b : t) -> a === b -> So (a == b)
  -- toDecEq : (a, b : t) -> So (a == b) -> a === b

interface OrdCompat t (ord : Ord t) where
  toLeq : (a, b : t) -> a === b -> So (a <= b)
  toNotLeq : (a, b : t) -> compare a b === GT -> (a <= b) === False

getEq : SortedDMap k v -> Eq k
getEq Empty = %search
getEq (M _ _) = %search

getOrd : SortedDMap k v -> Ord k
getOrd Empty = %search
getOrd (M _ _) = %search

getEqFromOrd : Ord a -> Eq a
getEqFromOrd o = %search

treeLookup' : (key : k) -> {o : Ord k} -> Either (Tree n k v o) (Tree n k v o, k, Tree n k v o) -> Maybe (y : k ** v y)
treeLookup' k (Left t) = treeLookup k t
treeLookup' k (Right (t, k', t')) = if k <= k' then treeLookup k t else treeLookup k t'
--
-- treeLookup'TreeInsert'Branch2Lemma : DecEq k -> EqCompat k (Constraint (Eq ty) o) -> OrdCompat k o -> (key : k) -> (y : k) -> (val : v key) -> (x : Tree n k v o) -> (z : Tree n k v o) -> treeLookup' key (case treeInsert' key val z of { Left t2' => Left (Branch2 x y t2') ; Right (a, (b, c)) => Left (Branch3 x y a b c) }) = Just (key ** val)
--
-- treeLookup'TreeInsert' : DecEq k => (key : k) -> {o : Ord k} -> (val : v key) -> (t : Tree n k v o) -> EqCompat k (getEqFromOrd o) => OrdCompat k o => treeLookup' key (treeInsert' key val t) === Just (key ** val)
-- treeLookup'TreeInsert' @{_} key val (Leaf x y) @{eqCompatK} @{ordCompatK} with (compare key x) proof compareKeyX
--   _ | LT = let keyLeqRefl = toLeq @{ordCompatK} key key Refl in
--     rewrite soToEq keyLeqRefl in let keyRefl = toEq @{eqCompatK} key key Refl in
--       rewrite soToEq keyRefl in Refl
--   _ | EQ = let keyRefl = toEq @{eqCompatK} key key Refl in
--     rewrite soToEq keyRefl in Refl
--   _ | GT = let notKeyLeqX = toNotLeq @{ordCompatK} key x compareKeyX in
--     rewrite notKeyLeqX in let keyRefl = toEq @{eqCompatK} key key Refl in
--       rewrite soToEq keyRefl in Refl
-- treeLookup'TreeInsert' key val (Branch2 x y z) with (key <= y)
--   _ | False = ?prfh_3 --conArg conArg conArg key y val x z
--   _ | True = ?prfh_4
-- treeLookup'TreeInsert' key val (Branch3 x y z w s) = ?prfh_2

branchTreeInsert' : {auto o : Ord k} -> (key : k) -> v key -> Tree n k v o -> k -> Tree n k v o -> Either (Tree (S n) k v o) (Tree (S n) k v o, (k, Tree (S n) k v o))
branchTreeInsert' key val x y z = case treeInsert' {v} key val z of { Left t2' => Left (Branch2 {v} x y t2') ; Right (a, (b, c)) => Left (Branch3 {v} x y a b c) }

treeInsertCase : {auto o : Ord k} -> Either (Tree n k v o) (Tree n k v o, (k, Tree n k v o)) -> Either (Tree n k v o) (Tree (S n) k v o)
treeInsertCase t = case t of
  { Left t' => Left t'
  ; Right (a, (b, c)) => Right (Branch2 a b c)
  }

insertCase : {auto o : Ord k} -> {n : Nat} -> Either (Tree n k v o) (Tree (S n) k v o) -> SortedDMap k v
insertCase t = case t of
  { Left t' => M _ t'
  ; Right t' => M (S _) t'
  }

lookupInsert : DecEq k => (key : k) -> (val : v key) -> (m : SortedDMap k v) -> EqCompat k (getEq m) => OrdCompat k (getOrd m) => lookup key (insert key val m) === Just (key ** val)


lookupInsertBranch2 : DecEq k => {auto o : Ord k} -> EqCompat k (getEqFromOrd o) => OrdCompat k o => (key : k) -> {0 v : k -> Type} -> (val : v key) -> {n : Nat} -> (x : Tree n k v o) -> (y : k) -> {notKeyLeqY : (key <= y) === False} -> (z : Tree n k v o) -> lookup key (insertCase (treeInsertCase (branchTreeInsert' key val x y z))) = Just (key ** val)
lookupInsertBranch2 @{_} @{_} @{eqCompatK} @{ordCompatK} key val x y (Leaf z w) with (compare key z) proof compareKeyZ
  _ | LT =
    rewrite notKeyLeqY in let keyLeqRefl = toLeq @{ordCompatK} key key Refl in
      rewrite soToEq keyLeqRefl in let keyRefl = toEq @{eqCompatK} key key Refl in
        rewrite soToEq keyRefl in Refl
  _ | EQ =
    rewrite notKeyLeqY in let keyRefl = toEq @{eqCompatK} key key Refl in
      rewrite soToEq keyRefl in Refl
  _ | GT =
    rewrite notKeyLeqY in let notKeyLeqZ = toNotLeq @{ordCompatK} key z compareKeyZ in
      rewrite notKeyLeqZ in let keyRefl = toEq @{eqCompatK} key key Refl in
        rewrite soToEq keyRefl in Refl
lookupInsertBranch2 key val x y branch2@(Branch2 z w s) with (key <= w)
  _ | False =
    -- lookup key (case case case case treeInsert' key val s of { Left t2' => Left (Branch2 z w t2') ; Right (a, (b, c)) => Left (Branch3 z w a b c) } of { Left t2' => Left (Branch2 x y t2') ; Right (a, (b, c)) => Left (Branch3 x y a b c) } of { Left t' => Left t' ; Right (a, (b, c)) => Right (Branch2 a b c) } of { Left t' => M (S (S n)) t' ; Right t' => M (S (S (S n))) t' }) = Just (key ** val)
    let
      subprf = lookupInsertBranch2 key val z w s
      -- 0 subprf1Type := lookup key (insert key val (M _ branch2)) === Just (key ** val)
      -- subprf1 = lookupInsert key val (M _ s)
    in
      ?hl_3
  _ | True = ?hl_4
lookupInsertBranch2 key val x y (Branch3 z w s t u) = ?hl_2

lookupInsert @{decEqK} key val Empty @{eqCompatK} =
  let keyRefl = toEq @{eqCompatK} key key Refl in
    rewrite soToEq keyRefl in Refl
lookupInsert @{_} key val (M 0 (Leaf x y)) @{eqCompatK} @{ordCompatK} with (compare key x) proof compareKeyX
  _ | LT =
    let keyLeqRefl = toLeq @{ordCompatK} key key Refl in
      rewrite soToEq keyLeqRefl in let keyRefl = toEq @{eqCompatK} key key Refl in
        rewrite soToEq keyRefl in Refl
  _ | EQ = let keyRefl = toEq @{eqCompatK} key key Refl in
    rewrite soToEq keyRefl in Refl
  _ | GT =
    let notKeyLeqX = toNotLeq @{ordCompatK} key x compareKeyX in
      rewrite notKeyLeqX in let keyRefl = toEq @{eqCompatK} key key Refl in
        rewrite soToEq keyRefl in Refl
lookupInsert key val (M (S n) (Branch2 x y z)) with (key <= y)
  _ | False =
      ?lih_3 --conArg conArg conArg y key val x z
  _ | True = ?lih_4
lookupInsert key val (M (S n) (Branch3 x y z w s)) = ?lih_2

-- lookupInsert key val (M n tree) with (treeInsert' key val tree)
--   lookupInsert key val (M 0 tree) | (Left (Leaf x y)) = case choose (key == x) of
--     (Left z) => rewrite soToEq z in case @@(decEq key x) of
--       (((Yes Refl) ** snd)) => rewrite snd in ?lih1_10
--       (((No contra) ** snd)) => ?lih1_11
--     (Right z) => ?lih1_8
--   lookupInsert key val (M (S n) tree) | (Left (Branch2 x y z)) = ?lih1_5
--   lookupInsert key val (M (S n) tree) | (Left (Branch3 x y z w s)) = ?lih1_6
--   _ | (Right x) = ?lih1_1

{-
weaken : Term m a -> Term (S m) a
weaken (Var x) = Var (weaken x)
weaken (Val x) = Val x
weaken (Pair x y) = Pair (weaken x) (weaken y)

weakenSubKey : Substitution m n a -> Substitution (S m) n a
weakenSubKey s =
  let
    pairs = SortedMap.toList s
    weakenedPairs = map (\(k, v) => (weaken k, v)) pairs
  in fromList weakenedPairs

-- data IndMap : {0 k, v : Type} -> {auto 0 ord : Ord k} -> SortedMap k v -> Type where
--   Nil : {auto 0 ord : Ord k} -> IndMap {ord} SortedMap.empty
--   Cons : (0 x : k) -> (0 t : v) -> IndMap {ord} s -> IndMap {ord} (insert x t s)

data IndSub : (0 m, n : Nat) -> Substitution m n a -> Type where
  SubNil : IndSub n n SortedMap.empty
  SubCons : (x : Variable (S m)) -> (t : Term n a) -> IndSub m n s -> IndSub (S m) n (insert x t (weakenSubKey s))
