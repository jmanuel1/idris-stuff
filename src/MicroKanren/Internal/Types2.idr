module MicroKanren.Internal.Types

import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import public MicroKanren.Internal.Types.Term
import public MicroKanren.Internal.Types.Variable

%default total

public export
Substitution' : Type -> Type
Substitution' a = SortedMap Variable (Term a)

public export covering
walk : Term a -> Substitution' a -> Term a
walk u s = case u of
  Var u => case lookup u s of
    Just term => walk term s
    Nothing => Var u
  _ => u

public export
AssociationList : Type -> Type
AssociationList a = List (Variable, Term a)

public export
values : AssociationList a -> List (Term a)
values xs = map snd xs

mutual
  public export
  data Substitution : (0 _ : Substitution' a) {--> (0 _ : AssociationList a)-} -> Type where
    Empty : Substitution SortedMap.empty --[]
    Extend : (0 x : Variable) -> (0 v : Term a) -> (0 _ : Substitution s {-l-}) -> (0 _ : So (not (occurs x v s))) -> Substitution (insert x v s) --((x, v) :: l)
  -- Substitution a = (s : SortedMap Variable (Term a) ** All (\x => All (\v => So (not (occurs x v s))) (values s)) (keys s))

  public export
  covering
  occurs : Variable -> Term a -> Substitution' a -> Bool
  occurs x v s = let v = walk v s in
    case v of
      Var v => v == x
      Pair carV cdrV => occurs x carV s || occurs x cdrV s
      _ => False

public export
record State a where
  constructor MkState
  subMap : Substitution' a
  substitution : Substitution subMap
  nextVar : Variable
