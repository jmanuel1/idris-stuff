module MicroKanren.Internal.Types

import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import public MicroKanren.Internal.Types.Term
import public MicroKanren.Internal.Types.Variable

%default total

Substitution' : Type -> Type
Substitution' a = SortedMap Variable (Term a)

public export covering
walk : Term a -> Substitution' a -> Term a
walk u s = case u of
  Var u => case lookup u s of
    Just term => walk term s
    Nothing => Var u
  _ => u

mutual
  public export
  Substitution : Type -> Type
  Substitution a = (s : SortedMap Variable (Term a) ** All (\x => All (\v => So (not (occurs x v s))) (values s)) (keys s))

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
  substitution : Substitution a
  nextVar : Variable
