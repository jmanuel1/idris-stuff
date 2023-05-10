module MicroKanren.Internal.WellFormed

import Data.List.Quantifiers
import MicroKanren.Internal.Constraint
import MicroKanren.Internal.Types

%default total

public export
data WellFormedTerm : (Variable -> Type) -> Term a -> Type where
  WFVar : v a -> WellFormedTerm v (Var a)
  WFVal : WellFormedTerm v (Val val)
  WFPair : WellFormedTerm v t1 -> WellFormedTerm v t2 -> WellFormedTerm v (Pair t1 t2)

-- public export
-- %hint
-- wfFst : WellFormedTerm v (Pair t1 t2) -> WellFormedTerm v t1
-- wfFst (WFPair fst _) = fst
--
-- public export
-- %hint
-- wfSnd : WellFormedTerm v (Pair t1 t2) -> WellFormedTerm v t2
-- wfSnd (WFPair _ snd) = snd

public export
WellFormedConstraint : (Variable -> Type) -> EqualityConstraint a -> Type
WellFormedConstraint v (t1, t2) = (WellFormedTerm v t1, WellFormedTerm v t2)

namespace CList
  public export
  data WellFormedCList : (Variable -> Type)  -> ConstraintList a -> Type where
    Nil : WellFormedCList _ []
    (::) : WellFormedConstraint v con -> WellFormedCList v c -> WellFormedCList v (con :: c)

namespace Substitution
  public export
  data WellFormedSub : (Variable -> Type) -> Substitution a -> Type where
    Nil : WellFormedSub v [] -- ?
    (::) : (v a, WellFormedTerm (\var => (v var, Not (var === a))) t) -> WellFormedSub (\var => (v var, Not (var === a))) s' -> WellFormedSub v ((a, t) :: s')
