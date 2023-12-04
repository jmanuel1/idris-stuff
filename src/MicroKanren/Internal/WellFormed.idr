module MicroKanren.Internal.WellFormed

import Data.List.Elem
import Data.List.Elem.Extra
import Data.List.Quantifiers
import Data.Nat
import Decidable.Equality
import MicroKanren.Internal.Constraint
import MicroKanren.Internal.Types

%default total

public export
VarContext : Type
VarContext = List Variable

public export
remove : VarContext -> Variable -> VarContext
remove [] _ = []
remove (x :: xs) v with (decEq x v)
  _ | (No _) = x :: (xs `remove` v)
  _ | (Yes _) = xs `remove` v

public export
data WellFormedTerm : (Variable -> Type) -> Term a -> Type where
  WFVar : v a -> WellFormedTerm v (Var a)
  WFVal : WellFormedTerm v (Val val)
  WFPair : WellFormedTerm v t1 -> WellFormedTerm v t2 -> WellFormedTerm v (Pair t1 t2)

weakenAppendWFTermLeft : (xs, ys : VarContext) -> WellFormedTerm (`Elem` xs) t -> WellFormedTerm (`Elem` (xs ++ ys)) t
weakenAppendWFTermLeft xs ys (WFVar x) = WFVar (elemAppLeft xs ys x)
weakenAppendWFTermLeft xs ys WFVal = WFVal
weakenAppendWFTermLeft xs ys (WFPair x y) = WFPair (weakenAppendWFTermLeft xs ys x) (weakenAppendWFTermLeft xs ys y)

weakenAppendWFTermRight : (xs, ys : VarContext) -> WellFormedTerm (`Elem` ys) t -> WellFormedTerm (`Elem` (xs ++ ys)) t
weakenAppendWFTermRight xs ys (WFVar x) = WFVar (elemAppRight xs ys x)
weakenAppendWFTermRight xs ys WFVal = WFVal
weakenAppendWFTermRight xs ys (WFPair x y) = WFPair (weakenAppendWFTermRight xs ys x) (weakenAppendWFTermRight xs ys y)

placeTermInContext : (t : Term a) -> (ctxt : VarContext ** WellFormedTerm (`Elem` ctxt) t)
placeTermInContext (Var k) = ([k] ** WFVar Here)
placeTermInContext (Val x) = ([] ** WFVal)
placeTermInContext (Pair x y) =
  let
    (ctxtX ** wfX) = placeTermInContext x
    (ctxtY ** wfY) = placeTermInContext y
  in
    (ctxtX ++ ctxtY ** WFPair (weakenAppendWFTermLeft ctxtX ctxtY wfX) (weakenAppendWFTermRight ctxtX ctxtY wfY))

public export
WellFormedConstraint : (Variable -> Type) -> EqualityConstraint a -> Type
WellFormedConstraint v con = (WellFormedTerm v (fst con), WellFormedTerm v (snd con))

placeConstraintInContext : (con : EqualityConstraint a) -> (ctxt : VarContext ** WellFormedConstraint (`Elem` ctxt) con)
placeConstraintInContext (t1, t2) =
  let
    (ctxt1 ** wf1) = placeTermInContext t1
    (ctxt2 ** wf2) = placeTermInContext t2
  in
    (ctxt1 ++ ctxt2 ** (weakenAppendWFTermLeft ctxt1 ctxt2 wf1, weakenAppendWFTermRight ctxt1 ctxt2 wf2))

weakenAppendWFConLeft : (xs, ys : VarContext) -> WellFormedConstraint (`Elem` xs) t -> WellFormedConstraint (`Elem` (xs ++ ys)) t
weakenAppendWFConLeft ctxt1 ctxt2 (wf1, wf2) = (weakenAppendWFTermLeft ctxt1 ctxt2 wf1, weakenAppendWFTermLeft ctxt1 ctxt2 wf2)

weakenAppendWFConRight : (xs, ys : VarContext) -> WellFormedConstraint (`Elem` ys) t -> WellFormedConstraint (`Elem` (xs ++ ys)) t
weakenAppendWFConRight ctxt1 ctxt2 (wf1, wf2) = (weakenAppendWFTermRight ctxt1 ctxt2 wf1, weakenAppendWFTermRight ctxt1 ctxt2 wf2)

namespace CList
  public export
  data WellFormedCList : (Variable -> Type)  -> ConstraintList a -> Type where
    Nil : WellFormedCList _ []
    (::) : WellFormedConstraint v con -> WellFormedCList v c -> WellFormedCList v (con :: c)

  weakenAppendWFCListRight : (xs, ys : VarContext) -> WellFormedCList (`Elem` ys) t -> WellFormedCList (`Elem` (xs ++ ys)) t
  weakenAppendWFCListRight _ _ [] = []
  weakenAppendWFCListRight xs ys (wfCon :: wfCons) = (weakenAppendWFConRight xs ys wfCon :: weakenAppendWFCListRight xs ys wfCons)

  export
  placeCListInContext : (conList : ConstraintList a) -> (ctxt : VarContext ** WellFormedCList (`Elem` ctxt) conList)
  placeCListInContext [] = ([] ** [])
  placeCListInContext (con :: cons) =
    let
      (ctxtCon ** wfCon) = placeConstraintInContext con
      (ctxtCons ** wfCons) = placeCListInContext cons
    in
      (ctxtCon ++ ctxtCons ** weakenAppendWFConLeft ctxtCon ctxtCons wfCon :: weakenAppendWFCListRight ctxtCon ctxtCons wfCons)

namespace Substitution
  public export
  data WellFormedSub : VarContext -> Substitution a -> Type where
    Nil : WellFormedSub _ []
    (::) : (a `Elem` context, WellFormedTerm (`Elem` (context `remove` a)) t) -> WellFormedSub (context `remove` a) s' -> WellFormedSub context ((a, t) :: s')
