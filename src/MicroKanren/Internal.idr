module MicroKanren.Internal

import Control.Relation
import Control.WellFounded
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Nat
import Data.SortedMap
import Deriving.Functor
import MicroKanren.Internal.Constraint
import MicroKanren.Internal.Types
import MicroKanren.Internal.WellFormed

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
emptyState = MkState empty 0

{-
A Mechanized Textbook Proof of a Type Unification Algorithm
Rodrigo Ribeiro and Carlos Camarão
https://rodrigogribeiro.github.io/files/unify.pdf
-}

mappingAp : (Variable, Term a) -> (Term a -> Term a)
mappingAp m (Pair t1 t2) = Pair (m `mappingAp` t1) (m `mappingAp` t2)
mappingAp (a, t') (Var v) with (decEq a v)
  mappingAp (a, t') (Var v) | No contra = Var v
  mappingAp (a, t') (Var _) | Yes Refl = t'
mappingAp _ t = t

subAp : Substitution a -> (Term a -> Term a)
subAp [] t = t
subAp (m :: s') t = s' `subAp` (m `mappingAp` t)

subApCon : Substitution a -> (EqualityConstraint a -> EqualityConstraint a)
subApCon s (t, t') = (s `subAp` t) `eqCon` (s `subAp` t')

subApConList : Substitution a -> (ConstraintList a -> ConstraintList a)
subApConList s [] = []
subApConList s (x :: y) = (s `subApCon` x) :: (s `subApConList` y)

-- I think Lemma 3 from Ribeiro & Camarão is not needed to prove termination.

VarContext : Type
VarContext = List Variable

remove : VarContext -> Variable -> VarContext
remove [] _ = []
remove (x :: xs) v with (decEq x v)
  _ | (No _) = x :: (xs `remove` v)
  _ | (Yes _) = xs `remove` v

removeDomOf : VarContext -> Substitution a -> VarContext
removeDomOf context [] = context
removeDomOf context ((a, _) :: s) = (context `remove` a) `removeDomOf` s

subCompose : (s2, s1 : Substitution a) -> {auto 0 _ : WellFormedSub (`Elem` context) s1} -> {auto 0 _ : WellFormedSub (`Elem` (context `removeDomOf` s1)) s2} -> Substitution a
subCompose s2 s1 = s1 ++ s2

applySubEnd : (s1 : Substitution a) -> (m : (Variable, Term a)) -> (t : Term a) -> subAp (s1 ++ [m]) t === mappingAp m (subAp s1 t)
applySubEnd [] _ _ = Refl
applySubEnd (x :: xs) _ _ = applySubEnd xs _ _

subAppendApplication : {0 t : Term a} -> (s1, s2 : Substitution a) -> ((s1 ++ s2) `subAp` t) === (s2 `subAp` (s1 `subAp` t))
subAppendApplication s1 [] =
  rewrite appendNilRightNeutral s1 in
  Refl
subAppendApplication s1 (m :: s2') =
  let subprf = subAppendApplication (s1 ++ [m]) s2' in
  rewrite appendAssociative s1 [m] s2' in
  rewrite sym $ applySubEnd s1 m t in
  subprf

||| Theorem 1
subComposeApplication : {context : VarContext} -> {0 t : Term a} -> (s1, s2 : Substitution a) -> {0 wfS1 : WellFormedSub (`Elem` context) s1} -> {0 wfS2 : WellFormedSub {a} (`Elem` (context `removeDomOf` s1)) s2} -> ((subCompose @{wfS1} @{wfS2} s2 s1) `subAp` t) === (s2 `subAp` (s1 `subAp` t))
subComposeApplication s1 s2 = subAppendApplication s1 s2

data Occurs : Variable -> Term a -> Type where
  OccursFst : Occurs a t1 -> Occurs a (Pair t1 t2)
  OccursSnd : Occurs a t2 -> Occurs a (Pair t1 t2)
  OccursVar : Occurs a (Var a)

||| Lemma 4
decideOccurs : (a : Variable) -> (t : Term ty) -> Dec (Occurs a t)
decideOccurs a (Var i) with (decEq a i)
  _ | (No contra) = No $ \OccursVar => contra Refl
  decideOccurs a (Var a) | (Yes Refl) = Yes OccursVar
decideOccurs a (Val x) = No $ \case evidence impossible
decideOccurs a (Pair x y) with (decideOccurs a x) | (decideOccurs a y)
  _ | (Yes prf) | occursY = Yes (OccursFst prf)
  _ | (No contra) | (Yes prf) = Yes (OccursSnd prf)
  _ | (No contra) | (No f) = No $ \case
    (OccursFst z) => contra z
    (OccursSnd z) => f z

||| Lemma 5
%hint
differentVarsInContext : {a1, a2 : Variable} -> (context : VarContext) -> a1 `Elem` context -> Not (a2 === a1) -> (a1 `Elem` (context `remove` a2))
differentVarsInContext [] _ contra impossible
differentVarsInContext (x :: xs) a1InContext contra with (decEq x a2) | (a1InContext)
  _ | (No _) | There a1InXs =
    let subprf = differentVarsInContext xs a1InXs contra in
    There subprf
  _ | (No _) | Here = Here
  _ | (Yes _) | There a1InXs =
    let subprf = differentVarsInContext xs a1InXs contra in
    subprf
  _ | (Yes Refl) | Here = void $ contra Refl

||| Lemma 6
%hint
notOccursWellFormed : (t : Term ty) -> WellFormedTerm v t => Not (Occurs a t) -> WellFormedTerm (\var => (v var, Not (var === a))) t
notOccursWellFormed (Var i) @{WFVar iInContext} contra = WFVar (iInContext, \Refl => contra OccursVar)
notOccursWellFormed (Val x) contra = WFVal
notOccursWellFormed (Pair x y) @{WFPair wfX wfY} contra =
  WFPair (notOccursWellFormed x (\z => contra (OccursFst z))) (notOccursWellFormed y (\z => contra (OccursSnd z)))

degree : {context : VarContext} -> (c : ConstraintList a) -> WellFormedCList (`Elem` context) c => (Nat, Nat)
degree c = (length context, size c)

data LexLT : (relA : Rel a) -> (relB : Rel b) -> Rel (a, b) where
  FstLT : relA a b -> LexLT relA relB (a, c) (b, d)
  SndLT : relB a b -> LexLT relA relB (c, a) (c, b)

DegreeLT : Rel (Nat, Nat)
DegreeLT = LexLT LT LT

{- Well-founded lexicographic orders: an Idris translation of Agda's
Lexicographic.
https://agda.github.io/agda-stdlib/Induction.WellFounded.html#6170. -}
mutual
  degreeAccess : {x : a} -> {y : b} -> Accessible relA x -> WellFounded b relB -> Accessible (LexLT relA relB) (x, y)
  degreeAccess accA wfB =
    Access (degreeAccess' accA (wellFounded y) wfB)

  degreeAccess' : {x : a} -> {y : b} -> Accessible relA x -> Accessible relB y -> WellFounded b relB -> ((z : (a, b)) -> LexLT relA relB z (x, y) -> Accessible (LexLT relA relB) z)
  degreeAccess' (Access rsA) _ wfB _ (FstLT zxLessX) = degreeAccess (rsA _ zxLessX) wfB
  degreeAccess' accA (Access rsB) wfB _ (SndLT zyLessY) = Access (degreeAccess' accA (rsB _ zyLessY) wfB)

WellFounded a relA => WellFounded b relB => WellFounded (a, b) (LexLT relA relB) where
  wellFounded (x, y) = degreeAccess (wellFounded x) %search

ConstraintListLT : (c1, c2 : ConstraintList _) -> {context1, context2 : VarContext} -> WellFormedCList (`Elem` context1) c1 => WellFormedCList (`Elem` context2) c2 => Type
ConstraintListLT c1 c2 = DegreeLT (degree {context = context1} c1) (degree {context = context2} c2)

removeVarOutsideContextMaintainsLength : (context : VarContext) -> (a : Variable) -> Not (a `Elem` context) -> length (context `remove` a) === length context
removeVarOutsideContextMaintainsLength [] _ _ = Refl
removeVarOutsideContextMaintainsLength (x :: xs) a outsideContext with (decEq x a)
  _ | (No _) =
    let subprf = removeVarOutsideContextMaintainsLength xs a (outsideContext . There) in
    cong S subprf
  removeVarOutsideContextMaintainsLength (x :: xs) x outsideContext | (Yes Refl) = void $ outsideContext Here

removeVarInContextDecreasesLength : (context : VarContext) -> (a : Variable) -> a `Elem` context -> LT (length (context `remove` a)) (length context)
removeVarInContextDecreasesLength [] _ _ impossible
removeVarInContextDecreasesLength (x :: xs) a inContext with (decEq x a)
  _ | (No contra) =
    case inContext of
      There inXs =>
        let subprf = removeVarInContextDecreasesLength xs a inXs in
        LTESucc subprf
      Here =>
        void $ contra Refl
  _ | (Yes _) =
    case inContext of
      There inXs =>
        let subprf = removeVarInContextDecreasesLength xs a inXs in
        lteSuccRight subprf
      Here => case isElem x xs of
        Yes inXs =>
          let subprf = removeVarInContextDecreasesLength xs x inXs in
          lteSuccRight subprf
        No contra =>
          rewrite removeVarOutsideContextMaintainsLength xs x contra in
          reflexive

%hint
wellFormedTermMappingAp : {a : Variable} -> {context : VarContext} -> a `Elem` context => WellFormedTerm (`Elem` (context `remove` a)) t => (t1 : Term _) -> {auto wfT1 : WellFormedTerm (`Elem` context) t1} -> WellFormedTerm (`Elem` (context `remove` a)) (mappingAp (a, t) t1)
wellFormedTermMappingAp (Val x) = %search
wellFormedTermMappingAp (Var k) with (decEq a k)
  wellFormedTermMappingAp (Var k) | (Yes Refl) = %search
  wellFormedTermMappingAp (Var k) | (No contra) = let WFVar kInContext = wfT1 in WFVar $ differentVarsInContext context kInContext contra
wellFormedTermMappingAp (Pair x y) {wfT1 = WFPair wfX wfY} = WFPair (wellFormedTermMappingAp x) (wellFormedTermMappingAp y)

%hint
wellFormedCListSubAp : {a : Variable} -> {context : VarContext} -> a `Elem` context => WellFormedTerm (`Elem` (context `remove` a)) t => (c : ConstraintList _) -> {auto wfC : WellFormedCList (`Elem` context) c} -> WellFormedCList (`Elem` (context `remove` a)) ([(a, t)] `subApConList` c)
wellFormedCListSubAp [] = []
wellFormedCListSubAp ((t1, t2) :: y) {wfC = (wfT1, wfT2) :: wfCTail} = (wellFormedTermMappingAp t1, wellFormedTermMappingAp t2) :: wellFormedCListSubAp y

%hint
wellFormedCListVarConstraintCons : (a : Variable) -> v a => (t : Term _) -> WellFormedTerm v t => (c : ConstraintList _) -> WellFormedCList v c => WellFormedCList v ((Var a `eqCon` t) :: c)
wellFormedCListVarConstraintCons a t c = (WFVar %search, %search) :: %search

weakenContextMembership : (context : VarContext) -> {a : Variable} -> v `Elem` (context `remove` a) -> v `Elem` context
weakenContextMembership [] inContext = inContext
weakenContextMembership (x :: xs) inContext with (decEq x a) | (inContext)
  _ | (No _) | Here = Here
  _ | (No _) | There inXs = There (weakenContextMembership xs inXs)
  _ | (Yes Refl) | _ = There (weakenContextMembership xs inContext)

%hint
weakenContextWFTerm : (context : VarContext) -> {a : Variable} -> WellFormedTerm (`Elem` (context `remove` a)) t -> WellFormedTerm (`Elem` context) t
weakenContextWFTerm context (WFVar elem) = WFVar (weakenContextMembership context elem)
weakenContextWFTerm context WFVal = WFVal
weakenContextWFTerm context (WFPair fst snd) = WFPair (weakenContextWFTerm context fst) (weakenContextWFTerm context snd)

||| Lemma 7
||| See varctxt_lt_constraints_varl in rodrigogribeiro/unification.
subApDecreasesDegree : {context : VarContext} -> {a : Variable} ->
  {auto aInContext : a `Elem` context} -> {valTy : Type} -> {t : Term valTy} ->
  {auto wfT : WellFormedTerm (`Elem` (context `remove` a)) t} ->
  (c : ConstraintList valTy) ->
  {auto wfC : WellFormedCList (`Elem` context) c} ->
  ConstraintListLT
    @{wellFormedCListSubAp @{aInContext} @{wfT} c} ([(a, t)] `subApConList` c)
    @{wellFormedCListVarConstraintCons a @{%search} t @{weakenContextWFTerm context {a} wfT} c} ((Var a `eqCon` t) :: c)
subApDecreasesDegree _ = FstLT $ removeVarInContextDecreasesLength context a aInContext

{-
covering
walk : Term a -> Substitution a -> Term a
walk u s = case u of
  Var u => case lookup u s of
    Just term => walk term s
    Nothing => Var u
  _ => u

covering
occurs : Variable -> Term a -> Substitution a -> Bool
occurs x v s = let v = walk v s in
  case v of
    Var v => v == x
    Pair carV cdrV => occurs x carV s || occurs x cdrV s
    _ => False

{-
covering
extendSubstitution : Variable -> Term a -> Substitution a -> Maybe (Substitution a)
extendSubstitution x v s = if occurs x v s then Nothing else Just $ insert x v s

covering
unify : Eq a => Term a -> Term a -> Substitution a -> Maybe (Substitution a)
unify u v s =
  let
    u = walk u s
    v = walk v s
  in case (u, v) of
    (Var u, Var v) => if u == v then Just s else extendSubstitution u (Var v) s
    (Var u, v) => extendSubstitution u v s
    (u, Var v) => extendSubstitution v u s
    (Pair carU cdrU, Pair carV cdrV) => do
      s <- unify carU carV s
      unify cdrU cdrV s
    (Val u, Val v) => if u == v then Just s else Nothing
    _ => Nothing

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
