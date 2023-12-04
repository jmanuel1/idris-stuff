module MicroKanren.Internal

import Control.Relation
import Control.WellFounded
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Nat
import Data.SortedMap
import Decidable.Order.Strict
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

removeDomOf : VarContext -> Substitution a -> VarContext
removeDomOf context [] = context
removeDomOf context ((a, _) :: s) = (context `remove` a) `removeDomOf` s

subCompose : (s2, s1 : Substitution a) -> {auto 0 _ : WellFormedSub context s1} -> {auto 0 _ : WellFormedSub (context `removeDomOf` s1) s2} -> Substitution a
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
subComposeApplication : {context : VarContext} -> {0 t : Term a} -> (s1, s2 : Substitution a) -> {0 wfS1 : WellFormedSub context s1} -> {0 wfS2 : WellFormedSub {a} (context `removeDomOf` s1) s2} -> ((subCompose @{wfS1} @{wfS2} s2 s1) `subAp` t) === (s2 `subAp` (s1 `subAp` t))
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
notOccursWellFormed : (t : Term ty) -> {context : VarContext} -> WellFormedTerm (`Elem` context) t => {a : Variable} -> Not (Occurs a t) -> WellFormedTerm (`Elem` (context `remove` a)) t
notOccursWellFormed (Var i) @{WFVar iInContext} contra = WFVar (differentVarsInContext context iInContext $ \prf => contra $ rewrite sym prf in OccursVar)
notOccursWellFormed (Val x) contra = WFVal
notOccursWellFormed (Pair x y) @{WFPair wfX wfY} contra =
  WFPair (notOccursWellFormed x (\z => contra (OccursFst z))) (notOccursWellFormed y (\z => contra (OccursSnd z)))

degree : {context : VarContext} -> (c : ConstraintList a) -> WellFormedCList (`Elem` context) c => (Nat, Nat)
degree c = (length context, size c)

data LexLT : (relA : Rel a) -> (relB : Rel b) -> Rel (a, b) where
  FstLT : {0 x : a} -> {0 y : a} -> relA x y -> LexLT relA relB (x, c) (y, d)
  SndLT : {0 x : b} -> {0 y : b} -> relB x y -> LexLT relA relB (c, x) (c, y)

Irreflexive a relA => Irreflexive b relB => Irreflexive (a, b) (LexLT relA relB) where
  irreflexive (FstLT xx) = irreflexive {rel = relA} xx
  irreflexive (SndLT xx) = irreflexive {rel = relB} xx

DegreeLT : Rel (Nat, Nat)
DegreeLT = LexLT LT LT

ltTransitiveS : {a, b, c : Nat} -> LT a b -> LT b (S c) -> LT a c
ltTransitiveS ab (LTESucc bc) = transitive ab bc

{- Well-founded lexicographic orders: an Idris translation of Agda's
Lexicographic.
https://agda.github.io/agda-stdlib/Induction.WellFounded.html#6170. -}
mutual
  degreeAccess : {y : b} -> Accessible relA x -> WellFounded b relB -> Accessible (LexLT relA relB) (x, y)
  degreeAccess accA wfB =
    Access (degreeAccess' accA (wellFounded y) wfB)

  degreeAccess' : Accessible relA x -> Accessible relB y -> WellFounded b relB -> ((z : (a, b)) -> LexLT relA relB z (x, y) -> Accessible (LexLT relA relB) z)
  degreeAccess' (Access rsA) accB wfB (zx, zy) (FstLT zxLessX) = degreeAccess (rsA zx zxLessX) wfB
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

wellFormedTermMappingAp : {a : Variable} -> {context : VarContext} -> a `Elem` context => WellFormedTerm (`Elem` (context `remove` a)) t => (t1 : Term _) -> {auto wfT1 : WellFormedTerm (`Elem` context) t1} -> WellFormedTerm (`Elem` (context `remove` a)) (mappingAp (a, t) t1)
wellFormedTermMappingAp (Val x) = %search
wellFormedTermMappingAp (Var k) with (decEq a k)
  wellFormedTermMappingAp (Var k) | (Yes Refl) = %search
  wellFormedTermMappingAp (Var k) | (No contra) = let WFVar kInContext = wfT1 in WFVar $ differentVarsInContext context kInContext contra
wellFormedTermMappingAp (Pair x y) {wfT1 = WFPair wfX wfY} = WFPair (wellFormedTermMappingAp x) (wellFormedTermMappingAp y)

wellFormedCListSubAp : {a : Variable} -> {context : VarContext} -> a `Elem` context => {auto wfT : WellFormedTerm (`Elem` (context `remove` a)) t} -> (c : ConstraintList _) -> {auto wfC : WellFormedCList (`Elem` context) c} -> WellFormedCList (`Elem` (context `remove` a)) ([(a, t)] `subApConList` c)
wellFormedCListSubAp [] = []
wellFormedCListSubAp ((t1, t2) :: y) {wfC = (wfT1, wfT2) :: wfCTail} = (wellFormedTermMappingAp t1, wellFormedTermMappingAp t2) :: wellFormedCListSubAp y

wellFormedCListVarConstraintCons : (a : Variable) -> v a => (t : Term _) -> WellFormedTerm v t => (c : ConstraintList _) -> WellFormedCList v c => WellFormedCList v ((Var a `eqCon` t) :: c)
wellFormedCListVarConstraintCons a t c = (WFVar %search, %search) :: %search

weakenContextMembership : (context : VarContext) -> {a : Variable} -> v `Elem` (context `remove` a) -> v `Elem` context
weakenContextMembership [] inContext = inContext
weakenContextMembership (x :: xs) inContext with (decEq x a) | (inContext)
  _ | (No _) | Here = Here
  _ | (No _) | There inXs = There (weakenContextMembership xs inXs)
  _ | (Yes Refl) | _ = There (weakenContextMembership xs inContext)

-- NOTE: Marking this %hint contributes noticeably to type checking time.
weakenContextWFTerm : (context : VarContext) -> {a : Variable} -> WellFormedTerm (`Elem` (context `remove` a)) t -> WellFormedTerm (`Elem` context) t
weakenContextWFTerm context (WFVar elem) = WFVar (weakenContextMembership context elem)
weakenContextWFTerm context WFVal = WFVal
weakenContextWFTerm context (WFPair fst snd) = WFPair (weakenContextWFTerm context fst) (weakenContextWFTerm context snd)

||| Lemma 7
||| See varctxt_lt_constraints_varl in rodrigogribeiro/unification.
subApDecreasesDegree : {context : VarContext} -> {a : Variable} ->
  {auto aInContext : a `Elem` context} -> {0 valTy : Type} -> {t : Term valTy} ->
  {auto wfT : WellFormedTerm (`Elem` (context `remove` a)) t} ->
  (c : ConstraintList valTy) ->
  {auto wfC : WellFormedCList (`Elem` context) c} ->
  ConstraintListLT
    @{wellFormedCListSubAp @{aInContext} @{wfT} c} ([(a, t)] `subApConList` c)
    @{wellFormedCListVarConstraintCons a @{%search} t @{weakenContextWFTerm context {a} wfT} c} ((Var a `eqCon` t) :: c)
subApDecreasesDegree _ = FstLT $ removeVarInContextDecreasesLength context a aInContext

||| Lemma 8
fewerPairsImpliesLowerDegree : {t1, t1', t2, t2' : Term valTy} -> {c : ConstraintList valTy} -> WellFormedTerm (`Elem` context) t1 => WellFormedTerm (`Elem` context) t2 => WellFormedTerm (`Elem` context) t1' => WellFormedTerm (`Elem` context) t2' => WellFormedCList (`Elem` context) c => ConstraintListLT {context1 = context, context2 = context} ((t1 `eqCon` t1') :: (t2 `eqCon` t2') :: c) (((Pair t1 t2) `eqCon` (Pair t1' t2')) :: c)
fewerPairsImpliesLowerDegree = SndLT $ splitPairConstraintDecreasesSize c

||| Lemma 9
fewerConstraintsImpliesLowerDegree : {t, t' : Term valTy} -> {c : ConstraintList valTy} -> WellFormedTerm (`Elem` context) t => WellFormedTerm (`Elem` context) t' => WellFormedCList (`Elem` context) c => ConstraintListLT {context1 = context, context2 = context} c ((t `eqCon` t') :: c)
fewerConstraintsImpliesLowerDegree = SndLT $ removeConstraintDecreasesSize t t'

ConstraintListInContext : VarContext -> Type -> Type
ConstraintListInContext context a = (c : ConstraintList a ** WellFormedCList (`Elem` context) c)

ConstraintListInContextLT : {context1, context2 : VarContext} -> (c1 : ConstraintListInContext context1 a) -> (c2 : ConstraintListInContext context2 a) -> Type
ConstraintListInContextLT c1 c2 = ConstraintListLT {context1, context2} @{snd c1} @{snd c2} (fst c1) (fst c2)

SubstitutionInContext : VarContext -> Type -> Type
SubstitutionInContext context a = (s : Substitution a ** WellFormedSub context s)

Eq a => Eq (Term a) where
  Var a == Var b = a == b
  Val a == Val b = a == b
  Pair a b == Pair c d = a == c && b == d
  _ == _ = False

unify' : Eq a => {context1 : VarContext} -> (c1InContext : ConstraintListInContext context1 a) -> ({context2 : VarContext} -> (c2InContext : ConstraintListInContext context2 a) -> ConstraintListInContextLT {context1 = context2, context2 = context1} c2InContext c1InContext -> Maybe (SubstitutionInContext context2 a)) -> Maybe (SubstitutionInContext context1 a)
unify' ([] ** wfC1) rec = Just ([] ** [])
unify' (((Var a, Var b) :: c1) ** ((WFVar wfA, WFVar wfB) :: wfC1)) rec with (decEq a b)
  _ | (No contra) = do
    let wfBContextRemoveA = differentVarsInContext context1 wfB contra
    let wfT = WFVar wfBContextRemoveA
    (s ** wfS) <- rec (subApConList [(a, Var b)] c1 ** wellFormedCListSubAp {context = context1, wfT} c1) (subApDecreasesDegree {wfT} c1)
    pure $ (subCompose {context = context1} s [(a, Var b)] @{[(wfA, wfT)]} ** ((wfA, wfT) :: wfS))
  _ | (Yes prf) = rec (c1 ** wfC1) (fewerConstraintsImpliesLowerDegree @{WFVar wfA} @{WFVar wfB})
unify' (((Var a, t) :: c1) ** ((WFVar wfA, wfT) :: wfC1)) rec with (decideOccurs a t)
  _ | (No contra) = do
    let wfT = notOccursWellFormed t contra
    (s ** wfS) <- rec (subApConList [(a, t)] c1 ** wellFormedCListSubAp {context = context1, wfT} c1) (subApDecreasesDegree {wfT} c1)
    pure $ (subCompose {context = context1} s [(a, t)] @{[(wfA, wfT)]} ** ((wfA, wfT) :: wfS))
  _ | (Yes occursPrf) = Nothing
unify' (((t, Var a) :: c1) ** ((wfT, WFVar wfA) :: wfC1)) rec with (decideOccurs a t)
  _ | (No contra) = do
    let wfT = notOccursWellFormed t contra
    (s ** wfS) <- rec (subApConList [(a, t)] c1 ** wellFormedCListSubAp {context = context1, wfT} c1) (rewrite plusCommutative (size t) 1 in subApDecreasesDegree {wfT} c1)
    pure $ (subCompose {context = context1} s [(a, t)] @{[(wfA, wfT)]} ** ((wfA, wfT) :: wfS))
  _ | (Yes occursPrf) = Nothing
unify' (((Pair t1 t2, Pair t t') :: c1) ** ((WFPair wfT1 wfT2, WFPair wfT wfT') :: wfC1)) rec =
  rec (((t1 `eqCon` t) :: (t2 `eqCon` t') :: c1) ** %search) fewerPairsImpliesLowerDegree
unify' (((t, t') :: c1) ** ((wfT, wfT') :: wfC1)) rec =
  if t == t' then rec (c1 ** wfC1) (fewerConstraintsImpliesLowerDegree @{wfT} @{wfT'}) else Nothing

ConstraintListInExistentialContext : Type -> Type
ConstraintListInExistentialContext a = (context : VarContext ** ConstraintListInContext context a)

ConstraintListInExistentialContextLT : (c1, c2 : ConstraintListInExistentialContext a) -> Type
ConstraintListInExistentialContextLT c1 c2 = ConstraintListInContextLT {context1 = fst c1, context2 = fst c2} (snd c1) (snd c2)

0 UnifyP : ConstraintListInExistentialContext a -> Type
UnifyP c = Maybe (SubstitutionInContext (fst c) a)

unifyExistential' : Eq a => (c1InContext : ConstraintListInExistentialContext a) -> ((c2InContext : ConstraintListInExistentialContext a) -> ConstraintListInExistentialContextLT c2InContext c1InContext -> UnifyP c2InContext) -> UnifyP c1InContext
unifyExistential' (c1Context ** c1) rec = unify' c1 $ \c2InContext, lt => rec (_ ** c2InContext) lt

accInd' : {0 P : b -> Type} -> (0 f : b -> a) -> ((x : b) -> ((y : b) -> rel (f y) (f x) -> P y) -> P x) -> (z : b) -> (0 _ : Accessible rel (f z)) -> P z
accInd' f fun z (Access rec) = fun z $ \y, lt => accInd' f fun y (rec (f y) lt)

unifyExistential : Eq a => (c : ConstraintListInExistentialContext a) -> Maybe (SubstitutionInContext (fst c) a)
unifyExistential c = accInd' (\c => degree @{snd $ snd c} (fst $ snd c)) unifyExistential' c (wellFounded {rel = LexLT LT LT} (degree @{snd $ snd c} (fst $ snd c)))

subToConList : Substitution a -> ConstraintList a
subToConList = makeConstraintList . map (mapFst Var)

unify : Eq a => Term a -> Term a -> Substitution a -> Maybe (Substitution a)
unify u v s =
  let
    conList = (u `eqCon` v) :: subToConList s
    (ctxt ** wf) = placeCListInContext conList
  in map fst $ unifyExistential (ctxt ** conList ** wf)

export
callFresh : (Term a -> Goal a) -> Goal a
callFresh f = \state => let c = state.nextVar in f (Var c) ({ nextVar $= (+ 1) } state)

export
(===) : Eq a => Term a -> Term a -> Goal a
u === v = \state => let s = unify u v state.substitution in
  case s of
    Just s => pure ({substitution := s} state)
    Nothing => neutral

export
disj : Goal a -> Goal a -> Goal a
disj g1 g2 = \state => g1 state <+> g2 state

export
conj : Goal a -> Goal a -> Goal a
conj g1 g2 = \state => g1 state >>= g2
