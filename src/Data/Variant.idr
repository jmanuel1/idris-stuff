module Data.Variant

import Data.List.Quantifiers
import Data.Singleton
import Derive.Eq
import Generics.Derive

%language ElabReflection

%hide Generics.Derive.Eq
%hide Generics.Derive.Ord
%hide Data.Vect.Quantifiers.Any.Any

%default total

namespace Any
  Variant : (labelTy, Type) -> Type
  Variant (label, ty) = (Singleton label, ty)

  Shape : Type
  Shape = Any Variant [("Square", Double), ("Circle", Double)]

  -- inject : (label : labelTy ** variantTy label row)
  --
  -- Variant' v = (val : _ ** inject val)

  area : Shape -> Double
  area (Here (Val "Square", side)) = side * side
  area (There (Here (Val "Circle", radius))) = 3.14 * radius * radius

  {-
  Problems:
  * The row is ordered because of the Here/There contructors.
    * Extensibility won't fix this.
    * Higher-kinded mapping won't fix this.
  -}

{-
namespace AnyWithViewsEqual
    ShapeVariant : String -> Type
    ShapeVariant "Square" = Double
    ShapeVariant "Circle" = Double
    ShapeVariant _ = Void

    Row : Type -> Type
    Row labelTy = (labelTy -> Type, List labelTy)

    ShapeDef : Row ?
    ShapeDef = (ShapeVariant, ["Square", "Circle"])

    Shape : Type
    Shape = Any (fst ShapeDef) (snd ShapeDef)

    Sum : Row labelTy -> Type
    Sum r = Any (fst r) (snd r)

    -- I could use isElem
    TyForLabel' : (l : labelTy) -> (labelTy -> Type) -> List labelTy -> Type
    -- TyForLabel' l _ [] = Void
    -- TyForLabel' l f (l' :: ls) =
    --   case (decEq l l') of
    --     Yes Refl => f l
    --     No contra => TyForLabel' l f ls
    TyForLabel' l f _ = f l

    TyForLabel : (l : labelTy) -> (r : Row labelTy) -> Type
    TyForLabel l r = TyForLabel' l (fst r) (snd r)

    inject : (label : labelTy) -> {r : ?} -> (i : label `Elem` (Builtin.snd r)) => TyForLabel label r -> Sum r
    inject {r = (_, [])} _ v impossible
    inject {r = (f, label :: xs)} label val @{Here} = Here val -- with (decEq label label)
      -- _ | Yes Refl = Here val --with (decEqSelfIsYes {x = label})
      -- _ | No contra = void $ contra Refl
      -- _ | refl = Here $ replace {p = \case
      --            { Yes Refl => f label
      --            ; No contra => TyForLabel' label f xs
      --            }} refl val
    inject {r = (f, x :: xs)} label val @{(There y)} = There $ inject label {r = (f, xs)} val --with (decEq label x)
      -- inject {r = (f, label :: xs)} label val @{_} @{(There y)} | Yes Refl = Here val
      -- _ | No contra = There $ inject label {r = (f, xs)} val

    data MatchView : (r : Row labelTy) -> Sum r -> Type where
      Match : {0 r : Row labelTy} -> (label : labelTy) -> (i : label `Elem` (Builtin.snd r)) => (value : TyForLabel label r) -> MatchView r $ inject label {r} value @{i}

    matchView : {r : Row labelTy} -> (v : Sum r) -> MatchView r v
    matchView {r = r@(f, label :: xs)} (Here val) = --with (decEq label label)
      Match {r = (f, label :: xs)} {i = Here} label val
      -- _ | No contra = ?fbfb
      -- let m = Match @{eq} {r} label val in ?hgnf_0 --Match ?gngfb ?fbfb -- Need (label == label) to become True
    matchView {r = (f, _ :: xs)} (There x) =
      let Match label val = matchView {r = (f, xs)} x in Match label val --?hgnf_1 --Match ?gngfb_0 ?fbfb_0

    partial
    area : Shape -> Double
    area shape with (matchView {r = ShapeDef} shape)
      area _ | Match "Square" side = side * side
      area _ | Match "Circle" radius = 3.14 * radius * radius
    -- area (Here (Val "Square", side)) = side * side
    -- area (There (Here (Val "Circle", radius))) = 3.14 * radius * radius

    data Label = Square | Circle | Triangle

    %runElab derive "Label" [Generic, Meta, Eq]

    ShapeDef' : Label -> Type
    ShapeDef' Square = Double
    ShapeDef' Circle = Double
    ShapeDef' Triangle = (Double, Double)

    0 Shape' : Type
    Shape' = Sum (ShapeDef', [Square, Circle])

    partial
    area' : Shape' -> Double
    area' shape with (matchView {r = (ShapeDef', [Square, Circle])} shape)
      area' _ | Match Square side = side * side
      area' _ | Match Circle radius = 3.14 * radius * radius

    private infixl 10 //
    (//) : (r : Row labelTy) -> (s : List labelTy) -> Row labelTy
    (r // s) = (fst r, snd r ++ s)

    withoutLabels : Eq labelTy => Row labelTy -> List labelTy -> Row labelTy
    -- r `withoutLabels` labels = filter (\(l, _) => not (l `elem` labels)) r
    r `withoutLabels` labels = (fst r, deleteFirstsBy (\m, l => l == m) (snd r) labels)

    match : DecEq labelTy => Eq labelTy => {r : ?} -> Sum r -> (cases : List (label : labelTy ** TyForLabel label r -> a)) -> (Sum (r `withoutLabels` map DPair.fst cases) -> a) -> a
    match v cases k with (matchView {r} v)
      match v@_ [] k | Match label val = k v
      -- match {r = (f, [])} _ ((caseLabel ** arm) :: cases) k | Match label val = ?vbfd
      match {r = (f, r)} v@_ ((caseLabel ** arm) :: cases) k | Match label val with (decEq caseLabel label)--(r)
        match {r = (f, r)} _ ((label ** arm) :: cases) k | Match label val | Yes Refl = arm val
        match {r = (f, r)} v ((caseLabel ** arm) :: cases) k | Match label val | No contra = match {r = (f, r)} v cases ?bdrvbdbd2
        -- _ | (activeLabel :: activeLabels) with (activeLabel == caseLabel)
        --   _ | True = ?vbfd1
        --   _ | False = ?vbfd12
        -- _ | [] = ?fbdf
-}

{-
    areaOpen : {r : ?} -> Sum ((ShapeDef', [Square, Circle]) // r) -> (Sum (ShapeDef', r) -> Double) -> Double
    areaOpen shape k =
      match {r = (ShapeDef', [Square, Circle]) // r} shape -- Have to specify implicit argument :(
        [(Square ** \side => side * side),
          (Circle ** \radius => 3.14 * radius * radius)]
        k -- No "row equality" relation needed here! Although I figure I'll want one eventually

    TriangleDef : Row Label
    TriangleDef = (ShapeDef', [Square, Circle]) // [Triangle]

    (.only) : Any p [x] -> p x
    (.only) (Here a) = a

    areaTriangle : Sum TriangleDef -> Double
    areaTriangle shape = areaOpen {r = [Triangle]} shape $ \x => 0.5 * fst x.only * snd x.only
      -- Can't match on dims for some reason with explicit r :(
      -- (Triangle ** (base, height)) =>
      --   0.5 * base * height

-}

namespace AnyWithViews
    Variant : (labelTy, Type) -> Type
    Variant (label, ty) = (Singleton label, ty)

    Row : Type -> Type
    Row labelTy = List (labelTy, Type)

    ShapeDef : Row ?
    ShapeDef = [("Square", Double), ("Circle", Double)]

    Shape : Type
    Shape = Any Variant ShapeDef

    TyForLabel : Eq labelTy => labelTy -> Row labelTy -> Type
    TyForLabel l r = fromMaybe Void (lookup l r)

    inject : Eq labelTy => {0 label : labelTy} -> {r : ?} -> Variant (label, TyForLabel label r) -> Any Variant r
    inject {r = []} (_, v) impossible
    inject {r = ((x, y) :: xs)} (Val label, val) with (label == x)
      _ | True = Here (Val x, val)
      _ | False = There $ inject {r = xs} (Val label, val)

    -- data MatchView : (r : Row labelTy) -> Any Variant r -> Type where
    --   Match :


    data MatchView : {-{auto eq : Eq labelTy} -> -}(r : Row labelTy) -> Any Variant r -> Type where
      Match : {auto eq : Eq labelTy} -> (label : labelTy) -> (value : TyForLabel @{eq} label r) -> MatchView {-@{eq}-} r $ inject (Val label, value)

    -- valPrf : (x : Singleton y) -> x === Val y
    -- valPrf x = ?dfvdfv
{-
    matchView : Eq labelTy => {r : Row labelTy} -> (v : Any Variant r) -> MatchView r v
    matchView @{eq} {r = r@((label, ty) :: xs)} (Here (vlabel, val)) =
      let m = Match @{eq} {r} label val in ?hgnf_0 --Match ?gngfb ?fbfb -- Need (label == label) to become True
    matchView (There x) = ?hgnf_1 --Match ?gngfb_0 ?fbfb_0
-}
    area : Shape -> Double
    -- area shape with
    -- area (Here (Val "Square", side)) = side * side
    -- area (There (Here (Val "Circle", radius))) = 3.14 * radius * radius

{-
namespace HigherKindedUsingVoid
  ShapeDef : String -> Type
  ShapeDef "Square" = Double
  ShapeDef "Circle" = Double
  ShapeDef _ = Void

  0 -- QUESTION: Why does labelTy need to be accessible?
  Variant : (labelTy -> Type) -> Type
  Variant f = (label : labelTy ** f label)

  0 Shape : Type
  Shape = Variant ShapeDef

  partial
  area : Shape -> Double
  area ("Square" ** side) = side * side
  area ("Circle" ** radius) = 3.14 * radius * radius

  data Label = Square | Circle | Triangle

  %runElab derive "Label" [Generic, Meta, Eq]

  ShapeDef' : Label -> Type
  ShapeDef' Square = Double
  ShapeDef' Circle = Double
  ShapeDef' _ = Void

  0 Shape' : Type
  Shape' = Variant ShapeDef'

  area' : Shape' -> Double
  area' (Square ** side) = side * side
  area' (Circle ** radius) = 3.14 * radius * radius

  private infixl 10 //
  (//) : (r, s : labelTy -> Type) -> (labelTy -> Type)
  (r // s) label =
    case r label of
      Void => s label
      ty => ty

  withoutLabels : Eq labelTy => (labelTy -> Type) -> List labelTy -> labelTy -> Type
  (r `withoutLabels` labels) l = ifThenElse (l `elem` labels) Void (r l)

  match : Eq labelTy => Variant r -> (cases : List (label : labelTy ** r label -> a)) -> (Variant (r `withoutLabels` map DPair.fst cases) -> a) -> a

  areaOpen : Variant (ShapeDef' // r) -> (Variant r -> Double) -> Double
  areaOpen shape k =
    match shape
      [(Square ** \side => side * side),
        (Circle ** \radius => 3.14 * radius * radius)]
      ?holek -- The rows are functions and I'd need extensionality (even just as a relation)
-}

namespace FirstOrderUsingAbsence
  Row : Type -> Type
  Row labelTy = List (labelTy, Type)

  ShapeDef : Row ?
  ShapeDef = [("Square", Double), ("Circle", Double)]

  TyForLabel : Eq labelTy => labelTy -> Row labelTy -> Type
  TyForLabel l r = fromMaybe Void (lookup l r)

  0 -- QUESTION: Why does labelTy need to be accessible?
  Variant : Eq labelTy => Row labelTy -> Type
  Variant f = (label : labelTy ** TyForLabel label f)

  0 Shape : Type
  Shape = Variant ShapeDef

  partial
  area : Shape -> Double
  area ("Square" ** side) = side * side
  area ("Circle" ** radius) = 3.14 * radius * radius

  data Label = Square | Circle | Triangle

  %runElab derive "Label" [Generic, Meta, Eq]

  ShapeDef' : Row Label
  ShapeDef' = [(Square, Double), (Circle, Double)]

  0 Shape' : Type
  Shape' = Variant ShapeDef'

  area' : Shape' -> Double
  area' (Square ** side) = side * side
  area' (Circle ** radius) = 3.14 * radius * radius

  private infixl 10 //
  (//) : (r, s : Row labelTy) -> Row labelTy
  (r // s) = r ++ s

  withoutLabels : Eq labelTy => Row labelTy -> List labelTy -> Row labelTy
  -- r `withoutLabels` labels = filter (\(l, _) => not (l `elem` labels)) r
  r `withoutLabels` labels = deleteFirstsBy (\m, (l, _) => l == m) r labels

  match : Eq labelTy => Variant r -> (cases : List (label : labelTy ** TyForLabel label r -> a)) -> (Variant (r `withoutLabels` map DPair.fst cases) -> a) -> a

  areaOpen : Variant (ShapeDef' // r) -> (Variant r -> Double) -> Double
  areaOpen shape k =
    match {r = ShapeDef' // r} shape -- Have to specify implicit argument :(
      [(Square ** \side => side * side),
        (Circle ** \radius => 3.14 * radius * radius)]
      k -- No "row equality" relation needed here! Although I figure I'll want one eventually

  TriangleDef : Row Label
  TriangleDef = ShapeDef' // [(Triangle, (Double, Double))]

  areaTriangle : Variant TriangleDef -> Double
  areaTriangle shape = areaOpen {r = [(Triangle, (Double, Double))]} shape $ \case
    -- Can't match on dims for some reason with explicit r :(
    (Triangle ** (base, height)) =>
      0.5 * base * height
    -- Either r must be explicit or these redundant clauses must be here :(
    -- (Square ** dims {-(base, height)-}) => absurd dims --0.5 * base * height
    -- (Circle {-Triangle-} ** dims {-(base, height)-}) => absurd dims --0.5 * base * height
