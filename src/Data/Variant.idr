module Data.Variant

import Data.List.Quantifiers
import Data.Singleton
import Decidable.Equality.Core
import Derive.Eq
import Deriving.Functor
import Deriving.Show
import Generics.Derive

%language ElabReflection

%hide Data.Vect.Quantifiers.Any.Any
%hide Generics.Derive.Eq
%hide Generics.Derive.Ord
%hide Language.Reflection.Syntax.as
%hide Language.Reflection.Syntax.rec

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
    -- TODO: Leave out the labels???
    Shape = Any Variant ShapeDef

    -- I think the later proofs would be easier if I computed the type using an
    -- interface...
    TyForLabel : DecEq labelTy => labelTy -> Row labelTy -> Type
    TyForLabel l [] = Void
    TyForLabel l ((m, t) :: xs) with (decEq l m)
      _ | No contra = TyForLabel l xs
      TyForLabel l ((l, t) :: xs) | Yes Refl = t

    inject : DecEq labelTy => {0 label : labelTy} -> {r : ?} -> Variant (label, TyForLabel label r) -> Any Variant r
    inject {r = []} (_, v) impossible
    inject {r = ((x, y) :: xs)} (Val label, val) with (decEq label x)
      _ | No _ = There $ inject {r = xs} (Val label, val)
      inject {r = ((label, y) :: xs)} (Val label, val) | Yes Refl = Here (Val label, val)

    data MatchView : {auto eq : DecEq labelTy} -> (r : Row labelTy) -> Any Variant r -> Type where
      Match : {auto eq : DecEq labelTy} -> (label : labelTy) -> (value : TyForLabel @{eq} label r) -> MatchView @{eq} r $ inject (Val label, value)

    -- valPrf : (x : Singleton y) -> x === Val y
    -- valPrf x = ?dfvdfv

    -- matchView : DecEq labelTy => {r : Row labelTy} -> (v : Any Variant r) -> MatchView r v
    -- matchView @{eq} {r = r@((label, ty) :: xs)} (Here (Val label, val)) with (decEq label label)
    --   _ | Yes Refl =
    --   -- let m = Match @{eq} {r} label val in
    --   -- rewrite sym $ decEqSelfIsYes {x = label} in
    --     Match label ?fgbfdbval --Match ?gngfb ?fbfb -- Need (label == label) to become True
    --   _ | No contra = contra Refl
    -- matchView (There x) = ?hgnf_1 --Match ?gngfb_0 ?fbfb_0

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

||| Using a final representation (like interfaces) for extensibility.
|||
||| I think it would get confusing or noisy when implementing an interface in
||| terms of another implementation of the same interface. I could use records.
||| I could also use named implementations so that I don't have to use record
||| syntax.
namespace Final
  interface SquareCircle a where
    constructor Blah
    square : Double -> a
    circle : Double -> a

  export
  [area]
  SquareCircle Double where
    square s = s * s
    circle r = 3.14 * r * r

  interface TriangleOnly a where
    triangle : Double -> Double -> a

  export
  [areaTriangleOnly]
  TriangleOnly Double where
    triangle b h = 0.5 * b * h

  export
  printAreas : SquareCircle Double => TriangleOnly Double => IO ()
  printAreas = do
    printLn (the Double $ square 1)
    printLn (the Double $ circle 1)
    printLn (the Double $ triangle 1 1)

namespace AnyShow
  export
  Show (Any f []) where
    show x impossible

namespace AnyShowCons
  export
  [showAnyCons] Show ((the (x -> Type) f) a) => Show (Any f as) => Show (Any f (a :: as)) where
    showPrec d (Here x) = showCon d "Here" $ showArg x
    showPrec d (There x) = showCon d "There" $ showArg x

namespace AnyAsCoproduct
  interface Area a where
    area : a -> Double

  data SquareCircle = Square Double | Circle Double

  Area SquareCircle where
    area (Square dbl) = dbl * dbl
    area (Circle dbl) = 3.14 * dbl * dbl

  record TriangleOnly where
    constructor Triangle
    base : Double
    height : Double

  Area TriangleOnly where
    area triangle = 0.5 * triangle.base * triangle.height

  All Area as => Area (Any Prelude.id as) where
    area @{impl :: _} (Here x) = area x
    area @{_ :: impl} (There x) = area x

  Cast a (Any Prelude.id (a :: _)) where
    cast = Here

  Cast a (Any Prelude.id as) => Cast a (Any Prelude.id (_ :: as)) where
    cast = There . cast

  printArea : Any Prelude.id [SquareCircle, TriangleOnly] -> IO ()
  printArea shape = printLn $ area shape

  export
  printAreas : IO ()
  printAreas = do
    printArea $ cast $ Square 1
    (printArea $ cast $ Circle 1)
    (printArea $ cast $ Triangle 1 1)

  export
  data Lambda rec = Var String | App rec rec | Lam String rec

  %hint
  lamFunctor : Functor Lambda
  lamFunctor = %runElab derive

  export %hint
  lamShow : Show a => Show (Lambda a)
  lamShow = %runElab derive

  export
  data Let rec = MkLet String rec rec

  export %hint
  letFunctor : Functor Let
  letFunctor = %runElab derive

  export %hint
  letShow : Show a => Show (Let a)
  letShow = %runElab derive

  public export
  record AnyF (fs : List (Type -> Type)) (a : Type) where
    constructor MkAnyF
    any : Any ($ a) fs

  Functor (AnyF []) where
    map f (MkAnyF x) impossible

  Functor f => Functor (AnyF fs) => Functor (AnyF (f :: fs)) where
    map f (MkAnyF (Here x)) = MkAnyF $ Here $ map f x
    map f (MkAnyF (There x)) = MkAnyF $ There $ (map f (MkAnyF x)).any

  -- export
  -- [showAny] All (Show . f) as => Show (Any f as) where
  --   showPrec @{impl :: _} d (Here x) = showCon d "Here" $ showArg x
  --   showPrec @{_ :: impl} d (There x) = showCon d "There" $ showArg x

  export
  [showAnyF] Show (Any ($ a) fs) => Show (AnyF fs a) where
    showPrec d x = showCon d "MkAnyF" $ showArg x.any

  injectF : Elem f fs => (f a) -> (AnyF fs a)
  injectF @{Here} x = MkAnyF (Here x)
  injectF @{There i} x = MkAnyF (There (injectF x).any)

  Elem f fs => Cast (f a) (AnyF fs a) where
    cast = injectF

  covering
  data Fix : (Type -> Type) -> Type where
    MkFix : f (Fix f) -> Fix f

  -- https://github.com/vmchale/recursion_schemes/blob/master/Data/Functor/Foldable/Instances.idr#L31
  -- Mu is the least fixed point represented as the catamorphism. I find it
  -- harder to think about, so I don't think I'll use it. Idris accepts it as
  -- total though, unlike Fix.
  total
  data Mu : (Type -> Type) -> Type where
    MuF : ({0 a : Type} -> (f a -> a) -> a) -> Mu f

  export covering
  [showFix] Show (f (Fix f)) => Show (Fix f) where
    showPrec d (MkFix x) = showCon d "MkFix" $ show x

  match : All (\x => f x -> a) xs -> Any f xs -> a
  match (f :: _) (Here x) = f x
  match (_ :: fs) (There x) = match fs x

  Algebra : (Type -> Type) -> (Type -> Type)
  Algebra f a = f a -> a

  covering
  desugarLet' : Algebra (AnyF [Let, Lambda]) (Fix Lambda)
  desugarLet' = MkFix . match [
    \(MkLet v e b) => App (MkFix $ Lam v b) e,
    id
  ] . .any

  covering
  cata : Functor f => Algebra f a -> Fix f -> a
  cata alg (MkFix op) = alg (map (cata alg) op)

  cataMu : Functor f => Algebra f a -> Mu f -> a
  cataMu alg (MuF op) = op alg

  export covering
  injectFix : Elem f fs => Functor f => Fix f -> Fix (AnyF fs)
  injectFix = cata (MkFix . injectF)

  covering
  desugarLet : Fix (AnyF [Let, Lambda]) -> Fix Lambda
  desugarLet = cata desugarLet'

  export
  covering
  example : Fix (AnyF [Let, Lambda])
  example =
    let id : Fix (AnyF [Let, Lambda]) := MkFix (injectF $ Lam "x" (MkFix (injectF $ Var "x")))
        app : Fix (AnyF [Let, Lambda]) := MkFix (injectF $ App (MkFix (injectF $ Var "id")) (MkFix (injectF $ Var "x"))) in
    MkFix (injectF $ Lam "x" (MkFix (cast $ MkLet "id" id app)))

  export
  exampleMu : Mu (AnyF [Let, Lambda])
  exampleMu =
    let MuF id : Mu (AnyF [Let, Lambda]) = MuF $ \elim => elim (injectF $ Lam "x" (elim (injectF $ Var "x")))
        MuF app : Mu (AnyF [Let, Lambda]) = MuF $ \elim => elim (injectF $ App (elim (injectF $ Var "id")) (elim (injectF $ Var "x"))) in
    MuF $ \elim => elim (injectF $ Lam "x" (elim (injectF $ MkLet "id" (id elim) (app elim))))

  covering
  stringifyExpr : Fix (AnyF [Let, Lambda]) -> String
  stringifyExpr = cata (match [
    \(MkLet v e b) => "let \{v} = \{e} in \{b}",
    \case
      Lam v b => "\\\{v} => \{b}"
      App f a => "(\{f})(\{a})"
      Var v => v
  ] . .any)

  stringifyExprMu : Mu (AnyF [Let, Lambda]) -> String
  stringifyExprMu = cataMu (match [
    \(MkLet v e b) => "let \{v} = \{e} in \{b}",
    \case
      Lam v b => "\\\{v} => \{b}"
      App f a => "(\{f})(\{a})"
      Var v => v
  ] . .any)

covering
main : IO ()
main = do
  printAreas @{area} @{areaTriangleOnly}
  AnyAsCoproduct.printAreas
  -- (let
  --   -- _ : (0 a : Type) -> All (\x => Show (x a)) [Let, Lambda] := \a => All.(::) (the (Show (Let a)) letShow) $ All.(::) (the (Show (Lambda a)) lamShow) $ All.Nil
  --   _ = letShow @{showFix}
  --   _ = showAnyCons
  --   _ = showAnyF
  --   _ = showFix in
  --   printLn AnyAsCoproduct.example)
  putStrLn (stringifyExpr AnyAsCoproduct.example)
  putStrLn (stringifyExpr (injectFix (desugarLet AnyAsCoproduct.example)))
  putStrLn (stringifyExprMu AnyAsCoproduct.exampleMu)
