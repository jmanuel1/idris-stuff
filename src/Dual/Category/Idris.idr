module Dual.Category.Idris

import Control.Function
import Control.Function.FunExt
-- import Data.Container
import Data.Description.Regular
import Data.Late
import Data.List
import Data.Morphisms
import Dual.Category

%default total

public export
IdrisCat : Category Type (~>)
IdrisCat = MkCategory {
  id = \_ => Mor id,
  compose = \(Mor f), (Mor g) => Mor (f . g),
  idComposeRight = \a, b, (Mor f) => Refl,
  idComposeLeft = \a, b, (Mor f) => Refl,
  composeAssociative = \a, b, c, d, (Mor f), (Mor g), (Mor h) =>
    Refl
}

export
etaPair : (p : (a, b)) -> (fst p, snd p) === p
etaPair (a, b) = Refl

idrisProduct : FunExt => (a, b : Type) -> Product Type (~>) IdrisCat a b
idrisProduct a b = MkProduct {
  product = (a, b),
  pi = Mor fst,
  pi' = Mor snd,
  arrowProduct = \_, (Mor f), (Mor g) => Mor (\x => (f x, g x)),
  diagramCommutes = \_, (Mor f), (Mor g) => (Refl, Refl),
  arrowProductUnique = \c, (Mor g) =>
    cong Mor (funExt $ \x => etaPair (g x))
}

idrisExponential : FunExt => (b, a : Type) -> Exponential Type (~>) IdrisCat b a
idrisExponential b a = MkExponential {
  exp = a -> b,
  productARight = \o => idrisProduct o a,
  eval = Mor (\x => fst x (snd x)),
  curry = \_, (Mor f) => Mor (\x, y => f (x, y)),
  diagramCommutes = \_, (Mor f) => cong Mor (funExt $ \x => cong f (etaPair x)),
  curryUnique = \_, (Mor _) => Refl
}

idrisCartesian : FunExt => Cartesian Type (~>) IdrisCat
idrisCartesian = MkCartesian {finiteProduct = idrisProduct}

idrisCartesianClosed : FunExt => CartesianClosed Type (~>) IdrisCat
idrisCartesianClosed = MkCartesianClosed {cartesian = idrisCartesian, exponential = idrisExponential}

{- Show that Idris has coproducts. -}

idrisCoproduct : FunExt => (a, b : Type) -> Coproduct Type (~>) IdrisCat a b
idrisCoproduct a b = MkProduct {
  product = Either a b,
  pi = Mor Left,
  pi' = Mor Right,
  arrowProduct = \_, (Mor f), (Mor g) => Mor $ either f g,
  diagramCommutes = \_, (Mor f), (Mor g) => (Refl, Refl),
  arrowProductUnique = \_, (Mor g) =>
    cong Mor (funExt $ \x => case x of
      Left x => Refl
      Right x => Refl)
}

{- List is a functor. -}

mapId : (xs : List a) -> map Prelude.id xs === xs
mapId [] = Refl
mapId (x :: xs) = cong (x ::) $ mapId xs

listFunctor : FunExt => Functor IdrisCat IdrisCat List
listFunctor = MkFunctor {
  fmap = \_, _, (Mor f) => Mor (map f),
  identity = \a => cong Mor (funExt mapId),
  composition = \a, b, c, (Mor f), (Mor g) => cong Mor (funExt $ \xs => sym $ mapFusion f g xs)
}

-- containerFunctor : FunExt => Functor IdrisCat IdrisCat (Extension c)
-- containerFunctor = MkFunctor {
--   fmap = \_, _, (Mor f) => Mor (map f),
--   identity = \a => cong Mor (funExt $ \(MkExtension s p) => Refl),
--   composition = \a, b, c, (Mor f), (Mor g) => cong Mor (funExt $ \(MkExtension s p) => Refl)
-- }

mapDesc : (d : Desc p) -> (a -> b) -> (x : Elem d a) -> Elem d b
mapDesc Zero f x = x
mapDesc One f x = x
mapDesc Id f x = f x
mapDesc (Const s prop) f x = x
mapDesc (d1 * d2) f x = (mapDesc d1 f (fst x), mapDesc d2 f (snd x))
mapDesc (d1 + d2) f (Left x) = Left (mapDesc d1 f x)
mapDesc (d1 + d2) f (Right x) = Right (mapDesc d2 f x)

mapDescId : (d : Desc p) -> (x : Elem d a) -> mapDesc {a, b = a} d Prelude.id x === x
mapDescId Zero _ = Refl
mapDescId One _ = Refl
mapDescId Id _ = Refl
mapDescId (Const s prop) _ = Refl
mapDescId (d1 * d2) (x, y) =
  let fstPrf = mapDescId d1 x
      sndPrf = mapDescId d2 y in
  cong2 (,) fstPrf sndPrf
mapDescId (d1 + d2) (Left x) = cong Left (mapDescId d1 x)
mapDescId (d1 + d2) (Right x) = cong Right (mapDescId d2 x)

mapDescCompose : (d : Desc p) -> (f : (b -> c)) -> (g : (a -> b)) -> (x : Elem d a) -> mapDesc d (\x => f (g x)) x === mapDesc d f (mapDesc d g x)
mapDescCompose Zero f g _ = Refl
mapDescCompose One f g _ = Refl
mapDescCompose Id f g _ = Refl
mapDescCompose (Const s prop) f g _ = Refl
mapDescCompose (d1 * d2) f g x = cong2 (,) (mapDescCompose d1 f g (fst x)) (mapDescCompose d2 f g (snd x))
mapDescCompose (d1 + d2) f g (Left x) = cong Left (mapDescCompose d1 f g x)
mapDescCompose (d1 + d2) f g (Right x) = cong Right (mapDescCompose d2 f g x)

descFunctor : FunExt => (d : Desc p) -> Functor IdrisCat IdrisCat (Elem d)
descFunctor d = MkFunctor {
  fmap = \_, _, (Mor f) => Mor (mapDesc d f),
  identity = \a => cong Mor (funExt $ \x => mapDescId d x),
  composition = \a, b, c, (Mor f), (Mor g) => cong Mor (funExt $ mapDescCompose d f g)
}

data Interp :  Desc p -> Type -> Type where
  -- Zero should be uninhabited
  IOne : Interp One a -- Unit type
  IId : a -> Interp Id a
  IConst : {auto 0 prop : p b} -> b -> Interp (Const {p} b prop) a
  IProd : Interp d1 a -> Interp d2 a -> Interp (d1 * d2) a
  ILeft : Interp d a -> Interp (d + _) a
  IRight : Interp d a -> Interp (_ + d) a

mapInterp : (d : Desc p) -> (a -> b) -> (x : Interp d a) -> Interp d b
mapInterp Zero f x impossible
mapInterp One f x = IOne
mapInterp Id f (IId x) = IId $ f x
mapInterp (Const s prop) f (IConst x) = IConst x
mapInterp (d1 * d2) f (IProd x1 x2) = IProd (mapInterp d1 f x1) (mapInterp d2 f x2)
mapInterp (d1 + d2) f (ILeft x) = ILeft (mapInterp d1 f x)
mapInterp (d1 + d2) f (IRight x) = IRight (mapInterp d2 f x)

data GFix : Desc p -> Type where
  MkGFix : Interp d (Late (GFix d)) -> GFix d

%hide Data.Late.unfold

{-
unfold : (d : Desc p) -> (s -> Interp d s) -> s -> Late (GFix d)
unfold Zero next seed = case next seed of {}
unfold One next seed = pure $ MkGFix IOne
unfold Id next seed =
  let IId seed' = next seed in
  Later (unfold Id next seed')
unfold (Const x prop) next seed =
  case next seed of
    IConst val => pure $ MkGFix (IConst val)
unfold (d1 * d2) next seed =
  case next seed of
    IProd seed1 seed2 => pure $ MkGFix (IProd (mapInterp d1 (\s => Later $ unfold (d1 * d2) next s) seed1) ?fbf)
unfold (d1 + d2) next seed = ?fbfdndn_5
  -- let seed' = next seed in
  -- MkGFix ?fbdfb
--   let (I seed') = next seed in
--   MkGFix (I (case d of
--                   Zero => seed'
--                   One => seed'
--                   Id => unfold Id next seed'
--                   (Const x prop) => seed'
--                   (d1 * d2) => (mapDesc {b = Inf _} d1 (\s => unfold d next s) (fst seed'), ?dfbd)
--                   (d1 + d2) => ?fgbdfbdf_5))

data Cofree : Desc p -> Type -> Type where
  -- `Interp` is used to avoid using `assert_total`. An explanation of why is at
  -- https://github.com/idris-lang/Idris2/blob/ecf4765c4beab2656d57ba4982f42427a40bc016/libs/papers/Data/Description/Regular.idr#L58.
  MkCofree : a -> Interp d (Inf (Cofree d a)) -> Cofree d a

  {-
forceInf : Inf a -> a
forceInf a = a

delayInf : a -> Inf a
delayInf a = Delay a

cofreeMapDelayed : (d : Desc p) -> (a -> b) -> Inf (Cofree d a) -> Inf (Cofree d b)
cofreeMapDelayed d f (MkCofree a fa) = MkCofree (f a) (mapDesc {a = Inf (Cofree d _), b = Inf (Cofree d _)} d (\x => cofreeMapDelayed d f x) fa)
-}


-- {d : Desc p} -> Prelude.Functor (Cofree d) where
--   map f (MkCofree a (I fa)) = MkCofree (f a) (I $ mapDesc {a = Inf (Cofree d _), b = Inf (Cofree d _)} d (\ca => map {f = Cofree d} f ca) fa)

-- cofreeMap : (x -> y) -> M (Pair (Const x) c) -> M (Pair (Const y) c)
-- cofreeMap f m@(MkM e@(MkExtension ms mp)) = MkM (map (\blah => ?fhole) e){-(MkExtension (f (fst ms), snd ms) $ \case
  -- Left v => absurd v
  -- Right pos => cofreeMap f m)--MkM (MkExtension ?fhole ?hole2))

-- cofreeMap' : (a -> b) -> Cofree c a -> Cofree c b
-- cofreeMap' f (MkCofree cf) = MkCofree $ cofreeMap f cf


{-
cofreeIsComonad : Functor IdrisCat IdrisCat f -> Comonad IdrisCat (Cofree f)
-- cofreeIsComonad functor = MkComonad {
--
-- }
