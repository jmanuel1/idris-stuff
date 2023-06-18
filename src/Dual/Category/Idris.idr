module Dual.Category.Idris

import Control.Function
import Control.Function.FunExt
import Data.Container
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

containerFunctor : FunExt => Functor IdrisCat IdrisCat (Extension c)
containerFunctor = MkFunctor {
  fmap = \_, _, (Mor f) => Mor (map f),
  identity = \a => cong Mor (funExt $ \(MkExtension s p) => Refl),
  composition = \a, b, c, (Mor f), (Mor g) => cong Mor (funExt $ \(MkExtension s p) => Refl)
}
