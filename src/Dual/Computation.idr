-- https://reader.elsevier.com/reader/sd/pii/S0304397599001243?token=6A5B6AEC40426B281C073440D460D2A4D378BECDF962D5A4C74FBD12D0BF59918A3D2006BB5B3E7CF1E1A1BCD845F0F7&originRegion=eu-west-1&originCreation=20221224221200
-- https://www.reddit.com/r/haskell/comments/qwklh/coexponentials/
module Dual.Computation

import Control.Function
import Control.Function.FunExt
import Data.Morphisms
import Deriving.Functor
import Dual.Category
import Syntax.WithProof

%default total
%language ElabReflection

namespace Cont
  public export
  Cont : Type -> Type -> Type
  Cont r a = ((a -> r) -> r)

  public export
  runCont : Cont r a -> (a -> r) -> r
  runCont = id

  public export
  map : (a -> b) -> Cont r a -> Cont r b
  map f cont = \k => cont (k . f)

  public export
  pure : a -> Cont r a
  pure a = \k => k a

  public export
  (>>=) : Cont r a -> (a -> Cont r b) -> Cont r b
  fa >>= f = \k => fa $ \fa' => (f fa') k

  public export
  KleisliCont : Type -> Type -> Type -> Type
  KleisliCont r = Kleislimorphism (Cont r)

-- Object :

-- introduction rule
-- A |- (A - B) \/ B

data Coexp r a b = MkCoexp a (b -> r)

coeval : KleisliCont r a (Either (Coexp r a b) b)
coeval = Kleisli $ \x => \k => k (Left (MkCoexp x $ \y => k (Right y)))

-- elimination rule (kinda?)
cocurry : KleisliCont r b (Either c a) -> KleisliCont r (Coexp r b a) c
cocurry (Kleisli f) = Kleisli $ \(MkCoexp y err) => \k => runCont (f y) (either k err)

example : Nat
example =
  let ex = cocurry coeval in ex.applyKleisli (MkCoexp (the Nat 6 * 9) $ \y => y) $ \(MkCoexp x k) => k x

{- The Kleisli category of the continuation monad is cocartesian coclosed if the
underlying category is cartesian closed and has coproducts. So, let's show that
Idris (the non-dependent fragment) is cartesian closed first. -}

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

{- Now, to show that the Kleisli category of the continuation monad is
cocartesian coclosed. -}

ContKleisliTriple : FunExt => KleisliTriple IdrisCat (Cont r)
ContKleisliTriple = MkTriple {
  pure = \_ => Mor pure,
  extend = \_, _, (Mor f) => Mor (>>= f),
  extendPureIsId = \_ => Refl,
  pureComposeRight = \_, _, (Mor _) => Refl,
  extendCompose = \_, _, _, (Mor _), (Mor _) => Refl
}

KleisliContCat : FunExt => {r : _} -> KleisliCategory IdrisCat (ContKleisliTriple {r})
KleisliContCat = mkKleisliCategory IdrisCat ContKleisliTriple

kleisliContCoproduct : FunExt => {0 r : Type} -> (a, b : Type) -> Coproduct Type _ (KleisliContCat {r}) a b
kleisliContCoproduct a b = MkProduct {
  product = Either a b,
  pi = Mor (pure . Left),
  pi' = Mor (pure . Right),
  arrowProduct = \_, (Mor f), (Mor g) => Mor $ \x => case x of
    Left x => f x
    Right x => g x,
  diagramCommutes = \_, (Mor _), (Mor _) => (Refl, Refl),
  arrowProductUnique = \_, (Mor _) =>
    cong Mor (funExt $ \x => case x of
      Left _ => Refl
      Right _ => Refl)
}
