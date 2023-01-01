-- https://reader.elsevier.com/reader/sd/pii/S0304397599001243?token=6A5B6AEC40426B281C073440D460D2A4D378BECDF962D5A4C74FBD12D0BF59918A3D2006BB5B3E7CF1E1A1BCD845F0F7&originRegion=eu-west-1&originCreation=20221224221200
-- https://www.reddit.com/r/haskell/comments/qwklh/coexponentials/
module Dual.Computation

import Control.Function
import Data.Morphisms
import Deriving.Functor
import Dual.Category
import Syntax.WithProof

%default total
%language ElabReflection

record Cont r a where
  constructor MkCont
  runCont : ((a -> r) -> r)

%hint
contFunctor : Functor (Cont r)
contFunctor = %runElab derive

Applicative (Cont r) where
  pure a = MkCont $ \k => k a
  (<*>) (MkCont f) (MkCont a) = MkCont $ \k => f $ \f' => a $ \a' => k (f' a')

Monad (Cont r) where
  (MkCont fa) >>= f = MkCont $ \k => fa $ \fa' => case f fa' of MkCont ffa => ffa k
  join (MkCont ffa) = MkCont (\k => ffa $ \(MkCont fa) => fa k)

-- MkCont (\k => let MkCont fa = f x in fa k) = f x
-- MkCont (let fa = runCont $ f x in fa) = f x
etaCont : (cont : Cont r a) -> MkCont (\k => let MkCont c = cont in c k) === cont
etaCont (MkCont _) = Refl

KleisliCont : Type -> Type -> Type -> Type
KleisliCont r = Kleislimorphism (Cont r)

-- Object :

-- introduction rule
-- A |- (A - B) \/ B

data Coexp r a b = MkCoexp a (b -> r)

coeval : KleisliCont r a (Either (Coexp r a b) b)
coeval = Kleisli $ \x => MkCont $ \k => k (Left (MkCoexp x $ \y => k (Right y)))

-- elimination rule (kinda?)
cocurry : KleisliCont r b (Either a c) -> KleisliCont r (Coexp r b a) c
cocurry (Kleisli f) = Kleisli $ \(MkCoexp y err) => MkCont $ \k => runCont (f y) (either err k)

example : Nat
example =
  let ex = cocurry coeval in runCont (ex.applyKleisli (MkCoexp (6 * 9) $ \(MkCoexp a bCont) => bCont (a + 42))) id

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

-- internal POSTULATE: function extensionality.
funExt : {0 f, g : t -> t'} -> ((x : t) -> f x === g x) -> f === g
funExt _ = believe_me (Refl {a = t -> t', x = f})

idrisProduct : (a, b : Type) -> Product Type (~>) IdrisCat a b
idrisProduct a b = MkProduct {
  product = (a, b),
  pi = Mor fst,
  pi' = Mor snd,
  arrowProduct = \_, (Mor f), (Mor g) => Mor (\x => (f x, g x)),
  diagramCommutes = \_, (Mor f), (Mor g) => (Refl, Refl),
  arrowProductUnique = \c, (Mor g) =>
    cong Mor (funExt $ \x => etaPair (g x))
}

idrisExponential : (b, a : Type) -> Exponential Type (~>) IdrisCat b a
idrisExponential b a = MkExponential {
  exp = a -> b,
  productARight = \o => idrisProduct o a,
  eval = Mor (\x => fst x (snd x)),
  curry = \_, (Mor f) => Mor (\x, y => f (x, y)),
  diagramCommutes = \_, (Mor f) => cong Mor (funExt $ \x => cong f (etaPair x)),
  curryUnique = \_, (Mor _) => Refl
}

idrisCartesian : Cartesian Type (~>) IdrisCat
idrisCartesian = MkCartesian {finiteProduct = idrisProduct}

idrisCartesianClosed : CartesianClosed Type (~>) IdrisCat
idrisCartesianClosed = MkCartesianClosed {cartesian = idrisCartesian, exponential = idrisExponential}

{- Show that Idris has coproducts. -}

idrisCoproduct : (a, b : Type) -> Coproduct Type (~>) IdrisCat a b
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

simpleFunEta : (0 expr : Cont r a) -> (k : a -> r) -> Equal {a = r, b = r} (let MkCont x = expr in x k) ((the ((a -> r) -> r) (let MkCont x = expr in x)) k)
simpleFunEta (MkCont c) k = Refl

unwrapCont : Cont r a -> (a -> r) -> r
unwrapCont (MkCont c) = c

Injective Computation.unwrapCont where
  injective {x = MkCont c} {y = MkCont c} Refl = Refl

letEq : {0 r, a : Type} -> (c : Cont r a) -> (k : a -> r) -> Equal {a=r, b=r} (let MkCont x = c in x k) (let MkCont fa = c in fa k)
letEq (MkCont c') k = Refl

ContKleisliTriple : KleisliTriple IdrisCat (Cont r)
ContKleisliTriple = MkTriple {
  pure = \_ => Mor pure,
  extend = \_, _, (Mor f) => Mor (>>= f),
  extendPureIsId = \_ => cong Mor (funExt $ \(MkCont arg) => cong MkCont (funExt $ \_ => Refl)),
  pureComposeRight = \_, _, (Mor f) => cong Mor (funExt $ \x => rewrite sym (etaCont (f x)) in Refl),
  extendCompose = \_, _, _, (Mor f), (Mor g) =>
    cong Mor (funExt $ \(MkCont arg) =>
      cong MkCont (funExt $ \k =>
        cong arg (funExt $ \fa' =>
          rewrite sym (etaCont (f fa')) in
            case @@(f fa') of
              (MkCont c ** prf) => rewrite prf in cong c (funExt $ \fa' =>
                case @@(g fa') of
                  (MkCont _ ** prf) => rewrite prf in Refl))))
}

KleisliContCat : {r : _} -> KleisliCategory IdrisCat (ContKleisliTriple {r})
KleisliContCat = mkKleisliCategory IdrisCat ContKleisliTriple

kleisliContCoproduct : (r, a, b : Type) -> Coproduct Type _ (KleisliContCat {r}) a b
kleisliContCoproduct r a b = MkProduct {
  product = Either a b,
  pi = Mor (pure . Left),
  pi' = Mor (pure . Right),
  arrowProduct = \_, (Mor f), (Mor g) => Mor $ \x => case x of
    Left x => f x
    Right x => g x,
  diagramCommutes = \c, (Mor f), (Mor g) => let dc = (idrisCoproduct a b).diagramCommutes (Cont r c) (Mor f) (Mor g) in (cong Mor (funExt $ \x => rewrite sym (etaCont (f x)) in cong MkCont (funExt $ \k => case @@(f x) of (MkCont fx ** prf) => {-rewrite prf in-} ?hole)), cong Mor ?hole'), --(cong Mor (funExt $ \x => case @@(f x) of (MkCont fx ** prf) => rewrite prf in cong MkCont (funExt $ \k => ?h1)), ?h2),
  arrowProductUnique = ?h3 {-\_, (Mor g) =>
    cong Mor (funExt $ \x => case x of
      Left x => Refl
      Right x => Refl)-}
}
