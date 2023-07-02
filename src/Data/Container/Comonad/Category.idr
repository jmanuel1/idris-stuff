module Data.Container.Comonad.Category

import Control.Function.FunExt
import Data.Container
import Dual.Category
import Dual.Category.Idris
import Data.Morphisms

%default total

map : c `Morphism` d -> M c -> M d
map f@(MkMorphism shapeMorphism positionMorphism) (MkM (MkExtension shape payloads)) = MkM (MkExtension (shapeMorphism shape) (\pos => map f (payloads (positionMorphism pos))))

implicitfy : {0 b : a -> Type} -> ((x : a) -> b x) -> ({x' : a} -> b x')
implicitfy f {x'} = f x'

mkMorphism : {0 c : Container} -> {0 d : Container} -> (shapeMorphism : (Shape c -> Shape d)) -> ((s : Shape c) -> Position d (shapeMorphism s) -> Position c s) -> Morphism c d
mkMorphism shapeMorphism positionMorphism = MkMorphism shapeMorphism $ \pos => positionMorphism _ pos

Prelude.Functor (Cofree container) where
  -- https://hackage.haskell.org/package/comonad-5.0.8/docs/Control-Comonad.html#t:Comonad
  -- map f = extend (f . extract)
  map f (MkCofree (MkM c)) =
    let (c1, c2) = fromPair c in
    let c1' = toConst (f (fromConst c1)) in
    let c2' : Extension container (Inf (M (Pair (Const ?) container)))
      -- NOTE: Use `mkMorphism` to make the shape parameter to the position
      -- morphism explicit so that type checker will accept the position
      -- morphism. Match on the shape `(p, q)` to eliminate the `let` in the
      -- goal.
      = map (\m => map (mkMorphism (\x => (f (fst x), snd x)) $ \(p, q), pos => pos) m) c2 in
    MkCofree $ MkM $ toPair (c1', c2')

{-
cofreeIsFunctor : FunExt => Functor IdrisCat IdrisCat (Cofree c)
cofreeIsFunctor = MkFunctor {
  fmap = \a, b, (Mor f) => Mor (map f),
  identity = \a => cong Mor (funExt $ \(MkCofree (MkM (MkExtension s p))) => ?hole3),--cong MkCofree (cong MkM (cong (MkExtension s) ?hole1))),
  composition = \a, b, c, (Mor f), (Mor g) => cong Mor (funExt $ \(MkCofree (MkM (MkExtension ms mp))) => ?hole4)
}
