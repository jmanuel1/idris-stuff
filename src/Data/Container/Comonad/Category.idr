module Data.Container.Comonad.Category

import Control.Function.FunExt
import Data.Container
import Data.Container.Combinators
import Dual.Category
import Dual.Category.Idris
import Data.Morphisms
import Syntax.WithProof

%default total

map : c `Morphism` d -> M c -> M d
map f@(MkMorphism shapeMorphism positionMorphism) (MkM (MkExtension shape payloads)) = MkM (MkExtension (shapeMorphism shape) (\pos => map f (payloads (positionMorphism pos))))

implicitfy : {0 b : a -> Type} -> ((x : a) -> b x) -> ({x' : a} -> b x')
implicitfy f {x'} = f x'

record PosMor (c, d : Container) (shapeMorphism : (Shape c -> Shape d)) where
  constructor MkPM
  unPM : {s : c .Shape} -> d .Position (shapeMorphism s) -> c .Position s

mkPosMor' : (shapeMorphism_0 : (c .Shape -> d .Shape)) -> ((s : c .Shape) -> d .Position (shapeMorphism_0 s) -> c .Position s) -> ({s : c .Shape} -> d .Position (shapeMorphism_0 s) -> c .Position s)
mkPosMor' sm ps {s} = ps s

mkPosMor : (shapeMorphism_0 : (c .Shape -> d .Shape)) -> ((s : c .Shape) -> d .Position (shapeMorphism_0 s) -> c .Position s) -> PosMor c d shapeMorphism_0
mkPosMor sm ps = MkPM (mkPosMor' sm ps)

mkMorphism : {0 c : Container} -> {0 d : Container} -> (shapeMorphism : (Shape c -> Shape d)) -> ((s : Shape c) -> Position d (shapeMorphism s) -> Position c s) -> Morphism c d
mkMorphism shapeMorphism positionMorphism = MkMorphism shapeMorphism $ (mkPosMor shapeMorphism positionMorphism).unPM

blah : (s : (a, container.Shape)) -> Either Void (container .Position (snd s)) -> let (p, q) = s
                                                   in Either (Position (MkContainer a (\value => Void)) p) (Position container q)
blah _ (Left void) = absurd void
blah (p, q) (Right pos) = Right pos

delayInf : a -> Inf a
delayInf x = Delay x

{-
\case
  Left void => absurd void
  -- `s` is from https://github.com/idris-lang/Idris2/blob/main/libs/papers/Data/Container.idr#L48 I believe
  Right pos => Left ?h2 implicitfy $ \s => h1 {a, container, s} pos h1 {container}
-}

Prelude.Functor (Cofree container) where
  -- https://hackage.haskell.org/package/comonad-5.0.8/docs/Control-Comonad.html#t:Comonad
  -- map f = extend (f . extract)
  map f (MkCofree (MkM c)) =
    MkCofree $ MkM $ toPair (
      -- map f (fst (fromPair c)),
      -- case fst (fromPair c) of
      --   MkExtension {c = c'} s p => ?fndfbd {-MkExtension ?gbfc ?dfbdp-},
      toConst (f (fromConst (fst (fromPair c)))),
      -- NOTE: Use `mkMorphism` to make the shape parameter to the position
      -- morphism explicit so that type checker will accept the position
      -- morphism. Match on the shape `(p, q)` to eliminate the `let` binding
      -- of the shape in the goal.
      map (\m => map (mkMorphism (\x => (f (fst x), snd x)) $ \(_, _) => id) m) $ snd (fromPair c))


-- hole3 : FunExt => {0 a : Type} -> (c : Extension (MkContainer (a, container .Shape) (\lamc => let (p, q) = lamc in Either (Position (MkContainer a (\value => Void)) p) (Position container q))) (Inf (M (MkContainer (a, container .Shape) (\lamc => let (p, q) = lamc in Either (Position (MkContainer a (\value => Void)) p) (Position container q)))))) -> let (c1, c2) = fromPair c in let c1' = toConst (id (fromConst c1)) in let c2' = map (\m => (Delay (map (mkMorphism (\x => (id (fst x), snd x)) (\lamc => let (p, q) = lamc in \pos => pos)) (Force m)))) c2 in MkCofree (MkM (toPair (c1', c2'))) = MkCofree (MkM c)

etaPairExt : FunExt => (\x => (Builtin.fst x, Builtin.snd x)) === Prelude.id
etaPairExt = funExt $ \x => etaPair x

cofreeIsFunctor : FunExt => Functor IdrisCat IdrisCat (Cofree container)
cofreeIsFunctor = MkFunctor {
  fmap = \a, b, (Mor f) => Mor (map f),
  identity = \a => cong Mor (funExt $ \(MkCofree (MkM c)) =>
    cong (MkCofree . MkM) $
    -- rewrite constRoundTrip (fst (fromPair c)) in
    -- replace {p = \x => MkCofree (MkM (toPair (x, map (\m => map (mkMorphism (\x => ((fst x), snd x)) $ \(_, _) => id) m) $ snd (fromPair c)))) === MkCofree (MkM c)} {- ?hole5-} (sym $ constRoundTrip (fst (fromPair c))) $
    -- case constRoundTrip (fst (fromPair c)) of
    --   Refl =>
    -- rewrite pairRoundTrip c in
    -- rewrite etaPairExt in
    -- the (toPair (fst (fromPair c), _) === _) $
    ?hole3),--cong MkCofree (cong MkM (cong (MkExtension s) ?hole1))),
  composition = \a, b, c, (Mor f), (Mor g) => cong Mor (funExt $ \(MkCofree (MkM (MkExtension ms mp))) => ?hole4)
}
