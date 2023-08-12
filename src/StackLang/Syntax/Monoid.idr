module StackLang.Syntax.Monoid

import Control.Algebra
import Control.Function.FunExt
import Data.SnocList
import Data.SnocList.Quantifiers
import Dual.Category
import StackLang.Syntax
import Syntax.WithProof

%default total

{-
I could define an "indexed monoid," but that's basically what a category is.
https://github.com/ekmett/indexed/blob/331b5dd12eee9dfa89d8bf2dda18dce04030167b/src/Indexed/Monoid.hs#L59C6-L59C43
-}

||| Indexed monoid/category for (*->).
StackCat : Category ? (*->)
StackCat = MkCategory {
  id = \a => id,
  compose = (.),
  idComposeLeft = \a, b, f => Refl,
  idComposeRight = \a, b, f => Refl,
  composeAssociative = \a, b, c, d, f, g, h => Refl
}

stackCatFinal : FunExt => Final ? ? StackCat
stackCatFinal = MkFinal {
  top = [<],
  unit = \a => const [<],
  unitUnique = \a => \b => funExt $ \x => case @@(b x) of
    ([<] ** prf) => rewrite prf in Refl
}

stackCatInitial : FunExt => Initial ? ? StackCat
stackCatInitial = MkInitial {
  bottom = [<Void],
  absurd = \a => \case [<x] impossible,
  absurdUnique = \a => \b => funExt $ \case [<x] impossible
}

stackFst : (s' : ?) -> Stack (s ++ s') -> Stack s
stackFst [<] stack = stack
stackFst (s' :< _) (stack :< _) = stackFst s' stack

removeStackBottom : (s : ?) -> Stack ([<a] ++ s) -> Stack s
removeStackBottom [<] stack = [<]
removeStackBottom (s :< b) (stack :< y) = removeStackBottom s stack :< y

removeStackBottomPrf : (ys : ?) -> {0 fx : x} -> {0 gxs : Stack ys} -> removeStackBottom {a = x} ys ([<fx] ++ gxs) === gxs
removeStackBottomPrf [<] {gxs = [<]} = Refl
removeStackBottomPrf (sx :< y) {gxs = (z :< w)} =
  let subprf = removeStackBottomPrf {fx, gxs = z} sx in
  cong (:< w) subprf

stackSnd : (s : ?) -> {s' : ?} -> Stack (s ++ s') -> Stack s'
stackSnd [<] stack = rewrite sym $ appendLinLeftNeutral s' in stack
stackSnd (s :< a) stack =
  let rec = stackSnd {s' = [<a] ++ s'} s (rewrite appendAssociative s [<a] s' in stack) in
  removeStackBottom _ rec

appendLinLeftNeutral : {0 sx : SnocList a} -> (spx : All p sx) -> [<] ++ spx === rewrite appendLinLeftNeutral sx in spx
appendLinLeftNeutral [<] = Refl
appendLinLeftNeutral {sx = sx :< x} (spx :< px) = rewrite appendLinLeftNeutral sx in rewrite appendLinLeftNeutral spx in Refl

appendAssociative : {0 sx, tx, ux : SnocList a} -> (l : All p sx) -> (c : All p tx) -> (r : All p ux) -> l ++ (c ++ r) === rewrite appendAssociative sx tx ux in (l ++ c) ++ r
appendAssociative l c [<] = Refl
appendAssociative {ux = ux :< u} l c (x :< y) = rewrite appendAssociative sx tx ux in rewrite appendAssociative l c x in Refl

stackSndPrf : (sx : ?) -> {ys : ?} -> {0 fxs : Stack sx} -> {0 gxs : Stack ys} -> stackSnd sx (fxs ++ gxs) === gxs
stackSndPrf [<] {fxs = [<]} = rewrite appendLinLeftNeutral gxs in Refl
stackSndPrf (sx' :< x) {fxs = (fxs' :< fx)} =
  let subprf = stackSndPrf {fxs = fxs'} {gxs = [<fx] ++ gxs} sx' in
  rewrite sym $ appendAssociative fxs' [<fx] gxs in
  rewrite subprf in
  removeStackBottomPrf _

-- stackTransport : as === bs -> Stack

removeStackBottomStackSndSnoc :
  {0 fx : a} ->
  (as : ?) ->
  (bs : ?) ->
  {0 fxs : Stack as} ->
  {0 gxs : Stack bs} ->
  gxs === removeStackBottom {a} bs (stackSnd as (fxs ++ ([<fx] ++ gxs))) ->
  ------------------------------
  gxs :< gx === removeStackBottom {a} (bs :< b) (stackSnd as (fxs ++ ([<fx] ++ (gxs :< gx))))
removeStackBottomStackSndSnoc [<] bs prf = cong (:< gx) prf
removeStackBottomStackSndSnoc (sx :< x) [<] {fxs = (fxs :< fx), gxs = [<]} prf =
  let subprf := removeStackBottomStackSndSnoc {fxs, gxs = [<]} sx [<] prf in
  ?fgdbfdf_2
removeStackBottomStackSndSnoc {fxs = (fxs :< fx'){-, gxs = gxs :< gx'-}}  (sx :< x) (bs :< b') prf =
  -- let
  --   -- prf' := {-rewrite sym $ stackSndPrf sx in -}rewrite sym $ appendAssociative fxs [<fx'] ([<fx] ++ gxs) in prf
  --   subprf := removeStackBottomStackSndSnoc {fxs, gxs} sx bs
  --     ({-rewrite stackSndPrf sx in-} ?dbddf)
  -- in
  -- rewrite appendAssociative fxs ([<fx'] ++ ([<fx] ++ gxs)) [<gx] in
    ?fgdbfdf_1

-- appendLinLeftNeutral2 : {0 sx : SnocList a} -> (spx : All p sx) -> rewrite appendLinLeftNeutral sx in (===))[<] ++ spx === spx)
-- appendLinLeftNeutral2 [<] = Refl
-- appendLinLeftNeutral2 {sx = sx :< x} (spx :< px) = rewrite appendLinLeftNeutral sx in rewrite appendLinLeftNeutral spx in Refl

top : Stack (xs :< x) -> x
top (_ :< a) = a

drop : Stack (xs :< x) -> Stack xs
drop (as :< _) = as

stackProductCommute : FunExt => {a, b : ?} -> (c : SnocList Type) -> (f : (All Prelude.id c -> All Prelude.id a)) -> (g : (All Prelude.id c -> All Prelude.id b)) -> (f = (\x => stackFst b (f x ++ g x)), g = (\x => stackSnd a (f x ++ g x)))
stackProductCommute {a = [<]} {b = [<]} c f g =
  (
    funExt $ \x => case @@(g x) of ([<] ** prf) => rewrite prf in Refl,
    funExt $ \x => case @@(f x) of ([<] ** prf) => rewrite prf in case @@(g x) of ([<] ** prf) => rewrite prf in Refl
  )
stackProductCommute {a = as :< a} {b = [<]} c f g =
  (
    funExt $ \x => case @@(g x) of
      ([<] ** prf) => rewrite prf in Refl,
    funExt $ \x => case @@(g x) of ([<] ** prf) => rewrite prf in Refl
  )
stackProductCommute {a = [<]} {b = bs :< b} c f g =
  (
    funExt $ \x =>
      case @@(g x) of
        ((xs :< _) ** prf) =>
          rewrite prf in
          -- NOTE: Easier to typecheck if we get the subproof using the info
          -- just revealed about `g x`.
          let subprf := stackProductCommute c f (\x => xs)
              subprf1 : f x === stackFst bs (f x ++ xs)
              subprf1 := cong ($ x) (fst subprf) in
              subprf1,
    funExt $ \x =>
      case @@(f x) of
        ([<] ** prf) =>
          rewrite prf in
          -- sym $ appendLinLeftNeutral {sx = bs :< b} ?h4
          ?h4
  )
stackProductCommute {a = as :< a} {b = bs :< b} c f g =
  (
    funExt $ \x =>
      case @@(g x) of
        ((xs :< _) ** prf) =>
          rewrite prf in
          let subprf := stackProductCommute c f (\x => xs) in
          let subprf1 : f x === stackFst bs (f x ++ xs)
              subprf1 := cong ($ x) (fst subprf) in
              subprf1,
    funExt $ \x =>
      case (@@(f x), @@(g x)) of
        (((fxs :< fx) ** fprf), ((gxs :< gx) ** gprf)) =>
          rewrite fprf in
          rewrite gprf in
          let subprf := cong ($ x) $ snd $ stackProductCommute c (\x => fxs :< fx) (\x => gxs) in
          ?h42
  )

stackProductUnique : FunExt => (b, a : SnocList Type) -> (f : (Stack c -> Stack (a ++ b))) -> (g : Stack c) -> stackFst {s = a} b (f g) ++ stackSnd {s' = b} a (f g) === f g
stackProductUnique [<] [<] f g with (f g)
  _ | [<] = Refl
stackProductUnique [<] (sx :< x) f g = Refl
stackProductUnique (sx :< x) [<] f g with (stackFst (sx :< x) (f g)) | (f g)
  _ | [<] | (fgs :< fg) = let subprf = stackProductUnique sx [<] (drop . f) g in rewrite appendLinLeftNeutral fgs in rewrite appendLinLeftNeutral sx in ?xgfdf
stackProductUnique (sx :< x) (sy :< y) f g = ?fhfd_3

stackCatProduct : FunExt => (a, b : ?) -> Product ? ? StackCat a b
stackCatProduct a b = MkProduct {
  product = a ++ b,
  pi = \p => stackFst b p,
  pi' = \p => stackSnd _ p,
  arrowProduct = \gamma, f1, f2 => \g => f1 g ++ f2 g,
  diagramCommutes = stackProductCommute,
  arrowProductUnique = \c, f => funExt $ \g => stackProductUnique b a f g
}
