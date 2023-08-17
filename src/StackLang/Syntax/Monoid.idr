module StackLang.Syntax.Monoid

import Control.Algebra
import Control.Function.FunExt
import Control.Relation
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

removeStackBottom : (s : ?) -> Stack ([<a] ++ s) -> Stack s
removeStackBottom [<] stack = [<]
removeStackBottom (s :< b) (stack :< y) = removeStackBottom s stack :< y

removeStackBottomPrf : (ys : ?) -> {0 fx : x} -> {0 gxs : Stack ys} -> removeStackBottom {a = x} ys ([<fx] ++ gxs) === gxs
removeStackBottomPrf [<] {gxs = [<]} = Refl
removeStackBottomPrf (sx :< y) {gxs = (z :< w)} =
  let subprf = removeStackBottomPrf {fx, gxs = z} sx in
  cong (:< w) subprf

appendLinLeftNeutral : {0 sx : SnocList a} -> (spx : All p sx) -> [<] ++ spx === rewrite appendLinLeftNeutral sx in spx
appendLinLeftNeutral [<] = Refl
appendLinLeftNeutral {sx = sx :< x} (spx :< px) = rewrite appendLinLeftNeutral sx in rewrite appendLinLeftNeutral spx in Refl

appendAssociative : {0 sx, tx, ux : SnocList a} -> (l : All p sx) -> (c : All p tx) -> (r : All p ux) -> l ++ (c ++ r) === rewrite appendAssociative sx tx ux in (l ++ c) ++ r
appendAssociative l c [<] = Refl
appendAssociative {ux = ux :< u} l c (x :< y) = rewrite appendAssociative sx tx ux in rewrite appendAssociative l c x in Refl

-------------------------------------------------------------------------------

data Heq : (0 a : Type) -> (0 p : a -> Type) -> (l : (x : a ** p x)) -> (r : (y : a ** p y)) -> Type where
  HRefl : Heq a p l l

Symmetric (z : a ** p z) (Heq a p) where
  symmetric HRefl = HRefl

heqToEq : (0 _ : Heq a p l r) -> l = r
heqToEq HRefl = Refl

heqRewrite : (0 goal : p y -> Type) -> (0 heq : Heq a p (x ** px) (y ** py)) -> goal py -> goal (case heq of HRefl => px)
heqRewrite goalfn HRefl goal = goal

heqfromIndexRewrite : (0 p : a -> Type) -> (0 indexEq : y = x) -> (0 px : p x) -> Heq a p (x ** px) (y ** rewrite indexEq in px)
heqfromIndexRewrite _ Refl px = HRefl

-------------------------------------------------------------------------------

-- I'd like to have just `(xs : _) -> All p xs` here, but then Idris struggles
-- with accepting pattern matching on values of type `Split (xs ++ ys) _`.
data Split : (0 xs, ys : SnocList a) -> All p (xs ++ ys) -> Type where
  MkSplit : (0 xs, ys : SnocList a) -> (pxs : All p xs) -> (pys : All p ys) -> Split xs ys (pxs ++ pys)

(:<) : {0 p : a -> Type} -> {pxs : All p (xs ++ ys)} -> {x : a} -> Split xs ys pxs -> (px : p x) -> Split xs (ys :< x) (pxs :< px)
(MkSplit sx ys psx pys) :< px = MkSplit sx (ys :< x) psx (pys :< px)

split : (0 xs : SnocList a) -> (ys : SnocList a) -> (pxys : All p (xs ++ ys)) -> Split xs ys pxys
split xs [<] pxys = MkSplit xs [<] pxys [<]
split xs (sx :< x) (pxys :< pxy) =
  let recSplit = split xs sx pxys in
  recSplit :< pxy

fst : {0 a : Type} -> {0 p : a -> Type} -> {0 xs, ys : SnocList a} -> {0 pxys : All p (xs ++ ys)} -> Split xs ys pxys -> All p xs
fst (MkSplit xs ys pxs pys) = pxs

fstSnocForget : {0 pxys : All p (xs ++ ys)} -> (spl : Split xs ys pxys) -> (px : p x) -> fst (spl :< px) === fst spl
fstSnocForget (MkSplit xs ys pxs pys) px = Refl

snd : {0 a : Type} -> {0 p : a -> Type} -> {0 xs, ys : SnocList a} -> {0 pxys : All p (xs ++ ys)} -> Split xs ys pxys -> All p ys
snd (MkSplit xs ys pxs pys) = pys

sndSnocPrf : {0 a : Type} -> {0 p : a -> Type} -> {0 x : a} -> {0 xs, ys : SnocList a} -> {0 pxys : All p (xs ++ ys)} -> (spl : Split xs ys pxys) -> (px : p x) -> snd (spl :< px) === snd spl :< px
sndSnocPrf (MkSplit xs ys pxs pys) px = Refl

-------------------------------------------------------------------------------

stackFst : (s' : ?) -> Stack (s ++ s') -> Stack s
stackFst s' stack =
  fst (split s s' stack)

stackFstPrf : (0 sx : ?) -> (ys : ?) -> (fxs : Stack sx) -> (gxs : Stack ys) -> stackFst ys (fxs ++ gxs) === fxs
stackFstPrf sx [<] fxs [<] = Refl
stackFstPrf sx (sy :< x) fxs (y :< z) =
  rewrite fstSnocForget (split sx sy (fxs ++ y)) z in
  stackFstPrf sx sy fxs y

stackSnd : (0 s : ?) -> {s' : ?} -> Stack (s ++ s') -> Stack s'
stackSnd s stack = snd (split s s' stack)

stackSndPrf : (0 sx : ?) -> (ys : ?) -> (fxs : Stack sx) -> (gxs : Stack ys) -> stackSnd sx (fxs ++ gxs) === gxs
stackSndPrf sx [<] fxs [<] = Refl
stackSndPrf sx (sy :< x) fxs (y :< z) =
  let subprf = stackSndPrf sx sy fxs y in
  rewrite sndSnocPrf (split sx sy (fxs ++ y)) z in
  cong (:< z) subprf

stackSndSnoc :
  {0 x : Type} ->
  (fg : x) ->
  (0 sy : SnocList Type) ->
  {0 y : Type} ->
  {sx : SnocList Type} ->
  (fgs : Stack (sy ++ sx)) ->
  stackSnd {s' = sx :< x} sy (fgs :< fg) === stackSnd {s' = sx} sy fgs :< fg
stackSndSnoc fg sy fgs = sndSnocPrf (split sy sx fgs) fg

top : Stack (xs :< x) -> x
top (_ :< a) = a

drop : Stack (xs :< x) -> Stack xs
drop (as :< _) = as

stackProductCommute : FunExt => {a, b : ?} -> (c : SnocList Type) -> (f : (All Prelude.id c -> All Prelude.id a)) -> (g : (All Prelude.id c -> All Prelude.id b)) -> (f = (\x => stackFst b (f x ++ g x)), g = (\x => stackSnd a (f x ++ g x)))
stackProductCommute c f g = (funExt $ \x => sym $ stackFstPrf a b (f x) (g x), funExt $ \x => sym $ stackSndPrf a b (f x) (g x))

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
