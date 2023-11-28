module Dual.Category.CoKleisli

import Dual.Category

%default total

-- CoKleisli : (c : Category o arr) -> {w : o -> o} -> Comonad c w -> Category o (\a, b => w a `arr` b)
-- CoKleisli c m = MkCategory {
--   id = m.extract,
--   compose = \f, g => c.compose f (c.compose (m.functor.fmap _ _ g) (m.duplicate _)),
--   idComposeRight = \a, b, f =>
--     rewrite m.fmapExtractAfterDuplicateId a in
--     c.idComposeRight (w a) b f,
--   idComposeLeft =
--     {-
--     c .compose (m .extract b) (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) = f
--             f
--     w a --------------> b
--      |                  ^
--      |                  |
--      | duplicate        | extract
--      |                  |
--      |                  |
--      v      fmap f      |
--     w (w a) ----------> w b
--
--     fmap f . duplicate = (co)extend f
--     Need equation: extract . extend f = f
--     https://hackage.haskell.org/package/comonad
--     -}
--     m.extractAfterExtend,
--   composeAssociative = \a, b, c', d, f, g, h =>
--     -- c .compose (c .compose h (c .compose ((m .functor) .fmap (w b) c' g) (m .duplicate b))) (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) =
--     -- c .compose h (c .compose ((m .functor) .fmap (w a) c' (c .compose g (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)))) (m .duplicate a))
--     rewrite c.composeAssociative _ _ _ _ (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) (c .compose ((m .functor) .fmap (w b) c' g) (m .duplicate b)) h in
--     cong (c.compose h) $
--     -- c .compose (c .compose ((m .functor) .fmap (w b) c' g) (m .duplicate b)) (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) =
--     -- c .compose ((m .functor) .fmap (w a) c' (c .compose g (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)))) (m .duplicate a)
--     let fproof = m.functor.composition (w a) (w b) c' g (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) in
--     let rhsproof = cong (\x => c.compose x (m.duplicate a)) fproof in
--     -- c .compose (c .compose ((m .functor) .fmap (w b) c' g) (m .duplicate b)) (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) =
--     -- c .compose (c .compose ((m .functor) .fmap (w b) c' g) ((m .functor) .fmap (w a) (w b) (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)))) (m .duplicate a)
--     trans
--       (trans
--         (c.composeAssociative _ _ _ _ (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) (m .duplicate b) ((m .functor) .fmap (w b) c' g))
--         (trans
--           (cong (c.compose ((m .functor) .fmap (w b) c' g)) $
--           trans
--             -- c .compose (m .duplicate b) (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) =
--             -- c .compose (c .compose ((m .functor) .fmap (w (w a)) (w b) ((m .functor) .fmap (w a) b f)) ((m .functor) .fmap (w a) (w (w a)) (m .duplicate a))) (m .duplicate a)
--             (trans
--               {-
--                         duplicate                       fmap duplicate
--               w a -------------------------> w (w a) -------------------> w (w (w a))
--                                               |                               |
--                                               |                               |
--                                               |                               |
--                                               | fmap f          fmap (fmap f) |
--                                               |                               |
--                                               |                               |
--                                               V       duplicate               v
--                                              w b ------------------------> w (w b)
--               duplicate @a . extend f = extend (fmap f)
--               -}
--               - c .compose (m .duplicate b) (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a)) =
--               - c .compose ((m .functor) .fmap (w (w a)) (w b) ((m .functor) .fmap (w a) b f)) (c .compose ((m .functor) .fmap (w a) (w (w a)) (m .duplicate a)) (m .duplicate a))
--               ?compassochole
--               (sym $ c.composeAssociative _ _ _ _ (m .duplicate a) ((m .functor) .fmap (w a) (w (w a)) (m .duplicate a)) ((m .functor) .fmap (w (w a)) (w b) ((m .functor) .fmap (w a) b f))))
--             (sym $ cong (\x => c.compose x (m.duplicate a)) (m.functor.composition _ _ _ ((m .functor) .fmap (w a) b f) (m .duplicate a))))
--           (sym $ c.composeAssociative _ _ _ _ (m .duplicate a) ((m .functor) .fmap (w a) (w b) (c .compose ((m .functor) .fmap (w a) b f) (m .duplicate a))) ((m .functor) .fmap (w b) c' g))))
--       (sym rhsproof)
-- }

Comonad : {o : _} -> {a : _} -> Category o a -> (o -> o) -> Type
Comonad c w = KleisliTriple (dual c) w

CoKleisli : (c : Category o arr) -> {w : o -> o} -> Comonad c w -> Category o (\a, b => (flip arr) a (w b))
CoKleisli c m = mkKleisliCategory (dual c) m

-- CofreeFunctor : Cocartesian o a c -> (f : o -> o) -> Functor c c f -> o -> o
-- CofreeFunctor cocart f _ a = (cocart.finiteProduct a (f a)).product

Cofree : (c : Category _ _) -> (m : Comonad c w) -> Functor c (CoKleisli c m) Prelude.id
Cofree c m = MkFunctor {
  fmap = \a, b, f => ?h1,
  identity = \a => ?h2,
  composition = \a, b, c, f, g => ?h3
}
