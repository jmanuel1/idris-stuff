module Data.Container.Combinators

import Control.Function.FunExt
import Data.Container

%default total

public export
constRoundTrip : FunExt => (c1 : Extension _ x) -> Combinators.toConst (fromConst c1) === c1
constRoundTrip (MkExtension shape payloads) = cong (MkExtension shape) $ funExt $ \v => absurd v

public export
pairRoundTrip : FunExt => (ext : Extension (Pair c d) x) -> toPair (fst (fromPair {c, d} ext), snd (fromPair {c, d} ext)) === ext
pairRoundTrip (MkExtension (y, z) payloads) = cong (MkExtension (y, z)) $ funExt $ \case
  Left payload => Refl
  Right payload => Refl
