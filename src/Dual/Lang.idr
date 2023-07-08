module Dual.Lang

import Dual.Computation
import Data.List.Elem
import Data.Morphisms
import Syntax.WithProof

{-
STLC:

e = \x : t. e | e e | x
  | ()
t = t -> t
  | ()

Dual:
e^op = /x^op : t^op. e^op | coapp e^op e^op | x^op
     | never
t^op = t^op - t^op
     | Void

Sanity check:
[[ x ]] : (gamma, t) -> t                               = pi'
[[ \x : t. x ]] : gamma -> t ** t                       = curry pi'
[[ (\x : t. x) y ]] : (gamma, t) -> t                   = eval . (curry pi_x, pi_y)
[[ () ]] : gamma -> () (must exist because () is final) = unit

[[ x ]] : t -> Either gamma t                                     = inr
[[ /x : t. x ]] : t - t -> gamma                                  = cocurry inr
[[ coapp (/x : t. x) y ]] : t -> Either gamma t                   = [cocurry in_x, in_y] . coeval
The coapplication will switch to y when the cofunction evaluates to the most recently introduced covariable (i.e. its argument). (I think.)
[[ never ]] : Void -> gamma (must exist because Void is initial)  = absurd
-}

%default total

toEitherType : List Type -> Type
toEitherType [] = Void
toEitherType (t :: ts) = Either (toEitherType ts) t

inj : Elem t ts -> t -> toEitherType ts
inj Here val = Right val
inj (There x) val = Left (inj x val)

covar : Elem t ts -> KleisliCont r t (toEitherType ts)
covar index = Kleisli (pure . inj index)

never : KleisliCont r Void gamma
never = Kleisli absurd

colambda : KleisliCont r b (Either gamma a) -> KleisliCont r (Coexp r b a) gamma
colambda = cocurry

coapp : KleisliCont r (Coexp r a b) gamma -> KleisliCont r b gamma -> KleisliCont r a gamma
coapp (Kleisli colam) (Kleisli e) = Kleisli $ \x, k => coeval.applyKleisli x $ \eith =>
  case eith of
    Left coexp => colam coexp k
    Right y => e y k

namespace Example
  ||| coapp (/x : t. x) y
  export
  likeId : KleisliCont r t (toEitherType (t :: gamma))
  likeId = coapp (colambda (covar {ts = t :: t :: gamma} Here)) (covar Here)

  ||| coapp (/x : s. /z : t. z) y
  export
  inner : {0 s : Type} -> KleisliCont r (Coexp r t t) (toEitherType (s :: gamma))
  inner = coapp (colambda (colambda (covar {ts = t :: s :: s :: gamma} Here))) (covar Here)

  ||| coapp (/x : t. /z : s. x) y

  export
  runLikeId : Nat
  runLikeId = (likeId {gamma = []}).applyKleisli 42 (either absurd id)
