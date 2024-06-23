module LambdaC.AbstractInterp.ConcreteSem

import Data.SortedMap
import Data.Vect
import LambdaC
import LambdaC.Let

data N =
  Abs String CType Expr -- variable annotated with C type that is not checked
  | Prim String

Cast N Expr where
  cast n = ?hole1

mutual
  Val : Type
  Val = SortedMap String Closure

  Closure : Type
  Closure = (Val, N)

Stack : Type
Stack = List (Closure )

data Intermediate = MkIntermed Stack Expr Val

data State = Intermed Intermediate | Value Stack Closure

transition : Intermediate -> Maybe State
transition (MkIntermed s (Var str) val) = [| (Value s) (lookup str val) |]
transition (MkIntermed s (App f y) val) = pure (Intermed (MkIntermed ((\(fval, fn) =>
  case n of
    -- XXX: t used?
    Abs x t b => Intermed (MkIntermed ((\yclosure@(yval, yn) =>
      Intermed (MkIntermed s b (insert x yclosure fval))) :: s) y val)) :: s) f val))
transition (MkIntermed s (Abs str x y) val) = pure (Value s (val, Abs str x y))
transition (MkIntermed s e@(Fix str x y z) val) =
  let argName = ?genname in
    Intermed (MkIntermed s (Abs argName y ((x `App` e) `App` argName)) val)
transition (MkIntermed s (Extern str x) val) = pure (Value s (val, Prim str))
transition (MkIntermed (Let str x y z) val) = ?hole_5
