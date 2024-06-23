module LambdaC.NBE

import Control.Monad.State
import Data.SortedMap
import Debug.Trace
import LambdaC

data Sem : (Type -> Type) -> Type where
  Lam : (Sem m -> m (Sem m)) -> Sem m
  Fix : (Sem m -> m (Sem m)) -> Sem m
  Extern : String -> CType -> Sem m
  Syn : LC -> Sem m

incrementCounter : MonadState Nat m => m ()
incrementCounter = modify (+ 1)

genName : MonadState Nat m => m String
genName = do
  incrementCounter
  suffix <- map cast get
  pure (GLOBAL_NAME_PREFIX ++ "_" ++ suffix)

mutual
  reflect : MonadState Nat m => CType -> LC -> m (Sem m)
  reflect (RawType str) lc = pure $ Syn lc
  reflect (FunType x y str) lc = pure $ Lam $ \s => reflect y (lc `App` !(reify x s))
  reflect (ExternType x) lc = reflect x lc

  partial
  reify : MonadState Nat m => CType -> Sem m -> m LC
  reify (RawType str) (Syn t) = pure t
  reify (FunType x y str) (Lam s) = do
    var <- genName
    pure $ Abs var x !(reify y !(s !(reflect x (Var var))))
  reify ty@(FunType x y str) (Fix s) = do
    var <- genName
    pure $ Fix var !(reify ty !(s !(reflect ty (Var var)))) x y
  reify (ExternType x) sem = reify x sem

Context : (Type -> Type) -> Type
Context m = SortedMap String (Sem m)

partial
semApp : Monad m => Sem m -> Sem m -> m (Sem m)
semApp (Lam f) y = f y
semApp (Fix f) y = (Lam $ \s => !(f (Fix f)) `semApp` s) `semApp` y

partial
meaning : Monad m => Context m -> LC -> m (Sem m)
meaning g (Var str) = case lookup str g of Just val => pure val
meaning g (App x y) =
  !(meaning g x) `semApp` !(meaning g y)
meaning g (Abs str x y) = pure $ Lam $ \s => meaning (insert str s g) y
meaning g (Fix str x y z) = pure $ Fix $ \s => meaning (insert str s g) x
meaning g t@(Extern str x) = pure $ Syn t

partial
nbe : MonadState Nat m => CType -> LC -> m LC
nbe a t = reify a !(meaning empty t)

||| Should spin.
partial
infNBE : LC
infNBE = evalState Z (nbe "int" omegaApp)

||| Should not spin.
partial
omegaNBE : LC
omegaNBE = evalState Z (nbe (FunType "int" "int" "") omega)
