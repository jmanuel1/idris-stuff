module LambdaC.Let

import LambdaC

namespace Syntax
  public export
  data Expr =
    Var String
    | App Expr Expr
    | Abs String CType Expr -- variable annotated with C type that is not checked
    | Fix String Expr CType CType      -- fix f = \x => f (fix f) x ==> f : (a -> b) -> (a -> b), fix : ((a -> b) -> (a -> b)) -> (a -> b)
    | Extern String CType -- C expression annotated with unchecked C type
    | Let String CType Expr Expr

namespace Transform
  export
  desugarLet : {-MonadState (Nat, SortedMap String CType) m => MonadError String m => -} Monad m => Expr -> m LC
  desugarLet (Var str) = pure $ Var str
  desugarLet (App x y) = pure $ App !(desugarLet x) !(desugarLet y)
  desugarLet (Abs str x y) = pure $ Abs str x !(desugarLet y)
  desugarLet (Fix str x y z) = pure $ Fix str !(desugarLet x) y z
  desugarLet (Extern str x) = pure $ Extern str x
  desugarLet (Let v t e body) = pure $ (Abs v t !(desugarLet body)) `App` !(desugarLet e)
