module LambdaC.Let

import Data.Variant.Fix
import LambdaC
import LambdaC.Lambda

namespace Syntax
  public export
  data Expr =
    Var String
    | App Expr Expr
    | Abs String Ty Expr -- variable annotated with C type that is not checked
    | Fix String Expr Ty Ty      -- fix f = \x => f (fix f) x ==> f : (a -> b) -> (a -> b), fix : ((a -> b) -> (a -> b)) -> (a -> b)
    | Extern String Ty -- C expression annotated with unchecked C type
    | Let String Ty Expr Expr

namespace Transform
  export
  desugarLet : {-MonadState (Nat, SortedMap String CType) m => MonadError String m => -} Monad m => Expr -> m LC
  desugarLet (Var str) = pure $ MkFix $ Var str
  desugarLet (App x y) = pure $ MkFix $ App !(desugarLet x) !(desugarLet y)
  desugarLet (Abs str x y) = pure $ MkFix $ Abs str x !(desugarLet y)
  desugarLet (Fix str x y z) = pure $ MkFix $ Fix str !(desugarLet x) y z
  desugarLet (Extern str x) = pure $ MkFix $ Extern str x
  desugarLet (Let v t e body) = pure $ MkFix $ (MkFix $ Abs v t !(desugarLet body)) `App` !(desugarLet e)
