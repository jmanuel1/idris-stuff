module LambdaC.Infer

import Data.List.Quantifiers
import Decidable.Equality
import LambdaC.Effect
import LambdaC.Parser
import LambdaC.FFI
import LambdaC.Lexer

%default total

fromList : (list : List (x : a ** p x)) -> All p (map DPair.fst list)

%default partial

checkHandle : (ctxt : Context) -> String -> List PreSyntax -> List PreSyntax -> (ty : Ty ctxt) -> Either String (Handle ctxt ty)
inferHandle : (ctxt : Context) -> String -> List PreSyntax -> List PreSyntax -> Either String (ty : Ty ctxt ** Handle ctxt ty)

checkExpr : (ctxt : Context) -> PreSyntax -> (ty : Ty ctxt) -> Either String (Expr ctxt ty)
inferExpr : (ctxt : Context) -> PreSyntax -> Either String (ty : Ty ctxt ** Expr ctxt ty)

checkExpr ctxt (PSNat n) ty@(CTy (TInt sign sz)) = pure (EInt sign sz (cast n))
checkExpr ctxt ps@(PSNat n) (ComputationTy effs ty) = map EPure (checkExpr ctxt ps ty)
checkExpr ctxt (PSList _ (PSKeyword KHandle :: PSID eff :: PSList _ handlers :: body)) ty =
  map EHandle $ checkHandle ctxt eff handlers body ty
checkExpr ctxt (PSList _ (head :: args)) ty = do
  args' <- for args (inferExpr ctxt)
  head' <- checkExpr ctxt head (map fst args' :-> ty)
  pure (head' :$ fromList args')
checkExpr ctxt ps ty = do
  (ty' ** e) <- inferExpr ctxt ps
  case decEq ty ty' of
    Yes Refl => pure e
    _ => Left "\{show ty} expected, got \{show ty'}"

inferExpr ctxt (PSNat n) = pure (CTy (TInt Signed SizeDefault) ** EInt _ _ (cast n))
inferExpr ctxt (PSList _ (PSKeyword KHandle :: PSID eff :: PSList _ handlers :: body)) =
  map (\(ty ** h) => (ty ** EHandle h)) $ inferHandle ctxt eff handlers body
inferExpr ctxt (PSList _ (head :: args)) = do
  (argTys :-> retTy ** head') <- inferExpr ctxt head

  args' <- for args (inferExpr ctxt)
  pure (head' :$ fromList args')
inferExpr ctxt ps = Left "cannot infer type of \{show ps}"
