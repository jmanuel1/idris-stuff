module LambdaC.Effect.Example

import Data.List
import LambdaC.Effect
import LambdaC.FFI

state : Block [<] UnitTy
state =
  BEffectDecl (EDGeneral "io" []) $
  BEffectDecl (EDGeneral "state"
    [MkOperation "get" ([] :-> (CTy $ TInt Signed SizeDefault)) Tail,
      MkOperation "set" ([CTy $ TInt Signed SizeDefault] :-> UnitTy) Tail]) $
  BDef (DefExtern "putstr" ([CTy (TPtr (CTy TChar))] :-> ComputationTy [NamedTy "io" %search] UnitTy)
    "putstr" ([TPtr (CTy TChar)] :->* TRawType "void")) $
  BDef (DefExtern "int->str" ([CTy (TInt Signed SizeDefault)] :-> CTy (TPtr (CTy TChar)))
    "itoa" ([TInt Signed SizeDefault] :->* TPtr (CTy TChar))) $
  BDef (DefExtern "set!" ([CTy (TPtr $ CTy $ TInt Signed SizeDefault), CTy (TInt Signed SizeDefault)] :-> UnitTy)
    "lc_set_int" ([TPtr $ CTy $ TInt Signed SizeDefault, TInt Signed SizeDefault] :->* TRawType "void")) $
  BDef (DefExtern "+" (repeat 2 [CTy (TInt Signed SizeDefault)] :-> CTy (TInt Signed SizeDefault))
    "lc_add_ints" (repeat 2 [TInt Signed SizeDefault] :->* TInt Signed SizeDefault)) BNil
