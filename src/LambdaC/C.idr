module LambdaC.C

import LambdaC.FFI

%default total

public export
data Ty = MkTy (CType Ty)

public export
record CArg where
  constructor MkCArg
  type : Ty
  name : String

CExp = String

mutual
  public export
  data CStmt = RawStmt String | DeclStmt CDecl

  export
  FromString CStmt where
    fromString x = RawStmt x

  public export
  data CDecl =
    Fun Ty String (List CArg) (List CStmt)
    | Struct (List CDecl) String
    | Var Ty String (Maybe String)
    | FunPtr Ty String (List Ty)

public export
C : Type
C = List CDecl

export
GLOBAL_NAME_PREFIX : String
GLOBAL_NAME_PREFIX = "lc_"
