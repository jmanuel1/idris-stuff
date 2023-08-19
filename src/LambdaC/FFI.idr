module LambdaC.FFI

import Derive.Eq
import Derive.Ord
import Derive.Show
import Deriving.Show
import Generics.Derive

%language ElabReflection
%default total

%hide Generics.Derive.Eq
%hide Generics.Derive.Ord
%hide Generics.Derive.Show

namespace C
  public export
  data Signedness = Signed | Unsigned

  %runElab derive "Signedness" [Generic, Meta, Eq, Ord, Show]

  public export
  data Size =
    Size8 | Size16 | Size32 | Size64
    | SizeShort | SizeDefault | SizeLong | SizeLongLong

  %runElab derive "Size" [Generic, Meta, Eq, Ord, Show]

  infixr 1 :->*

  public export
  data CType pointedToTy =
    TInt Signedness Size
    | TChar
    | TFloat Size
    | TString
    | TPtr pointedToTy
    | TAnyPtr
    | TRawType String
    | (:->*) (List (CType pointedToTy)) (CType pointedToTy)
    | TStruct (List (String, (CType pointedToTy)))
    | TUnion (List (String, (CType pointedToTy)))
    | TNamed String (CType pointedToTy)

  %default partial
  %runElab derive "CType" [Generic, Meta, Eq, Ord, Show]
  %default total

  export
  FromString (CType pointedToTy) where
    fromString = TRawType

  getFunctionType : CType ptrTy -> Maybe (CType ptrTy)
  getFunctionType t@(_ :->* _) = Just t
  getFunctionType (TNamed _ t) = getFunctionType t
  getFunctionType _ = Nothing
