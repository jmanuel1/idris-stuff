module LambdaC.FFI

import Decidable.Equality
import Derive.Eq
import Derive.Ord
import Derive.Show
import Deriving.Functor
import Generics.Derive

%language ElabReflection
%default total

%hide Generics.Derive.Eq
%hide Generics.Derive.Ord
%hide Generics.Derive.Show

namespace C
  public export
  data Signedness = Signed | Unsigned

  %runElab derive "Signedness" [Generic, Meta, Eq, Ord, Show, DecEq]

  public export
  data Size =
    Size8 | Size16 | Size32 | Size64
    | SizeShort | SizeDefault | SizeLong | SizeLongLong

  %runElab derive "Size" [Generic, Meta, Eq, Ord, Show, DecEq]

  public export
  data FloatSize =
    FSize32 | FSize64

  %runElab derive "FloatSize" [Generic, Meta, Eq, Ord, Show, DecEq]

  export
  infixr 1 :->*

  public export
  data CType pointedToTy =
    TInt Signedness Size
    | TChar
    | TFloat FloatSize
    | TString
    | TPtr pointedToTy
    | TAnyPtr
    | TRawType String
    -- Function pointers.
    | (:->*) (List (CType pointedToTy)) (CType pointedToTy)
    | TStruct (List (String, (CType pointedToTy)))
    | TUnion (List (String, (CType pointedToTy)))

  %default partial
  %runElab derive "CType" [Generic, Meta, Eq, Ord, Show, DecEq]
  %default total

  public export
  Functor CType where
    map f (TInt x y) = TInt x y
    map f TChar = TChar
    map f (TFloat x) = TFloat x
    map f TString = TString
    map f (TPtr x) = TPtr (f x)
    map f TAnyPtr = TAnyPtr
    map f (TRawType str) = TRawType str
    map f (xs :->* x) = assert_total $ map (map f) xs :->* map f x
    map f (TStruct xs) = TStruct (assert_total $ map (mapSnd (map f)) xs)
    map f (TUnion xs) = TUnion (assert_total $ map (mapSnd (map f)) xs)

  export
  FromString (CType pointedToTy) where
    fromString = TRawType

  getFunctionType : CType ptrTy -> Maybe (CType ptrTy)
  getFunctionType t@(_ :->* _) = Just t
  getFunctionType _ = Nothing

  export
  0 intTy : Signedness -> Size -> Type
  intTy Signed Size8 = Int8
  intTy Signed Size16 = Int16
  intTy Signed Size32 = Int32
  intTy Signed Size64 = Int64
  intTy Signed SizeShort = Int
  intTy Signed SizeDefault = Int
  intTy Signed SizeLong = Integer
  intTy Signed SizeLongLong = Integer
  intTy Unsigned Size8 = Bits8
  intTy Unsigned Size16 = Bits16
  intTy Unsigned Size32 = Bits32
  intTy Unsigned Size64 = Bits64
  intTy Unsigned SizeShort = Nat
  intTy Unsigned SizeDefault = Nat
  intTy Unsigned SizeLong = Nat
  intTy Unsigned SizeLongLong = Nat
