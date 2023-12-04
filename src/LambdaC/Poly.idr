module LambdaC.Poly

import Control.Monad.State
import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Data.SortedMap
import Data.SortedMap.Dependent
import Data.SortedSet
import Derive.Eq
import Derive.Ord
import Derive.Show
import Generics.Derive
import LambdaC
import LambdaC.Let

%language ElabReflection

%hide Generics.Derive.Eq
%hide Generics.Derive.Ord
%hide Generics.Derive.Show

namespace Types
  public export
  data PType = RawType String | FunType PType PType | ExternType CType | TypeVar String | ForAll String PType

  %runElab derive "PType" [Generic, Meta, Eq, Ord, Show]

  export
  Interpolation PType where
    interpolate = show

  export
  injectCType : CType -> PType
  injectCType (RawType t) = RawType t
  injectCType (FunType s t _) = (injectCType s) `FunType` (injectCType t)
  injectCType (ExternType t) = ExternType t

  export
  FromString PType where
    fromString = injectCType . fromString

namespace Syntax
  -- Only polymorphism at let is allowed.
  public export
  data PExpr =
    Var String
    | App PExpr PExpr PType
    | Abs String PType PExpr
    | Fix String PExpr PType PType
    | Extern String CType -- C expression annotated with unchecked C type
    | Let String PType PExpr PExpr
    | TypeApp PExpr PType

  %runElab derive "PExpr" [Generic, Meta, Eq, Ord, Show]

  export
  Interpolation PExpr where
    interpolate = show

namespace Transform
  -- nameAbs : MonadState Nat m => PExpr -> m PExpr
  -- nameAbs (Var str) = Var str
  -- nameAbs (App x y) = ?plet_1
  -- nameAbs (Abs str x y) = ?plet_2
  -- nameAbs (Fix str x strs y z) = ?plet_3
  -- nameAbs (Extern str x) = ?plet_4
  -- nameAbs (Let str x y z) = ?plet_5
  -- nameAbs (TypeApp x y) = ?plet_6
  --
  record MonomorphizeState where
    constructor MkMS
    instantiatedVars : SortedMap String (SortedMap PType String)
    context : SortedMap String PType
    counter : Nat

  getPType : MonadState MonomorphizeState m => MonadError String m => String -> m PType
  getPType var = maybe (throwError ("don't know the type of `" ++ var ++ "`")) pure $ lookup var $ (!get).context

  enterBlock : MonadState MonomorphizeState m => String -> PType -> m a -> m a
  enterBlock var type block = do
    context <- map (.context) get
    modify {context $= insert var type}
    result <- block
    modify {context := context}
    pure result

  setTypeVars : MonadState MonomorphizeState m => MonadError String m =>  PType -> PType -> m (SortedMap String PType)
  setTypeVars (RawType str) target = pure empty
  setTypeVars (FunType x y) (FunType z w) = do
    sub <- setTypeVars x z
    sub2 <- setTypeVars y w
    pure (sub `mergeLeft` sub2)
  setTypeVars source@(FunType _ _) target = throwError "Mismatch between function type and non-function type: \{source} and \{target}"
  setTypeVars (ExternType x) target = pure empty
  setTypeVars (TypeVar str) target = pure (singleton str target)
  setTypeVars (ForAll str x) (ForAll str1 y) = do
    sub <- setTypeVars x y
    pure (insert str (TypeVar str1) sub)
  setTypeVars (ForAll str x) (RawType str1) = ?hole_5
  setTypeVars (ForAll str x) (FunType y z) = ?hole_6
  setTypeVars (ForAll str x) (ExternType y) = ?hole_7
  setTypeVars (ForAll str x) (TypeVar str1) = ?hole_8
  -- Forall "A" (ForAll "A" t), ForAll "B" (ForAll "C" t)

  bindInstances : MonadState MonomorphizeState m => String -> PExpr -> PExpr -> m PExpr
  bindInstances var init e = do
    instVars <- map (.instantiatedVars) get
    let instancesMapping = fromMaybe empty (lookup var instVars)
    pure $ Data.SortedMap.Dependent.foldl (\newE, (ty ** newVar) =>
      Let newVar ty init newE) e (cast instancesMapping)

  incrementCounter : MonadState MonomorphizeState m => m ()
  incrementCounter = modify {counter $= (+ 1)}

  genName : MonadState MonomorphizeState m => String -> m String
  genName root = do
    incrementCounter
    suffix <- map (cast . (.counter)) get
    pure (GLOBAL_NAME_PREFIX ++ root ++ "_" ++ suffix)

  instantiateVar : MonadState MonomorphizeState m => String -> PType -> m (PExpr, PType)
  instantiateVar var t = do
    instVars <- map (.instantiatedVars) get
    let instancesMapping = fromMaybe empty (lookup var instVars)
    case lookup t instancesMapping of
      Just varInst => pure (Var varInst, t)
      Nothing => do
        varInst <- genName var
        modify {instantiatedVars $= insert var (insert t varInst instancesMapping)}
        pure (Var varInst, t)

  export
  monomorphize : MonadState MonomorphizeState m => MonadError String m => PExpr -> PType -> m (PExpr, PType)
  monomorphize exp (ForAll tyVar expTy) = do
    (exp', expTy') <- monomorphize exp expTy
    pure (exp', ForAll tyVar expTy')
  monomorphize (Var str) expTy = instantiateVar str expTy
  monomorphize (App x y yType) expTy = do
    (y', yTy) <- monomorphize y yType
    (x', FunType argTy retTy) <- monomorphize x (yTy `FunType` expTy)
    | (x', _) => throwError "Must have function type: \{x}, monomorphized to \{x'}"
    pure (App x' y' argTy, retTy)
  monomorphize e@(Abs str _ y) expTy = do
    FunType argTy retTy <- pure expTy
    | _ => throwError "Must have function type: \{e}, instead given type \{expTy}"
    (y', yTy) <- enterBlock str argTy $ monomorphize y retTy
    pure (Abs str argTy y, argTy `FunType` yTy)
  monomorphize exp@(Fix f e _ _) expTy = do
    FunType argTy retTy <- pure expTy
    | _ => throwError "Must have function type: \{exp}, instead given type \{expTy}"
    let ty = argTy `FunType` retTy
    (e', eTy@(FunType eArgTy eRetTy)) <- enterBlock f ty $ monomorphize e ty
    | (e', _) => throwError "Must have function type: \{e}, monomorphized to \{e'}"
    pure (Fix f e' eArgTy eRetTy, eTy)
  monomorphize (Extern str x) _ = pure (LambdaC.Poly.Syntax.Extern str x, injectCType x)
  monomorphize (Let v t e body) expTy = do
    (e', eTy) <- monomorphize e t
    savedInstVars <- map (.instantiatedVars) get
    (body', bodyTy) <- enterBlock v eTy $ monomorphize body expTy
    bodyWithInstsBound <- bindInstances {m} v e' body'
    pure (bodyWithInstsBound, bodyTy)
  monomorphize (TypeApp e t) expTy = do
    (e', eTy) <- monomorphize e expTy
    pure (e', eTy)

  uniquifyTypeVariables : MonadState MonomorphizeState m => SortedMap String String -> PExpr -> m PExpr
  uniquifyTypeVariables typeContext e@(Var str) = pure e
  uniquifyTypeVariables typeContext (App x y z) = ?hole2_1
  uniquifyTypeVariables typeContext (Abs str x y) = ?hole2_2
  uniquifyTypeVariables typeContext (Fix str x y z) = ?hole2_3
  uniquifyTypeVariables typeContext (Extern str x) = ?hole2_4
  uniquifyTypeVariables typeContext (Let str x y z) = ?hole2_5
  uniquifyTypeVariables typeContext (TypeApp x y) = ?hole2_6

||| test: generic within generic
genericWithinGeneric : Either String (PExpr, PType)
genericWithinGeneric =
  let
    idType := \ty => ty `FunType` ty
    bindId : String -> PExpr -> PExpr
    bindId := \name => Let name (ForAll "A" (TypeVar "A" `FunType` TypeVar "A")) (Abs "x" (TypeVar "A") (Var "x"))
    e := bindId "f" (bindId "g" (App (App (Var "f") (Var "g") (idType "int")) (Extern "5" "int") "int"))
  in
    runIdentity (runEitherT {m = Identity, e = String} (evalStateT (MkMS {instantiatedVars = empty, context = empty, counter = 0}) (monomorphize e (ExternType "int"))))
-- test: fix, polymorphic recursion, abs (check names)
