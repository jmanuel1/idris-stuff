module LambdaC.SecondClass

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State
import Control.Monad.Reader
import Data.Either
import Data.Fin
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.Variant
import Derive.Eq
import Derive.Ord
import Derive.Show
import Generics.Derive
import LambdaC.C
import LambdaC.FFI

%default covering

%language ElabReflection

%hide Generics.Derive.Eq
%hide Generics.Derive.Ord
%hide Generics.Derive.Show
%hide Language.Reflection.Syntax.rec

namespace Class
  public export
  data Annotation = First | Second

  export
  fromInteger : (n : Integer) -> {auto prf : Either (n === 1) (n === 2)} -> Annotation
  fromInteger .(_) {prf = Left Refl} = First
  fromInteger .(_) {prf = Right Refl} = Second

  %runElab derive "Annotation" [Generic, Meta, Eq, Ord, Show]

namespace ExpTy
  public export
  data ExpTy : Type

namespace ValTy
  public export
  data ValTy = Boolean | Closure ValTy Annotation ExpTy | Pair ValTy Annotation ValTy Annotation

namespace ExpTy
  data ExpTy =
    NoReturn -- bottom
    | ValTy ValTy
    | CTy (CType ExpTy)

data TermF : Type -> Type where
  -- constants
  Extern : String -> CType ExpTy -> TermF rec
  Boolean : Bool -> TermF rec

  Var : String -> Annotation -> TermF rec
  Lam : String -> Annotation -> ValTy -> rec -> TermF rec
  App : rec -> rec -> TermF rec
  Pair : rec -> Annotation -> Annotation -> rec -> TermF rec
  Fst : rec -> TermF rec
  Snd : rec -> TermF rec
  If : rec -> rec -> rec -> TermF rec
  Let : String -> Annotation -> rec -> rec -> TermF rec
  -- the control operator C
  Control : rec -> TermF rec

data RuntimeValueF : Type -> Type where
  Closure : String -> rec -> List (String, rec) -> RuntimeValueF rec

Term : Type
Term = Fix TermF

RuntimeSyntax : Type
RuntimeSyntax = Fix (AnyF [TermF, RuntimeValueF])

isValue : RuntimeSyntax -> Bool
isValue = match [isTermValue, const True] . .any . .unFix
  where
    isTermValue : TermF RuntimeSyntax -> Bool
    isTermValue (Extern str x) = True
    isTermValue (Lam _ _ _ _) = True
    isTermValue (Pair x y z w) = isValue x && isValue w
    isTermValue _ = False

Stack : Type
Stack = List (Either (RuntimeSyntax -> RuntimeSyntax) (String, RuntimeSyntax))

Configuration : Type
Configuration = (RuntimeSyntax, Stack)

record CompilerCtxt where
  genNameCounter : Nat
  localCNames : SortedMap String String
  usedNames : SortedSet String

incrementCounter : MonadState CompilerCtxt m => m ()
incrementCounter = modify { genNameCounter $= (+ 1) }

markNameUsed : MonadState CompilerCtxt m => String -> m ()
markNameUsed name = modify { usedNames $= insert name }

genName : MonadState CompilerCtxt m => String -> m String
genName root = do
  incrementCounter
  suffix <- map (cast . .genNameCounter) get
  let name = GLOBAL_NAME_PREFIX ++ root ++ "_" ++ suffix
  if contains name (!get).usedNames
    then genName root
    else do
      markNameUsed name
      pure name

private
infix 6 `containsFree`
containsFree : RuntimeSyntax -> String -> Bool
containsFree t = match [go, go2] t.unFix.any where
  go : TermF RuntimeSyntax -> String -> Bool
  go (Extern str x) name = False
  go (Var str x) name = str == name
  go (Lam str _ _ y) name = str /= name && y `containsFree` name
  go (App x y) name = x `containsFree` name || y `containsFree` name
  go (Pair x y z w) name = x `containsFree` name || w `containsFree` name
  go (Fst x) name = x `containsFree` name
  go (Snd x) name = x `containsFree` name
  go (If x y z) name = x `containsFree` name || y `containsFree` name || z `containsFree` name
  go (Let str x y z) name = y `containsFree` name || str /= name && z `containsFree` name
  go (Control x) name = x `containsFree` name
  go (Boolean _) _ = False
  go2 : RuntimeValueF RuntimeSyntax -> String -> Bool
  go2 (Closure v b _) name = v /= name && b `containsFree` name

Ctxt : Type
Ctxt = SortedMap String (Annotation, ExpTy)

filter : Ord k => (k -> v -> Bool) -> SortedMap k v -> SortedMap k v
filter p xs = fromList $ filter (uncurry p) (toList xs)

restrict : Ctxt -> Annotation -> Ctxt
restrict ctxt n = filter (const ((<= n) . fst)) ctxt

TypedTerm : Type
TypedTerm = Fix (((Annotation, ExpTy), ) . TermF)

type : MonadError String m => Ctxt -> Term -> m TypedTerm
type ctxt = go . .unFix where
  go : TermF Term -> m TypedTerm
  go (Var v n) = do
    Just (ann, ty) <- pure $ lookup v (restrict ctxt n)
    | Nothing => throwError "\{v} cannot be used at class \{show n}"
    pure $ MkFix ((n, ty), Var v n)
  go (Extern ext ty) = pure $ MkFix ((1, CTy ty), Extern ext ty)
  go (Boolean b) = pure $ MkFix ((1, ValTy Boolean), Boolean b)
  go (Lam v n t b) = do
    b@(MkFix ((1, ty), _)) <- type (insert v (n, ValTy t) ctxt) b
    | _ => throwError "cannot return second-class value from lambda"
    pure $ MkFix ((2, ValTy $ Closure t n ty), Lam v n t b)

isValueTyped : RuntimeSyntax -> Bool

lookup : String -> Stack -> Maybe RuntimeSyntax
lookup var s = List.lookup var (rights s)

||| Take one step in evaluation. Errors are handled in a monad.
covering
step : MonadState CompilerCtxt m => MonadError String m => MonadReader (SortedMap String (RuntimeSyntax -> m RuntimeSyntax)) m => Configuration -> m Configuration
step c@(t, e) = match [stepTerm, stepRuntimeValue] t.unFix.any where
  stepTerm : TermF RuntimeSyntax -> m Configuration
  stepTerm (Var str x) =
    case lookup str e of
      Just val => pure (val, e)
      Nothing => throwError ("Unbound local: " ++ str)
  stepTerm (App x y) =
    if isValue x then
      if isValue y
        then match [
          \case
            Extern s _ => do
              Just extern <- asks (lookup s)
              | _ => throwError "Cannot step extern \{s}"
              res <- extern y
              pure (res, e)
            _ => throwError "Can call only closures",
          \case
            Closure v b env =>
              pure (b, Right (v, y) :: map Right env ++ e)
        ] x.unFix.any
        else pure (the RuntimeSyntax y, Left (fixInject . App x) :: e)
    else pure (x, Left (\res => fixInject $ App res y) :: e)
  stepTerm (Pair x y z w) =
    pure $ if isValue x then
      if isValue w then
        case e of
          Left f :: e => (f t, e)
          Right _ :: e => (t, e)
          [] => c
      else (w, Left (fixInject . Pair x y z) :: e)
    else (x, Left (\res => fixInject $ Pair res y z w) :: e)
  stepTerm (Fst x) =
    if isValue x
      then match [
        \case
          Pair first _ _ _ => pure (first, e)
          _ => throwError "fst requires a pair",
        \_ => throwError "fst requires a pair"
      ] x.unFix.any
      else pure (x, Left (fixInject . Fst) :: e)
  stepTerm (Snd x) =
    if isValue x
      then match [
        \case
          Pair _ _ _ second => pure (second, e)
          _ => throwError "snd requires a pair",
        \_ => throwError "snd requires a pair"
      ] x.unFix.any
      else pure (x, Left (fixInject . Snd) :: e)
  stepTerm (If x y z) =
    if isValue x then
      match [
        \case
          Boolean True => pure (y, e)
          Boolean False => pure (z, e)
          _ => throwError "Conditions must be boolean",
        \_ => throwError "Conditions must be boolean"
      ] x.unFix.any
    else pure (x, Left (\res => fixInject $ If res y z) :: e)
  stepTerm (Let str x y z) = do
    pure $
      if isValue y
      then (z, Right (str, y) :: e)
      else (y, Left (\res => fixInject $ Let str x res z) :: e)
  stepTerm t@(Control x) =
    case e of
      [] =>
        if isValue x then do
          Just (Closure kVar b _) <- pure (the (Maybe (RuntimeValueF _)) $ getAltLayer x)
          | _ => throwError "Control operator expects a lambda as an argument"
          let invalidUse = throwError "Invalid top-level use of control operator"
          Just (App f t) <- pure (the (Maybe (TermF _)) $ getAltLayer b)
          | _ => invalidUse
          Just (Var kVar2 _) <- pure (the (Maybe (TermF _)) $ getAltLayer f)
          | _ => invalidUse
          if kVar == kVar2 && not (t `containsFree` kVar)
            then pure (t, e)
            else invalidUse
        else pure (x, Left (fixInject . Control) :: e)
      (Right _ :: e) => the (m Configuration) $ pure {f = m} (fixInject t, e)
      (Left f :: e) =>
        if isValue x then do
          Just (Closure kVar t _) <- pure (the (Maybe (RuntimeValueF _)) $ getAltLayer x)
          | _ => throwError "Control operator expects a lambda as an argument"
          -- if isValueTyped (f (fixInject $ Control x))
            -- then do
          -- jVar <- genName "j"
          xVar <- genName "x"
          pure (fixInject $ Control (fixInject $ Lam "j" 2 (fixInject $ Let kVar 2 (fixInject $ Lam xVar 1 (fixInject (App (fixInject $ (Var "j" 2)) (f (fixInject $ Var xVar 1))))) t)), e)
            -- else throwError "Single-frame context must have a value type"
        else pure (x, Left (fixInject . Control) :: e)
  stepTerm (Lam v n t) = pure (fixInject $ Closure v t $ rights e, e)
  stepTerm _ =
    pure $ case e of
      Left f :: e => (f t, e)
      Right _ :: e => (t, e)
      _ => c
  stepRuntimeValue : RuntimeValueF RuntimeSyntax -> m Configuration
  stepRuntimeValue _ =
    pure $ case e of
      Left f :: e => (f t, e)
      Right _ :: e => (t, e)
      _ => c

{-
record Program where
  ffiExports : List (String, Term)



getLocalName : MonadState CompilerCtxt m => String -> m String
getLocalName local = do
  Just cName <- map (lookup local . .localCNames) get
  | Nothing => do
    cName <- genName local
    modify { localCNames $= insert local cName }
    pure cName
  pure cName

{-
enterBlock : MonadState CompilerCtxt m => String -> CType -> m a -> m a
enterBlock var type block = do
  (_, context) <- get
  modify (mapSnd (insert var type))
  result <- block
  modify (mapSnd (const context))
  pure result

compileTerm : MonadState CompilerCtxt m => Term -> m CExp
compileTerm (Extern str x) = pure str
compileTerm (Var str x) = getLocalName str
compileTerm (Lam str x y) = do
  envTypeName <- genName "closure_env"
  closureTypeName <- genName "closure"
  (bodyDecls, bodyExpr, bodyType) <- enterBlock arg argType $ lcToC body
  let closedOverVars = SortedSet.toList $ freeVars abs
  closedOverVarTypes <- traverse (\var => getCType var) closedOverVars
  let envTypeDecl = Struct (map (\(v, t) => Var t v Nothing) $ zip closedOverVars closedOverVarTypes) envTypeName
  funName <- genName "lambda_abstraction"
  let envType = RawType $ "struct " ++ envTypeName
      closureTypeDecl = Struct [FunPtr bodyType "function" [argType, envType], Var envType "env" Nothing] closureTypeName
      varDecls = map (\(var, t) => DeclStmt $ Var t var (Just ("env." ++ var))) $ zip closedOverVars closedOverVarTypes
      envInit = joinBy ", " closedOverVars
      funDecl = Fun bodyType funName [MkCArg argType arg, MkCArg (RawType $ "struct " ++ envTypeName) "env"] (map DeclStmt bodyDecls ++ varDecls ++ [RawStmt ("return " ++ bodyExpr)])
      closureExp = "(struct " ++ closureTypeName ++ "){" ++ funName ++ ", (struct " ++ envTypeName ++ "){" ++ envInit ++ "}}"
  tell [envTypeDecl, closureTypeDecl, funDecl]
  pure ([], closureExp, FunType argType bodyType $ "struct " ++ closureTypeName)
compileTerm (App x y) = ?h_3
compileTerm (Pair x y z w) = ?h_4
compileTerm (Fst x) = ?h_5
compileTerm (Snd x) = ?h_6
compileTerm (If x y z) = ?h_7
compileTerm (Let str x y z) = ?h_8
compileTerm (Control x) = ?h_9
