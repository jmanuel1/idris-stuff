module LambdaC.SecondClass

import Control.Monad.State
import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Data.Fin
import Data.SortedMap
import LambdaC.C
import LambdaC.Effect
import LambdaC.FFI

%default total

namespace Class
  public export
  data Annotation = First | Second

  export
  fromInteger : (n : Integer) -> {auto prf : Either (n === 1) (n === 2)} -> Annotation
  fromInteger .(_) {prf = Left Refl} = First
  fromInteger .(_) {prf = Right Refl} = Second

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

data Term : Type where
  -- constants
  Extern : String -> CType ExpTy -> Term
  Var : String -> Annotation -> Term
  Lam : String -> Annotation -> Term -> Term
  App : Term -> Term -> Term
  Pair : Term -> Annotation -> Annotation -> Term -> Term
  Fst : Term -> Term
  Snd : Term -> Term
  If : Term -> Term -> Term -> Term
  Let : String -> Annotation -> Term -> Term -> Term
  -- the control operator C
  Control : Term -> Term

isValue : Term -> Bool
isValue (Extern str x) = True
isValue (Var str x) = True
isValue (Lam str x y) = True
isValue (Pair x y z w) = isValue x && isValue w
isValue _ = False

-- ||| E[_]
-- findEvalCtxt : Term -> (Term, Term -> Term)
-- findEvalCtxt (App x y) =
--   if isValue x then
--     let (redex, e) = findEvalCtxt y in (redex, \res => App x (e res))
--   else let (redex, e) = findEvalCtxt x in (redex, \res => App (e res) y)
-- findEvalCtxt (Pair x y z w) =
--   if isValue x then
--     let (redex, e) = findEvalCtxt w in (redex, \res => Pair x y z (e res))
--   else let (redex, e) = findEvalCtxt x in (redex, \res => Pair (e res) y z w)
-- findEvalCtxt (Fst x) = mapSnd (Fst .) (findEvalCtxt x)
-- findEvalCtxt (Snd x) = ?h1_6
-- findEvalCtxt (If x y z) = ?h1_7
-- findEvalCtxt (Let str x y z) = ?h1_8
-- findEvalCtxt (Control x) = ?h1_9
-- findEvalCtxt t = (t, id)

Configuration : Type
Configuration = (Term, List (Term -> Term))

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
  if contains name (!get).usedNames then
    genName root
  else do
    markNameUsed name
    pure name


-- getVar : MonadState EvalCtxt m => String -> m (Maybe Term)
-- getVar name = map (lookup name . .env) get

infix 6 `containsFree`
containsFree : Term -> String -> Bool
containsFree (Extern str x) name = False
containsFree (Var str x) name = str == name
containsFree (Lam str x y) name = str /= name && y `containsFree` name
containsFree (App x y) name = x `containsFree` name || y `containsFree` name
containsFree (Pair x y z w) name = x `containsFree` name || w `containsFree` name
containsFree (Fst x) name = x `containsFree` name
containsFree (Snd x) name = x `containsFree` name
containsFree (If x y z) name = x `containsFree` name || y `containsFree` name || z `containsFree` name
containsFree (Let str x y z) name = y `containsFree` name || str /= name && z `containsFree` name
containsFree (Control x) name = x `containsFree` name

rename : Term -> String -> String -> Term
rename t@(Var name n) x y = if name == x then Var y n else t
rename t@(Lam name n b) x y = if name == x then t else Lam name n (rename b x y)
rename (Let name n v b) x y = Let name n (rename v x y) (if name == x then b else (rename b x y))
rename (App f a) x y = App (rename f x y) (rename a x y)
rename (Pair f m n s) x y = Pair (rename f x y) m n (rename s x y)
rename (Fst p) x y = Fst (rename p x y)
rename (Snd p) x y = Snd (rename p x y)
rename (If c t f) x y = If (rename c x y) (rename t x y) (rename f x y)
rename (Control t) x y = Control (rename t x y)
rename t@(Extern _ _) _ _ = t

covering
sub : Term -> String -> Term -> Term
sub body@(Var str x) var val = if var == str then Var var x else body
sub body@(Lam str x y) var val =
  if var == str then body else
  if val `containsFree` str then
    let renamedVar = str ++ "'" in
    sub (Lam renamedVar x (rename y str renamedVar)) var val
  else Lam str x (sub y var val)
sub (App x y) var val = App (sub x var val) (sub y var val)
sub (Pair x y z w) var val = Pair (sub x var val) y z (sub w var val)
sub (Fst x) var val = Fst (sub x var val)
sub (Snd x) var val = Snd (sub x var val)
sub (If x y z) var val = If (sub x var val) (sub y var val) (sub z var val)
sub (Let str x y z) var val =
  if var == str then Let str x (sub y var val) z else
  if val `containsFree` str then
    let renamedVar = str ++ "'" in
    sub (Let renamedVar x y (rename z str renamedVar)) var val
  else Let str x (sub y var val) (sub z var val)
sub (Control x) var val = Control (sub x var val)
sub body@(Extern _ _) _ _ = body

isValueTyped : Term -> Bool

||| Take one step in evaluation. Errors are handled in a monad.
covering
step : MonadState CompilerCtxt m => MonadError String m => Configuration -> m Configuration
step c@((Var str x), e) =
  throwError ("Unbound local:" ++ str)
step c@((App x y), e) =
  if isValue x then
    case x of
      Lam v n t =>
        if isValue y then pure (sub t v y, e) else pure (y, App x :: e)
      _ => throwError "Can call only lambdas"
  else pure (x, (\res => App res y) :: e)
step c@(t@(Pair x y z w), e) =
  pure $ if isValue x then
    if isValue w then
      case e of
        f :: e => (f t, e)
        [] => c
    else (w, Pair x y z :: e)
  else (x, (\res => Pair res y z w) :: e)
step ((Fst x), e) =
  if isValue x then
    case x of
      Pair first _ _ _ => pure (first, e)
      _ => throwError "fst requires a pair"
  else pure (x, Fst :: e)
step ((Snd x), e) =
  if isValue x then
    case x of
      Pair _ _ _ second => pure (second, e)
      _ => throwError "snd requires a pair"
  else pure (x, Snd :: e)
step ((If x y z), e) =
  if isValue x then
    case x of
      Extern "true" _ => pure (y, e)
      Extern "false" _ => pure (z, e)
      _ => throwError "Conditions must be boolean"
  else pure (x, (\res => If res y z) :: e)
step ((Let str x y z), e) = do
  markNameUsed str
  pure $ if isValue y then
    (sub z str y, e)
  else (y, (\res => Let str x res z) :: e)
step ((Control x), e@[]) =
  if isValue x then
    case x of
      Lam kVar _ (App (Var kVar2 _) t) =>
        if kVar == kVar2 && not (t `containsFree` kVar) then
          pure (t, e)
        else throwError "Invalid top-level use of control operator"
      _ => throwError "Control operator expects a lambda as an argument"
  else pure (x, Control :: e)
step ((Control x), f :: e) =
  if isValue x then
    case x of
      Lam kVar n t =>
        if isValueTyped (f (Control x)) then do
          jVar <- genName "j"
          xVar <- genName "x"
          pure (Control (Lam jVar 2 (sub t kVar (Lam xVar 1 (App (Var jVar 2) (f (Var xVar)))))), e)
        else throwError "Single-frame context must have a value type"
      _ => throwError "Control operator expects a lambda as an argument"
  else pure (x, Control :: e)
step c@(t@(Extern s _), e) =
  if s `elem` ["true", "false"] then
    pure $ case e of
      f :: e => (f t, e)
      [] => c
  else throwError "Cannot step externs"
step ((Lam v n t), e) = ?h_10

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
