module LambdaC

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Derive.Eq
import Derive.Ord
import Deriving.Show
import Generics.Derive
import System
import System.File.Handle
import System.File.ReadWrite

%language ElabReflection

%hide Generics.Derive.Eq
%hide Generics.Derive.Ord

-- lambda calculus

{-
namespace LC
  export
  freeVars : LC -> SortedSet String
  freeVars (Var str) = singleton str
  freeVars (App x y) = freeVars x `union` freeVars y
  freeVars (Abs str _ x) = delete str $ freeVars x
  freeVars (Fix var body _ _) = delete var $ freeVars body
  freeVars (Extern str _) = empty

  export
  sub : String -> LC -> LC -> LC
  sub var to w@(Var whole) = if var == whole
    then to
    else w
  sub var to (App wholeFun wholeArg) =
    App (sub var to wholeFun) (sub var to wholeArg)
  sub var to w@(Abs varWhole typeWhole bodyWhole) = if var == varWhole
    then w
    else
      -- capture avoidance
      let to' = sub varWhole (Var (varWhole ++ "_")) to in
        Abs varWhole typeWhole (sub var to' bodyWhole)
  sub var to e@(Fix fVar body argType retType) = if var == fVar
    then e
    else Fix fVar (sub var to body) argType retType
  sub _ _ e@(Extern _ _) = e

CompilerState : Type
CompilerState = (Nat, SortedMap String CType)

incrementCounter : MonadState (Nat, SortedMap String CType) m => m ()
incrementCounter = modify $ mapFst (+ 1)

genName : MonadState (Nat, SortedMap String CType) m => String -> m String
genName root = do
  incrementCounter
  suffix <- map (cast . fst) get
  pure (GLOBAL_NAME_PREFIX ++ root ++ "_" ++ suffix)

getCType : MonadState (Nat, SortedMap String CType) m => MonadError String m => String -> m CType
getCType var = maybe (throwError ("don't know the C type of `" ++ var ++ "`")) pure $ lookup var $ snd !get

enterBlock : MonadState (Nat, SortedMap String CType) m => String -> CType -> m a -> m a
enterBlock var type block = do
  (_, context) <- get
  modify (mapSnd (insert var type))
  result <- block
  modify (mapSnd (const context))
  pure result

lcToC : MonadState CompilerState m => MonadError String m => MonadWriter (List CDecl) m => LC -> m (C, CExp, CType)
lcToC (Var str) = do
  type <- getCType str
  pure ([], str, type)
lcToC (App x y) = do
  (xDecls, xExp, xType) <- lcToC x
  let funRequired = \a => the (m a) $ throwError "function application requires C function type as the callable"
  FunType argType retType _ <- maybe (funRequired CType) pure $ getFunctionType xType
  | _ => funRequired (C, CExp, CType)
  (yDecls, yExp, _) <- lcToC y
  xResultName <- genName "function"
  let xResultDecl = Var xType xResultName (Just xExp)
  pure (xDecls ++ yDecls ++ [xResultDecl], xResultName ++ ".function((" ++ yExp ++ "), " ++ xResultName ++ ".env)", retType)
lcToC abs@(Abs arg argType body) = do
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
lcToC fix@(Fix var body argType retType) = do
  -- rewrite f: \fixf => \x => <body containing fixf> to recf := \x => <body containing recf>
  -- this is safe because nothing outside of this expression can call (\var => body)
  recFName <- genName "recursive_function"
  closureTypeName <- genName "closure"
  let closureExp = "(struct " ++ closureTypeName ++ "){" ++ recFName ++ ", env}"
  let bodyUsingRecursion = sub var (Extern closureExp (FunType argType retType ("struct " ++ closureTypeName))) body
  let bodyCall = bodyUsingRecursion `App` Var "x"
  (bodyDecls, bodyExpr, bodyType) <- enterBlock "x" argType $ lcToC bodyCall
  envTypeName <- genName "closure_env"
  let closedOverVars = SortedSet.toList $ freeVars fix
  closedOverVarTypes <- traverse (\var => getCType var) closedOverVars
  let varDecls = map (\(var, t) => DeclStmt $ Var t var (Just ("env." ++ var))) $ zip closedOverVars closedOverVarTypes
      envInit = joinBy ", " closedOverVars
      envTypeDecl = Struct (map (\(v, t) => Var t v Nothing) $ zip closedOverVars closedOverVarTypes) envTypeName
      envType = RawType $ "struct " ++ envTypeName
      closureTypeDecl = Struct [FunPtr bodyType "function" [argType, envType], Var envType "env" Nothing] closureTypeName
  let funDecl = Fun retType recFName [MkCArg argType "x", MkCArg (RawType $ "struct " ++ envTypeName) "env"] (map DeclStmt bodyDecls ++ varDecls ++ [RawStmt ("return " ++ bodyExpr)])
  let resultClosureExp = "(struct " ++ closureTypeName ++ "){" ++ recFName ++ ", (struct " ++ envTypeName ++ "){" ++ envInit ++ "}}"
  tell [envTypeDecl, closureTypeDecl, funDecl]
  pure ([], resultClosureExp, FunType argType retType $ "struct " ++ closureTypeName)
lcToC (Extern str type) = pure ([], str, type)

lcToCProgram : MonadState (Nat, SortedMap String CType) m => MonadError String m => LC -> m C
lcToCProgram lc = do
  ((decls, exp, type), globalDecls) <- runWriterT $ lcToC {m=WriterT (List CDecl) m} lc
  pure $ globalDecls ++ [Fun type "main" [] $ map DeclStmt decls ++ [RawStmt ("return " ++ exp)]]

writeCType : File -> CType -> IO ()
writeCType file (RawType type) = ignore (fPutStr file type)
writeCType file (FunType _ _ closureType) = ignore (fPutStr file closureType)
writeCType file (ExternType type) = writeCType file type

writeCArg : File -> CArg -> IO ()
writeCArg file arg = do
  writeCType file arg.type
  ignore (fPutStr file (" " ++ arg.name))

mutual
  writeCStmt : File -> CStmt -> IO ()
  writeCStmt file (RawStmt str) = ignore (fPutStr file (str ++ ";\n"))
  writeCStmt file (DeclStmt x) = do
    writeCDecl file x

  -- includes final semicolon, when appropriate
  writeCDecl : File -> CDecl -> IO ()
  writeCDecl file (Fun type name args body) = do
    writeCType file type
    ignore (fPutStr file (" " ++ name ++ "("))
    sequence_ $ intersperse (ignore (fPutStr file ", ")) (map (writeCArg file) args)
    ignore (fPutStr file ") {\n")
    for_ body (writeCStmt file)
    ignore (fPutStr file "}\n\n")
  writeCDecl file (Struct decls typename) = do
    ignore (fPutStr file ("struct " ++ typename ++ "{\n"))
    for_ decls (\decl => writeCDecl file decl)
    ignore (fPutStr file "};\n\n")
  writeCDecl file (Var type name (Just init)) = do
    writeCType file type
    ignore (fPutStr file (" " ++ name ++ " = " ++ init ++ ";\n"))
  writeCDecl file (Var type name Nothing) = do
    writeCType file type
    ignore (fPutStr file (" " ++ name ++ ";\n"))
  writeCDecl file (FunPtr retType name argTypes) = do
    writeCType file retType
    ignore (fPutStr file (" (*" ++ name ++ ")("))
    sequence_ $ intersperse (ignore (fPutStr file ", ")) (map (writeCType file) argTypes)
    ignore (fPutStr file ");\n")

writeC : File -> C -> IO ()
writeC file c = for_ c (writeCDecl file)

export
omega : LC
omega = Fix "f" (Var "f") "int" "int"

-- infinite recursion
export
omegaApp : LC
omegaApp = omega `App` Extern "5" "int"

main : IO ()
main = do
  cOmega <-
    eitherT die pure (evalStateT (the Nat 0, the (SortedMap String CType) empty) $ lcToCProgram omegaApp)
  ignore $ withFile "out.c" WriteTruncate
    (\err => printLn err)
    (\file => map pure $ writeC file cOmega)
