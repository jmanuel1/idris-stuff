import Control.Monad.Identity
import Control.Monad.State
import System.File.Handle
import System.File.ReadWrite
import Data.SortedSet
import Data.String

-- untyped lambda calculus

namespace LC
  public export
  data LC =
    Var String
    | App LC LC
    | Abs String LC
    | Extern String -- C expression

  export
  freeVars : LC -> SortedSet String
  freeVars (Var str) = singleton str
  freeVars (App x y) = freeVars x `union` freeVars y
  freeVars (Abs str x) = delete str $ freeVars x
  freeVars (Extern str) = empty

-- C

namespace C
  public export
  record CArg where
    constructor MkCArg
    type : String
    name : String

  CExp = String

  mutual
    public export
    data CStmt = RawStmt String | DeclStmt CDecl

    FromString CStmt where
      fromString x = RawStmt x

    public export
    data CDecl =
      Fun String String (List CArg) (List CStmt)
      | Struct (List CDecl) String
      | Var String String (Maybe String)

  public export
  C : Type
  C = List CDecl

GLOBAL_NAME_PREFIX : String
GLOBAL_NAME_PREFIX = "lc_"

incrementCounter : MonadState Nat m => m ()
incrementCounter = modify (+ 1)

genName : MonadState Nat m => String -> m String
genName root = do
  incrementCounter
  suffix <- map cast get
  pure (GLOBAL_NAME_PREFIX ++ root ++ "_" ++ suffix)

lcToC : MonadState Nat m => LC -> m (C, CExp)
lcToC (Var str) = pure ([{-Var "int" str ("args." ++ str)-}], str)
lcToC (App x y) = do
  (xDecls, xExp) <- lcToC x
  (yDecls, yExp) <- lcToC y
  pure (xDecls ++ yDecls, "lc_app(" ++ xExp ++ ", " ++ yExp ++ ")")
lcToC abs@(Abs str body) = do
  envTypeName <- genName "closure_env"
  closureTypeName <- genName "closure"
  (bodyDecls, bodyExpr) <- lcToC body
  let closedOverVars = SortedSet.toList $ freeVars abs
      envTypeDecl = Struct (map (\var => Var "int" var Nothing) closedOverVars) envTypeName
      closureTypeDecl = Struct [Var "void *" "function" Nothing, Var ("struct " ++ envTypeName) "env" Nothing] closureTypeName
      varDecls = map (\var => DeclStmt $ Var "int" var (Just ("env." ++ var))) closedOverVars
      envInit = joinBy ", " closedOverVars
  pure ([envTypeDecl, closureTypeDecl, Fun "int" "TODO_names" [MkCArg "int" str, MkCArg ("struct " ++ envTypeName) "env"] (map DeclStmt bodyDecls ++ varDecls ++ [RawStmt ("return " ++ bodyExpr)])], "(struct " ++ closureTypeName ++ "){TODO_names, (struct " ++ envTypeName ++ "){" ++ envInit ++ "}}")
lcToC (Extern str) = pure ([], str)

lcToCProgram : MonadState Nat m => LC -> m C
lcToCProgram lc = do
  (decls, exp) <- lcToC lc
  pure $ decls ++ [Fun "void" "main" [] [RawStmt ("return " ++ exp)]]

writeCArg : File -> CArg -> IO ()
writeCArg file arg =
  ignore (fPutStr file (arg.type ++ " " ++ arg.name))

mutual
  writeCStmt : File -> CStmt -> IO ()
  writeCStmt file (RawStmt str) = ignore (fPutStr file (str ++ ";\n"))
  writeCStmt file (DeclStmt x) = do
    writeCDecl file x
    ignore (fPutStr file ";\n")

  writeCDecl : File -> CDecl -> IO ()
  writeCDecl file (Fun type name args body) = do
    ignore (fPutStr file (type ++ " " ++ name ++ "("))
    for_ args (\arg => writeCArg file arg >> ignore (fPutStr file ", "))
    ignore (fPutStr file ") {\n")
    for_ body (writeCStmt file)
    ignore (fPutStr file "}\n\n")
  writeCDecl file (Struct decls typename) = do
    ignore (fPutStr file ("struct " ++ typename ++ "{\n"))
    for_ decls (\decl => writeCDecl file decl >> ignore (fPutStr file ";\n"))
    ignore (fPutStr file "};\n\n")
  writeCDecl file (Var type name (Just init)) = do
    ignore (fPutStr file (type ++ " " ++ name ++ " = " ++ init))
  writeCDecl file (Var type name Nothing) = do
    ignore (fPutStr file (type ++ " " ++ name))

writeC : File -> C -> IO ()
writeC file c = for_ c (writeCDecl file)

main : IO ()
main = do
  let selfApply = Abs "x" (Var "x" `App` Var "x")
  let omega = selfApply `App` selfApply
  let cOmega = evalState Z $ lcToCProgram omega
  ignore $ withFile "out.c" WriteTruncate
    (\err => printLn err)
    (\file => map pure $ writeC file cOmega)
