module LambdaC.Effect

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.Identity
import Control.Monad.State
import Control.Relation
import Data.Path
import Data.SortedMap
import Deriving.Show
import LambdaC
import LambdaC.FFI

%hide Language.Reflection.TTImp.Clause

%language ElabReflection
%default total

public export
data CompilationStage = Effect | C | ADT

data DirectlyAbove : Rel CompilationStage where
  EffectADT : DirectlyAbove Effect ADT
  ADTC : DirectlyAbove ADT C

export
AtLeast : Rel CompilationStage
AtLeast = Path DirectlyAbove

public export
data Ty : CompilationStage -> Type where
  CTy : CType (Ty stage) -> Ty stage
  UnitTy : {auto 0 _ : stage `AtLeast` ADT} -> Ty stage
  VoidTy : {auto 0 _ : stage `AtLeast` ADT} -> Ty stage
  (:+) : {auto 0 _ : stage `AtLeast` ADT} -> Ty stage -> Ty stage -> Ty stage
  (:*) : {auto 0 _ : stage `AtLeast` ADT} -> Ty stage -> Ty stage -> Ty stage
  -- closure
  (:->) : {auto 0 _ : stage `AtLeast` ADT} -> List (Ty stage) -> Ty stage -> Ty stage
  NamedTy : String -> Ty stage

%hint total
tyShow : Show (Ty stage)
tyShow = %runElab derive

public export
data Expr : (0 stage : CompilationStage) -> Type

export
varRep : CompilationStage -> Type
varRep Effect = Expr Effect
varRep ADT = Expr ADT
varRep C = String

public export
record ArgumentAndResumption (0 stage : CompilationStage) where {
  constructor MkArgAndResume
  {auto 0 stageEv : stage `AtLeast` Effect}
  arg : varRep stage
  resume : varRep stage
}

-- op(x) -> e; h
public export
record Handler (0 stage : CompilationStage) where {
  constructor MkHandler
  {auto 0 stageEv : stage `AtLeast` Effect}
  op : String  -- op
  arg : String -- x
  argType : Ty stage
  resumeArgType : Ty stage
  body : ArgumentAndResumption stage -> Expr stage -- e
}

public export
data Clause : (0 stage : CompilationStage) -> {auto 0 stageEv : stage `AtLeast` Effect} -> Type where
  Return : Ty stage -> (varRep stage -> Expr stage) -> Clause @{stageEv} stage -- return (x: t) -> e
  OpHandler : Handler stage -> Clause @{stageEv} stage -> Clause @{stageEv} stage -- op(x) -> e; h

public export
record ExportDecl (0 stage : CompilationStage) where {
  name : String
  ty : varRep C
  expr : Expr stage
}

data Expr : (0 stage : CompilationStage) -> Type where
  (:$) : Expr stage -> Expr stage -> Expr stage -- e(e)
  Val : Expr stage -> Ty stage -> (varRep stage -> Expr stage) -> Expr stage-- val x = e; e
  Handle : {auto 0 _ : stage `AtLeast` Effect} -> Clause stage -> Expr stage -> Expr stage -- handle{h}e
  -- values
  LocalVar : varRep stage -> Expr stage
  GlobalVar : String -> Expr stage
  Extern : String -> varRep C -> Expr stage -- C expression annotated with unchecked C type
  Export : ExportDecl stage -> Expr stage -> Expr stage
  Op : {auto 0 _ : stage `AtLeast` Effect} -> String -> Ty stage -> Expr stage -- op
  (:\) : Ty stage -> (varRep stage -> Expr stage) -> Expr stage
  -- recursion
  Fix : Ty stage -> Ty stage -> (varRep stage -> Expr stage) -> Expr stage -- fix f = \x => f (fix f) x ==> f : (a -> b) -> (a -> b), fix : ((a -> b) -> (a -> b)) -> (a -> b)
  TyDecl : Ty stage -> (String -> Expr stage) -> Expr stage

record ContPassingStyleResult m where
  constructor MkContPSResult
  expr : (Expr -> m Expr) -> m Expr
  originalType : CType

getReturnArgType : Clause -> CType
getReturnArgType (Return _ t _) = t
getReturnArgType (OpHandler _ clause) = getReturnArgType clause

mutual
  clauseToContPassingStyle : MonadState CompilerState m => MonadError String m => CType -> (Expr -> m Expr) -> Clause -> m (Clause, CType)
  clauseToContPassingStyle resType k (Return x t e) = do
    e' <- enterBlock x t $ toContPassingStyle resType e
    pure (Return x t !(e'.expr k), e'.originalType)
  clauseToContPassingStyle resType k (OpHandler (MkHandler op x t resume resumeArgType e) clause) = do
    (clause', retType) <- clauseToContPassingStyle resType k clause
    e' <- enterBlock x t $ enterBlock resume (FunType resumeArgType retType "") $ toContPassingStyle resType e
    -- QUESTION: What does this mean for resume?
    pure (OpHandler (MkHandler op x t resume resumeArgType !(e'.expr k)) clause', retType)

  -- I'm not going to define a handle_l primitive because I'm not going to track the effects
  -- It's kind of like there's only one big effect with any operations you want
  -- TODO: generate introduced names to avoid capturing existing names, or do capture-avoidance
  toContPassingStyle : MonadState CompilerState m => MonadError String m => CType -> Expr -> m (ContPassingStyleResult m)
  -- CON (constants)
  toContPassingStyle resType e@(Extern _ t) = pure $ MkContPSResult (\k => k e) t
  toContPassingStyle resType e@(Op _ t) = pure $ MkContPSResult (\k => k e) t
  -- VAR (variables)
  toContPassingStyle resType e@(Var v) = do
    t <- getCType v
    pure $ MkContPSResult (\k => k e) t
  -- VAL
  toContPassingStyle resType (Val v t e rest) = do
    e' <- toContPassingStyle t e
    rest' <- enterBlock v t $ toContPassingStyle resType rest
    pure $ MkContPSResult
      (\k => e'.expr (\x => pure $ Val v t x !(rest'.expr k)))
      rest'.originalType
  -- HANDLE (handlers)
  toContPassingStyle resType (Handle clause e) = do
    let clause' = \k => clauseToContPassingStyle resType k clause
    let returnArgType = getReturnArgType clause
    e' <- toContPassingStyle returnArgType e
    pure $ MkContPSResult
      (\k => do
        (clause'', clauseRetType) <- clause' k
        pure $ Handle clause'' !(e'.expr (\x => pure x)))
      -- An unfortunate way to get the return type of the clause.
      (snd !(clause' (\x => pure x)))
  -- applications
  toContPassingStyle resType (App e1 e2) = do
    e2' <- toContPassingStyle resType e2
    e1' <- toContPassingStyle (FunType e2'.originalType resType "") e1
    -- TODO: Take type from e1 instead of resType?
    case e1'.originalType of
      -- APP
      ExternType (FunType _ retType _) => pure $ MkContPSResult
        (\k => e1'.expr (\f => e2'.expr (\x => k (f `App` x))))
        retType
      -- APP-CPS
      FunType _ retType _ => pure $ MkContPSResult
        (\k => e1'.expr (\f => e2'.expr (\x => do
          pure $ (f `App` x) `App` Abs "y" retType !(k (Var "y")))))
        retType
      _ => throwError "only functions can be applied to arguments"
  -- LAM-CPS (abstractions)
  toContPassingStyle resType expr@(Abs x t e) = do
    (FunType _ eResType envTypeName) <- pure resType
    | t => throwError $ "resType must be a function type for abstractions: " ++ show t ++ ", type of " ++ show expr
    e' <- enterBlock x t $ toContPassingStyle eResType e
    pure $ MkContPSResult
      (\k => k (Abs x t (Abs "k" (FunType e'.originalType "void" "") !(e'.expr (\x => pure $ Var "k" `App` x)))))
      (FunType t e'.originalType envTypeName)
  toContPassingStyle resType (Fix f e argType retType) = do
    let fixType = FunType argType retType ""
    e' <- enterBlock f fixType $ toContPassingStyle fixType e
    let contType = FunType retType "void" ""
    -- TODO: What if e evaluates to an ExternType?
    pure $ MkContPSResult
      (\k => k (Fix f (Abs "x" argType (Abs "k" contType !(e'.expr (\x => pure $ (x `App` Var "x") `App` Var "k")))) argType (FunType contType "void" "")))
      fixType

export
toContPassingStyleConcrete : CType -> Expr -> Either String Expr
toContPassingStyleConcrete resType e = do
  let runEffects = \a => \m => runIdentity $ runEitherT {e=String} {m=Identity} {a} (evalStateT (Z, the (SortedMap String CType) empty) m)
  e' <- runEffects (ContPassingStyleResult _) $ toContPassingStyle resType e
  let exitExtern = Extern "exit(-1)" $ ExternType "void"
  let exitExternFun = Abs "x" e'.originalType exitExtern
  runEffects Expr (e'.expr (\x => case e'.originalType of
    ExternType _ => pure $ exitExternFun `App` x
    RawType _ => pure $ exitExternFun `App` x
    _ => pure $ x `App` exitExternFun))

{- Examples -}

0 example1 : toContPassingStyleConcrete "int" ((Extern "prim_succ" (ExternType $ FunType "int" "int" "struct prim_fun_closure")) `App` ((Extern "prim_pred" (ExternType $ FunType "int" "int" "struct prim_fun_closure")) `App` (Extern "0" $ ExternType "int"))) = Right (App (Abs "x" (RawType "int") (Extern "exit(-1)" (ExternType (RawType "void")))) (App (Extern "prim_succ" (ExternType (FunType (RawType "int") (RawType "int") "struct prim_fun_closure"))) (App (Extern "prim_pred" (ExternType (FunType (RawType "int") (RawType "int") "struct prim_fun_closure"))) (Extern "0" (ExternType (RawType "int"))))))

0 example2 : (toContPassingStyleConcrete (FunType "int" "int" "") $ Handle (OpHandler (MkHandler "get" "unused" "void" "resume" "int" (Abs "s" "int" ((Var "resume" `App` Var "s") `App` Var "s"))) (OpHandler (MkHandler "set" "x" "int" "resume" "void" (Abs "s" "int" ((Var "resume" `App` Extern "void" "void") `App` Var "x"))) (Return "x" "int" (Abs "s" "int" (Var "x"))))) (Val "unused" "void" ((Op "set" (FunType "int" "void" "") `App` Extern "5" "int")) (Op "get" (FunType "void" "int" "") `App` Extern "void" "void"))) === Right (Handle (OpHandler (MkHandler "get" "unused" (RawType "void") "resume" (RawType "int") (App (Abs "s" (RawType "int") (Abs "k" (FunType (RawType "int") (RawType "void") "") (App (App (Var "resume") (Var "s")) (Abs "y" (FunType (RawType "int") (RawType "int") "") (App (App (Var "y") (Var "s")) (Abs "y" (RawType "int") (App (Var "k") (Var "y")))))))) (Abs "x" (FunType (RawType "int") (RawType "int") "") (Extern "exit(-1)" (ExternType (RawType "void")))))) (OpHandler (MkHandler "set" "x" (RawType "int") "resume" (RawType "void") (App (Abs "s" (RawType "int") (Abs "k" (FunType (RawType "int") (RawType "void") "") (App (App (Var "resume") (Extern "void" (RawType "void"))) (Abs "y" (FunType (RawType "int") (RawType "int") "") (App (App (Var "y") (Var "x")) (Abs "y" (RawType "int") (App (Var "k") (Var "y")))))))) (Abs "x" (FunType (RawType "int") (RawType "int") "") (Extern "exit(-1)" (ExternType (RawType "void")))))) (Return "x" (RawType "int") (App (Abs "s" (RawType "int") (Abs "k" (FunType (RawType "int") (RawType "void") "") (App (Var "k") (Var "x")))) (Abs "x" (FunType (RawType "int") (RawType "int") "") (Extern "exit(-1)" (ExternType (RawType "void")))))))) (App (App (Op "set" (FunType (RawType "int") (RawType "void") "")) (Extern "5" (RawType "int"))) (Abs "y" (RawType "void") (Val "unused" (RawType "void") (Var "y") (App (App (Op "get" (FunType (RawType "void") (RawType "int") "")) (Extern "void" (RawType "void"))) (Abs "y" (RawType "int") (Var "y")))))))

0 example3 : (toContPassingStyleConcrete (FunType "int" "int" "") $ Fix "f" (Var "f") "int" "int") === Right (App (Fix "f" (Abs "x" (RawType "int") (Abs "k" (FunType (RawType "int") (RawType "void") "") (App (App (Var "f") (Var "x")) (Var "k")))) (RawType "int") (FunType (FunType (RawType "int") (RawType "void") "") (RawType "void") "")) (Abs "x" (FunType (RawType "int") (RawType "int") "") (Extern "exit(-1)" (ExternType (RawType "void")))))

evidenceVectorVarName : String
evidenceVectorVarName = "lc_evidence_vector"

evidenceVectorVar : Expr
evidenceVectorVar = Var evidenceVectorVarName

abstractOverEvidenceVector : Expr -> Expr
abstractOverEvidenceVector e = Abs evidenceVectorVarName "struct lc_evidence_vector" e

{-
https://rust-unofficial.github.io/too-many-lists/infinity-stack-allocated.html
-}

consEvidence : Expr -> Expr -> Expr
consEvidence evidenceHead evidenceTail = (Extern "lc_evidence_vector_cons" (ExternType (FunType "struct lc_evidence_vector" "struct lc_evidence_vector *" "")) `App` evidenceHead) `App` (Extern "LC_ADDRESS_OF" (ExternType (FunType "struct lc_evidence_vector" "struct lc_evidence_vector *" "")) `App` evidenceTail)

createReturnEvidence : Expr -> Expr
createReturnEvidence returnHandlerFun = Extern "lc_evidence_vector_create_return_evidence" (ExternType (FunType "void *" "struct lc_evidence_vector" "")) `App` returnHandlerFun

createOpEvidence : String -> Expr -> Expr
createOpEvidence op opHandlerFun = (Extern "lc_evidence_vector_create_op_evidence" (ExternType (FunType "const char *" (FunType "void *" "struct lc_evidence_vector" "") "")) `App` op) `App` opHandlerFun

mutual
  extendEvidenceVector : MonadState CompilerState m => MonadError String m => Clause -> Expr -> m (Expr, Expr)
  extendEvidenceVector (Return x t e) evidence = do
    e' <- toEvidencePassingStyle e
    pure $ (consEvidence (createReturnEvidence (Abs x t (e' `App` evidenceVectorVar))) evidence, _)
  extendEvidenceVector (OpHandler (MkHandler op arg argType resume resumeArgType body) clause) evidence = do
    body' <- toEvidencePassingStyle body
    (evidence', t) <- extendEvidenceVector clause evidence
    pure $ (consEvidence (createOpEvidence op (Abs arg argType (Abs resume (FunType resumeArgType t "") (body' `App` evidenceVectorVar)))) evidence', t)

  toEvidencePassingStyle : MonadState CompilerState m => MonadError String m => Expr -> m Expr
  toEvidencePassingStyle (App x y) = do
    x' <- toEvidencePassingStyle x
    y' <- toEvidencePassingStyle y
    pure $ abstractOverEvidenceVector $ (x' `App` evidenceVectorVar) `App` (y' `App` evidenceVectorVar)
  toEvidencePassingStyle (Val x t e1 e2) = do
    e1' <- toEvidencePassingStyle e1
    e2' <- toEvidencePassingStyle e2
    pure $ abstractOverEvidenceVector $ Val x t (e1' `App` evidenceVectorVar) (e2' `App` evidenceVectorVar)
  toEvidencePassingStyle (Handle clause e) = do
    e' <- toEvidencePassingStyle e
    pure $ abstractOverEvidenceVector $ Val "lc_new_evidence_vector" "struct lc_evidence_vector" !(extendEvidenceVector clause evidenceVectorVar) (e' `App` Var "lc_new_evidence_vector")
  toEvidencePassingStyle (Var str) = ?hole_3
  toEvidencePassingStyle (Extern str x) = ?hole_4
  toEvidencePassingStyle (Op str x) = ?hole_5
  toEvidencePassingStyle (Abs str x y) = ?hole_6
  toEvidencePassingStyle (Fix str x y z) = ?hole_7

-- toCapPassingStyle : Expr -> Expr
-- toCapPassingStyle (App x y) = App (toCapPassingStyle x) (toCapPassingStyle y)
-- toCapPassingStyle (Val v t y z) = Val v t (toCapPassingStyle y) (toCapPassingStyle z)
-- toCapPassingStyle (Handle x y) = ?hole_2
-- toCapPassingStyle (Var str) = ?hole_3
-- toCapPassingStyle (Extern str x) = ?hole_4
-- toCapPassingStyle (Op str x) = ?hole_5
-- toCapPassingStyle (Abs str x y) = ?hole_6
-- toCapPassingStyle (Fix str x y z) = ?hole_7

-- desugar : Expr -> LC
