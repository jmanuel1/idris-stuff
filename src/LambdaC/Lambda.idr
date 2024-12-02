module LambdaC.Lambda

import Control.Monad.Cont
import Control.Monad.Error.Interface
import Control.Monad.State
import Control.Monad.Writer
import Data.SortedMap
import Data.SortedSet
import Data.Variant
import Derive.Eq
import Derive.Ord
import Derive.Show
import Generics.Derive
import Deriving.Functor
import Deriving.Foldable
import Deriving.Traversable
import LambdaC.FFI
import LambdaC.C

%language ElabReflection

%hide Generics.Derive.Eq
%hide Generics.Derive.Ord
%hide Generics.Derive.Show
%hide Language.Reflection.Syntax.rec
%hide LambdaC.C.Ty

public export
data Ty = CTy (CType Ty) | Closure Ty Ty

%runElab derive "Ty" [Generic, Meta, Eq, Ord, Show]

public export
data LCF rec =
  Var String
  | App rec rec
  | Abs String Ty rec -- variable annotated with C type that is not checked
  | Fix String rec Ty Ty      -- fix f = \x => f (fix f) x ==> f : (a -> b) -> (a -> b), fix : ((a -> b) -> (a -> b)) -> (a -> b)
  | Extern String Ty -- C expression annotated with unchecked type

%default total

export %hint total
lcfFunctor : Functor LCF
lcfFunctor = %runElab derive

export %hint total
lcfFoldable : Foldable LCF
lcfFoldable = %runElab derive

export %hint total
lcfTraversable : Traversable LCF
lcfTraversable = %runElab derive

%default covering

public export covering
LC : Type
LC = Fix LCF

MonadFresh : (Type -> Type) -> Type
MonadFresh m = MonadState (Nat, SortedSet String) m

FreshT : ?
FreshT = StateT (Nat, SortedSet String)

Fresh : ?
Fresh = State (Nat, SortedSet String)

MonadRename : (Type -> Type) -> Type
MonadRename m = (MonadFresh m, MonadState (SortedMap String String) m)

incrementCounter : MonadFresh m => m ()
incrementCounter = modify $ mapFst (+ 1)

covering
genName : MonadFresh m => String -> m String
genName root = do
  modify (mapSnd $ insert root)
  suffix <- map (cast . fst) get
  incrementCounter
  -- TODO: Filter chars
  let gensym = "lc_" ++ root ++ "_" ++ suffix
  if contains gensym !(gets snd)
    then genName root
    else do
      modify (mapSnd $ insert gensym)
      pure gensym

memName : MonadFresh m => String -> m ()
memName name = modify (mapSnd $ insert name)

getCType : MonadState (SortedMap String Ty) m => MonadError String m => String -> m Ty
getCType var = maybe (throwError ("don't know the C type of `" ++ var ++ "`")) pure $ lookup var $ !get

enterBlock : MonadState (SortedMap String b) m => String -> b -> m a -> m a
enterBlock var type block = do
  context <- get
  modify (insert var type)
  result <- block
  modify (const context)
  pure result

covering
rename : Monad m => MonadRename m => String -> m String
rename name = do
  Just name' <- gets (SortedMap.lookup name)
  | Nothing => genName name
  pure name'

||| Rename variables so that they all have unique names that are compatible with
||| C.
covering
renameLCF : Monad m => MonadRename m => Algebra LCF (m LC)
renameLCF (Var str) = map (MkFix . Var) (rename str)
renameLCF (Abs str x y) = do
  name <- rename str
  map (MkFix . Abs name x) $ enterBlock str name y
renameLCF (Fix str x y z) = do
  name <- rename str
  body <- enterBlock str name x
  pure $ MkFix $ Fix name body y z
renameLCF t = map MkFix $ sequence t

namespace ANF
  public export
  data ValueF rec =
    Var String
    | Abs String Ty rec
    | Fix String rec Ty Ty
    | Extern String Ty

  public export
  data ANFF rec =
    Halt (ValueF rec)
    | LetApp String (ValueF rec) (ValueF rec) rec

  public export
  ANF : Type
  ANF = Fix ANFF

  public export
  Value : Type
  Value = ValueF ANF

-- Algorithm based on https://compiler.club/anf-conversion/.
lcfToAnf' : Algebra LCF (FreshT (Cont ANF) Value)
lcfToAnf' (Var str) = do
  memName str
  pure (Var str)
lcfToAnf' (App x y) = do
  x <- x
  y <- y
  name <- genName "anf_app"
  lift $ mapContT (map (MkFix . LetApp name x y)) (pure (Var name))
lcfToAnf' (Abs str x y) = do
  memName str
  y <- y
  pure (Abs str x $ MkFix $ Halt y)
lcfToAnf' (Fix str x y z) = do
  memName str
  x <- x
  pure $ Fix str (MkFix $ Halt x) y z
lcfToAnf' (Extern str x) = pure $ Extern str x

lcfToAnf : LC -> ANF
lcfToAnf = flip runCont (MkFix . Halt) . evalStateT (0, neutral) . cata lcfToAnf'

-- anffToCExp : MonadWriter C m => MonadWriter CStmt m => Algebra ANFF (m ())
-- anffToCExp (Halt (Var v)) = tell $ RawStmt $ "return \{v}"
-- anffToCExp _ = ?fddbd

-- Closure conversion

data ClosedF rec = ClosedAbs String Ty String Ty rec

||| Close all abstractions. (Convert free vars to explicit environments.)
close : MonadFresh m => MonadState (SortedMap String Ty) m => MonadWriter CDecl m => Algebra LCF (m (Fix (AnyF [LCF, ClosedF])))
close (Var v) = pure $ MkFix $ injectF $ Var v
close (Abs x t b) = do
  b <- b
  let free = delete x (freeVars b)
  envName <- genName "close_anf_env"
  envType <- envType free
  let body = grabFreeVarsFromEnv envName free b
  pure $ MkFix $ injectF $ ClosedAbs x t envName envType body
close (Halt (Fix f b s t)) = do
  b <- b
  let free = delete x (freeVars b)
  envName <- genName "close_anf_env"
  envType <- envType free
  let body = grabFreeVarsFromEnv envName free b
  let body = MkFix $ injectF $ Let
  pure $ MkFix $ injectF $ Halt $ ClosedAbs x t envName envType body
