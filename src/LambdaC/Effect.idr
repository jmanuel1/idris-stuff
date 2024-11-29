||| High-level language with effects and handlers, expressed as a DSL.
||| Gentrification Gone too Far?: Affordable 2nd-Class Values for Fun and (Co-)Effect
||| https://www.cs.purdue.edu/homes/rompf/papers/osvald-oopsla16.pdf

module LambdaC.Effect

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.Identity
import Control.Monad.State
import Control.Relation
import Data.Path
import Data.SortedMap
import Data.Variant
import Data.Vect
import Derive.Show
import Deriving.Show
import Generics.Derive
import LambdaC
import LambdaC.FFI

%hide Language.Reflection.TTImp.Clause
%hide Generics.Derive.Show

%language ElabReflection
%default total

public export
data ResumeKind = Tail

%hint total
resumeKindShow : Show ResumeKind
resumeKindShow = %runElab derive

%runElab derive "ResumeKind" [Generic, DecEq]

data NameKind = NKType | NKValue

data Context : Type

data Ty : Context -> Type

public export
data Context where
  Lin : Context
  (:<) : (context : Context) -> (String, Ty context, NameKind) -> Context

public export
data TyIsNamed : String -> Context -> Type where
  TyHere : (0 n : String) -> TyIsNamed n (context :< (n, _, NKType))
  TyThere : TyIsNamed n context -> TyIsNamed n (context :< _)

%builtin Natural TyIsNamed

export infixr 1 :->

public export
data Ty : Context -> Type where
  CTy : CType (Ty context) -> Ty context
  UnitTy : Ty _
  -- Empty sum is Void
  SumTy : List (String, Ty context) -> Ty context
  RecordTy : List (String, Ty context) -> Ty context
  -- closure
  (:->) : List (Ty context) -> Ty context -> Ty context
  EffectTy : List (String, Ty context, ResumeKind) -> Ty context
  NamedTy : (0 name : String) -> TyIsNamed name context -> Ty context
  ComputationTy : List (Ty context) -> Ty context -> Ty context

Injective CTy where
  injective = ?fgbfg

Injective SumTy where
  injective = ?fgbfg1

Injective RecordTy where
  injective = ?fgbfg11

Biinjective (:->) where
  biinjective = ?fghgdh

Injective EffectTy where
  injective = ?fgbfg112

Biinjective ComputationTy where
  biinjective = ?fghgdh3


export partial
DecEq (Ty ctxt) where
  decEq (CTy x) (CTy y) = decEqCong $ decEq x y
  decEq UnitTy UnitTy = Yes Refl
  decEq (SumTy xs) (SumTy ys) = decEqCong $ decEq xs ys
  decEq (RecordTy xs) (RecordTy ys) = decEqCong $ decEq xs ys
  decEq (xs :-> x) (ys :-> y) = decEqCong2 (decEq xs ys) (decEq x y)
  decEq (EffectTy xs) (EffectTy ys) = decEqCong $ decEq xs ys
  decEq (NamedTy name x) (NamedTy name' y) = ?hgdh --decEqCong2 (decEq name name') (decEq x y)
  decEq (ComputationTy xs x) (ComputationTy ys y) = decEqCong2 (decEq xs ys) (decEq x y)
  -- cheating
  decEq _ _ = No (\_ => assert_total $ idris_crash "impossible")

export
(ctxt : Context) => Show (Ty ctxt) where
  showPrec d (CTy x) = assert_total $ showCon d "CTy" $ showArg x
  showPrec d UnitTy = "UnitTy"
  showPrec d (SumTy xs) = assert_total $ showCon d "SumTy" $ showArg xs
  showPrec d (RecordTy xs) = assert_total $ showCon d "RecordTy" $ showArg xs
  showPrec d (xs :-> x) = ?ghnhfgn_4
  showPrec d (EffectTy xs) = ?ghnhfgn_5
  showPrec d (NamedTy name x) = ?ghnhfgn_6
  showPrec d (ComputationTy xs x) = ?ghnhfgn_7

public export
data Operation : Context -> Type where
  MkOperation : String -> Ty context -> ResumeKind -> Operation context

||| Effect declaration.
public export
data EffectDecl : Context -> Type where
  EDGeneral : (name : String) -> List (Operation context) -> EffectDecl context

effectTy : List (Operation context) -> List (String, Ty context, ResumeKind)
effectTy ops = map (\(MkOperation n t r) => (n, t, r)) ops

public export
interface Weaken (t : Context -> Type) where
  total
  weaken : t c -> t (c :< b)

-- Weaken (TyIsNamed n) where
--   weaken i = TyThere i

export
Weaken Ty where
  weaken (CTy t) = CTy $ assert_total $ map weaken t
  weaken UnitTy = UnitTy
  weaken (SumTy alts) = SumTy (assert_total $ map (mapSnd weaken) alts)
  weaken (RecordTy alts) = RecordTy (assert_total $ map (mapSnd weaken) alts)
  weaken (params :-> ret) = assert_total $ map weaken params :-> weaken ret
  weaken (EffectTy ops) = EffectTy (assert_total $ map (\(n, t, r) => (n, weaken t, r)) ops)
  weaken (NamedTy n i) = NamedTy n (TyThere i)
  weaken (ComputationTy effs ty) = ComputationTy (assert_total $ map weaken effs) (weaken ty)

opsExtend : (context : Context) -> List (String, Ty context, ResumeKind) -> Context
opsExtend c [] = c
opsExtend c ((n, t, r) :: ops) = opsExtend (c :< (n, t, NKValue)) (assert_smaller ops $ map (mapSnd (mapFst weaken)) ops)

export
opsWeaken : (context : Context) -> (ops : List (String, Ty context, ResumeKind)) -> Ty context -> Ty (opsExtend context ops)
opsWeaken c [] ty = ty
opsWeaken c ((n, t, r) :: ops) ty =
  opsWeaken (c :< (n, t, NKValue)) (assert_smaller ops $ map (mapSnd (mapFst weaken)) ops) (weaken ty)

valExtend : (context : Context) -> List (String, Ty context) -> Context
valExtend c [] = c
valExtend c ((n, t) :: ops) = valExtend (c :< (n, t, NKValue)) (assert_smaller ops $ map (mapSnd weaken) ops)

export
valWeaken : (context : Context) -> (bindings : List (String, Ty context)) -> Ty context -> Ty (valExtend context bindings)
valWeaken context [] ty = ty
valWeaken c o@((n, t) :: ops) ty = valWeaken (c :< (n, t, NKValue)) (assert_smaller o $ map (mapSnd weaken) ops) (weaken ty)

effectExtend : (context : Context) -> EffectDecl context -> Context
effectExtend ctxt (EDGeneral name ops) =
  let ty = effectTy ops in
  opsExtend (ctxt :< (name, EffectTy ty, NKType)) (map (mapSnd (mapFst weaken)) ty)

export
effectWeaken : (context : Context) -> (eff : EffectDecl context) -> Ty context -> Ty (effectExtend context eff)
effectWeaken ctxt (EDGeneral name ops) ty =
  opsWeaken (ctxt :< (name, EffectTy (effectTy ops), NKType)) (map (mapSnd (mapFst weaken)) (effectTy ops)) (weaken ty)

public export
data Block : (ctxt : Context) -> Ty ctxt -> Type

public export
record Handler (context : Context) where {
  constructor MkHandler
  op : String  -- op
  args : List (String, Ty context) -- x
  retTy : Ty (valExtend context args)
  body : Block (valExtend context args) retTy -- e
}

public export
data Handle : (ctxt : Context) -> Ty ctxt -> Type where
  HGeneral : (effect : TyIsNamed n context) -> List (Handler context) -> Block context (ComputationTy (eff :: effs) ty) -> Handle context (ComputationTy effs ty)

export infixr 0 :$ -- same as `$`
export infixr 0 :\ -- QUESTION: zero?

public export
data Expr : (ctxt : Context) -> Ty ctxt -> Type where
  EInt : (sign : Signedness) -> (sz : Size) -> Integer -> Expr _ (CTy (TInt sign sz))
  EHandle : Handle context ty -> Expr context ty
  EPure : Expr context ty -> Expr context (ComputationTy eff ty)
  EInject : Expr context (ComputationTy effs ty) -> Subset effs effs2 -> Expr context (ComputationTy effs2 ty)
  (:$) : {0 args : _} -> Expr context (args :-> ret) -> All (Expr context) args -> Expr context ret
  EAddrOf : Expr context ty -> Expr context (CTy (TPtr ty))

public export
data Def : Context -> Type where
  DefExtern : (name : String) -> (ty : Ty context) -> (cName : String) -> (cTy : CType (Ty context)) -> Def context
  DefGeneral : (name : String) -> (ty : Ty context) -> (init : Block context ty) -> Def context

defExtend : (context : Context) -> Def context -> Context
defExtend ctxt (DefExtern name ty _ _) =
  ctxt :< (name, ty, NKValue)
defExtend ctxt (DefGeneral name ty _) =
  ctxt :< (name, ty, NKValue)

export
defWeaken : (context : Context) -> (def : Def context) -> Ty context -> Ty (defExtend context def)
defWeaken context (DefExtern name x cName cTy) ty = weaken ty
defWeaken context (DefGeneral name x init) ty = weaken ty

public export
record Fun (context : Context) where
  constructor MkFun
  name : String
  params : List (String, Ty context)
  retTy : Ty context
  body : Block (valExtend context params) (valWeaken context params retTy)

funExtend : (context : Context) -> Fun context -> Context
funExtend context fun = context :< (fun.name, map snd fun.params :-> fun.retTy, NKValue)

export
funWeaken : (context : Context) -> (fun : Fun context) -> Ty context -> Ty (funExtend context fun)
funWeaken context fun ty = weaken ty

public export
data Block : (ctxt : Context) -> Ty ctxt -> Type where
  BNil : Block _ UnitTy
  BEffectDecl : {0 ty : _} -> (eff : EffectDecl context) -> Block (effectExtend context eff) (effectWeaken context eff ty) -> Block context ty
  BDef : {0 ty : _} -> (def : Def context) -> Block (defExtend context def) (defWeaken context def ty) -> Block context ty
  BFun : {0 ty : _} -> (fun : Fun context) -> Block (funExtend context fun) (funWeaken context fun ty) -> Block context ty
  BExpr : {0 ty : _} -> Expr context ty -> Block context ty2 -> Block context ty2
  BExprRet : {0 ty : _} -> Expr context ty -> Block context ty
