||| https://andraskovacs.github.io/pdfs/2ltt_icfp24.pdf
||| https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/agda-opsem/Interpreter.agda
module LambdaC.TwoLTT

import Control.Monad.Maybe
import Control.Monad.State
import Data.List.Elem
import Data.List.Quantifiers
import Data.Variant.Fix
import Data.Vect
import Data.Vect.Elem

%default total

data U = Val | Comp

data Ty : Type -> U -> Type

ValTy : Type -> Type
ValTy var = Ty var Val

CompTy : Type -> Type
CompTy var = Ty var Comp

data Ty where
  Fun : Ty var Val -> Ty var u -> CompTy var
  Fix : (var -> Ty var Val) -> ValTy var
  Product, Sum : (ds : List $ Ty var Val) -> ValTy var
  -- Only used for recursive ValTys, so supporting only ValTy variables is fine
  TyVar : var -> Ty var Val
  Newtype : (0 tag : Type) -> Ty var u -> Ty var u

One, Zero : ValTy var
One = Product []
Zero = Sum []

0 VarTy : Type -> Type
VarTy tyvar = (0 u : U) -> Ty tyvar u -> Type

data Expr : (0 tyvar : Type) -> VarTy tyvar -> Ty tyvar u -> Type

0 CaseArms : List (Ty tyvar Val) -> VarTy tyvar -> Ty tyvar Val -> List Type
CaseArms ds var mot = map (\d => var _ d -> Expr tyvar var mot) ds

-- http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf, figure 9
data Sub : (0 t1 : var -> Ty var Val) -> ValTy var -> ValTy var -> Type where
  [search t1]
  SubFix : (t1 : var -> var -> ValTy var) -> (forall a. Sub (\a' => t1 a' a) t (t1' a)) -> Sub (\a => Fix (t1 a)) t (Fix t1')
  -- NOTE: Avoid trying to unify against a `map` call by having t2s return the
  -- whole list. The unifier likes this a lot better (see definition of
  -- `TreeExample.leaf`).
  SubSum : Sub t1 t t1' -> (t2s : var -> List (ValTy var)) -> Sub (\a => Sum (t2s a)) t (Sum t2s') -> Sub (\a => Sum (t1 a :: t2s a)) t (Sum (t1' :: t2s'))
  SubProd : Sub t1 t t1' -> (t2s : var -> List (ValTy var)) -> Sub (\a => Product (t2s a)) t (Product t2s') -> Sub (\a => Product (t1 a :: t2s a)) t (Product (t1' :: t2s'))
  SubReplace : Sub (\a => TyVar a) t t
  SubConst : Sub (\_ => t1) t t1
  SubNewtype : Sub t1 t t1' -> Sub (\a => Newtype tag (t1 a)) t (Newtype tag t1')

-- http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
data Expr where
  LetRec : {0 var : VarTy tyvar} -> (a : CompTy tyvar) -> (t : var _ a -> Expr tyvar var a) -> (u : var _ a -> Expr tyvar var ty) -> Expr tyvar var ty
  Let : {0 var : VarTy tyvar} -> (a : Ty tyvar u) -> (t : Expr tyvar var a) -> (u : var _ a -> Expr tyvar var ty) -> Expr tyvar var ty
  -- Not having multi-way case in syntax so that Idris can see totality of Expr
  Absurd : Expr tyvar var Zero -> Expr tyvar var a
  Match : Expr tyvar var (Sum (d :: ds)) -> (var _ d -> Expr tyvar var a) -> (var _ (Sum ds) -> Expr tyvar var a) -> Expr tyvar var a
  Lam : {0 var : VarTy tyvar} -> (a : ValTy tyvar) -> (t : var _ a -> Expr tyvar var b) -> Expr {u = Comp} tyvar var (Fun a b)
  Var : {0 var : VarTy tyvar} -> var _ ty -> Expr tyvar var ty
  App : (f : Expr tyvar var (Fun a b)) -> (arg : Expr tyvar var a) -> Expr tyvar var b
  Left : {0 var : VarTy tyvar} -> Expr tyvar var a -> Expr tyvar var (Sum (a :: b))
  Right : {0 var : VarTy tyvar} -> Expr tyvar var (Sum b) -> Expr tyvar var (Sum (a :: b))
  TT : Expr tyvar var One
  Prod : Expr tyvar var a -> Expr tyvar var (Product b) -> Expr tyvar var (Product (a :: b))
  First : Expr tyvar var (Product (a :: as)) -> Expr tyvar var a
  Rest : Expr tyvar var (Product (a :: as)) -> Expr tyvar var (Product as)
  -- Represent coercions explicitly in syntax
  Wrap : (0 tag : Type) -> Expr tyvar var a -> Expr tyvar var (Newtype tag a)
  Unwrap : Expr tyvar var (Newtype tag a) -> Expr tyvar var a
  Roll : Expr tyvar var unroll -> (0 sub : Sub f (Fix f) unroll) -> Expr tyvar var (Fix f)
  Unroll : Expr tyvar var (Fix f) -> (0 sub : Sub f (Fix f) unroll) -> Expr tyvar var unroll

Case : {0 var : VarTy tyvar} -> {ds : _} -> (scrutinee : Expr tyvar var (Sum ds)) -> HList (CaseArms ds var motive) -> Expr tyvar var motive
Case {ds = []} e [] = Absurd e
Case {ds = (_ :: _)} e (arm :: arms) = Match e arm (\right => Case (Var right) arms)

0 lift : Ty tyvar u -> VarTy tyvar -> Type
lift a var = Expr tyvar var a

record Gen (0 u : U) (0 var : VarTy tyvar) (a : Type) where
  constructor MkGen
  unGen : {0 r : Ty tyvar u} -> (a -> lift r var) -> lift r var

interface Monad m => MonadGen (0 u : U) (0 var : VarTy tyvar) m | m where
  liftGen : Gen u var a -> m a

Functor (Gen u var) where
  map f fa = MkGen $ \k => unGen fa $ \fa => k (f fa)

Applicative (Gen u var) where
  pure a = MkGen $ \k => k a
  fa <*> a = MkGen $ \k => unGen fa $ \fa => unGen a $ \a => k (fa a)

covering
Monad (Gen u var) where
  m >>= f = MkGen $ \k => unGen m (\a => unGen (f a) k)

MonadGen u var (Gen u var) where
  liftGen gen = gen

-- https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/haskell-cftt/CFTT/Improve.hs#L17
interface MonadGen Val var m => Improve (0 tyvar : Type) (0 var : VarTy tyvar) (0 f : ValTy tyvar -> Ty tyvar u) (0 m : Type -> Type) | m where
  up : {a : ValTy tyvar} -> lift (f a) var -> m (lift a var)
  down : {a : ValTy tyvar} -> m (lift a var) -> lift (f a) var

interface Split (0 tyvar : Type) (0 a : ValTy tyvar) | a where
  0 SplitTo : VarTy tyvar -> Type
  split : {0 var : VarTy tyvar} -> lift a var -> Gen Val var (SplitTo var)

data IdentityTag : Type where

Identity : ValTy tyvar -> ValTy tyvar
Identity a = Newtype IdentityTag a

Improve tyvar var Identity (Gen Val var) where
  up x = pure (Unwrap x)
  down x = unGen x (Wrap _)

List : ValTy tyvar -> ValTy tyvar
List a = Fix (\list => Sum [One, Product [a, TyVar list]])

{a : ValTy tyvar} -> Split tyvar (List a) where
  SplitTo var = Maybe (lift a var, lift (List a) var)
  split as = MkGen $ \k => Case (Unroll as %search) [\_ => k Nothing, \cons => k (Just (First (Var cons), First (Rest (Var cons))))]

namespace TreeExample
  TreeF : ValTy tyvar -> tyvar -> ValTy tyvar
  TreeF a = (\tree => Sum [One, Product [a, TyVar tree, TyVar tree]])

  Tree : ValTy tyvar -> ValTy tyvar
  Tree a = Fix $ TreeF a

  leaf : Expr tyvar var (Tree a)
  leaf = Roll (Left TT) %search

  node : Expr tyvar var a -> (l, r : Expr tyvar var (Tree a)) -> Expr tyvar var (Tree a)
  node n l r =
    Roll (Right $ Left $ Prod n (Prod l $ Prod r TT)) %search

  data TreeSplit : (0 var : VarTy tyvar) -> ValTy tyvar -> Type where
    Leaf : TreeSplit var a
    Node : Expr tyvar var a -> (l, r : Expr tyvar var (Tree a)) -> TreeSplit var a

  {a : _} -> Split tyvar (Tree {tyvar} a) where
    SplitTo var = TreeSplit var a
    split as = MkGen $ \k => Case (Unroll as %search) [\_ => k Leaf, \node => k (Node (First (Var node)) (First (Rest (Var node))) (First (Rest (Rest (Var node)))))]

  Nat : ValTy tyVar
  Nat = Fix (\nat => Sum [One, TyVar nat])

  data StateTTag : Type where

  StateT : ValTy var -> (ValTy var -> ValTy var) -> ValTy var -> CompTy var
  StateT s m a = Newtype StateTTag $ Fun s (m (Product [a, s]))

  Maybe : ValTy tyvar -> ValTy tyvar
  Maybe a = Sum [One, a]

  nothing : Expr tyvar var (Maybe a)
  nothing = Left TT

  just : Expr tyvar var a -> Expr tyvar var (Maybe a)
  just a = Right $ Left a

  {a : _} -> Split tyvar (Maybe a) where
    SplitTo var = Maybe (Expr tyvar var a)
    split ma = MkGen $ \k => Case ma [\_ => k Nothing, \a => k (Just (Var a))]

  data MaybeTTag : Type where

  public export
  MaybeT : (ValTy var -> Ty var u) -> ValTy var -> Ty var u
  MaybeT m a = Newtype MaybeTTag $ m (Maybe a)

  runMaybeT : Expr tyvar var (MaybeT m a) -> Expr tyvar var (m (Maybe a))
  runMaybeT = Unwrap

  MkMaybeT : Expr tyvar var (m (Maybe a)) -> Expr tyvar var (MaybeT m a)
  MkMaybeT = Wrap _

  MonadGen u var m => MonadGen u var (MaybeT m) where
    liftGen = lift . liftGen

  -- NOTE: For some reason, auto search can't find this, and it's rather
  -- annoying.
  [improveMaybeInstance]
  Improve tyvar var f m => Improve tyvar var (MaybeT f) (MaybeT m) where
    up x = MkMaybeT $ do
      ma <- up $ runMaybeT {m = f} x
      liftGen $ split ma
    down (MkMaybeT x) = MkMaybeT {m = f} $ down $ x >>= \case
      Nothing => pure nothing
      Just a => pure (just a)

  fail : Improve tyvar var f m => {a : _} -> Expr tyvar var (MaybeT f a)
  fail = down @{improveMaybeInstance} {f = MaybeT f, m = MaybeT m} nothing

  MonadGen u var m => MonadGen u var (StateT s m) where
    liftGen = lift . liftGen

  {s : _} -> Improve tyvar var f m => Improve tyvar var (StateT s f) (StateT (lift s var) m) where
    up x = ST $ \s => do
      h <- up {m = m} (App (Unwrap x) s)
      pure (First (Rest h), First h)
    down x = Wrap _ $ Lam _ $ \s => down {m = m} $ do
      (s, a) <- runStateT (Var s) x
      pure (Prod a (Prod s TT))

  Bool : ValTy var
  Bool = Sum [One, One]

  true : Expr tyvar var Bool
  true = Left TT

  false : Expr tyvar var Bool
  false = Right $ Left TT

  Split tyvar Nat where
    SplitTo var = Maybe (Expr tyvar var Nat)
    split n = MkGen $ \k => Case (Unroll n %search) [\_ => k Nothing, \n' => k (Just (Var n'))]

  (==) : Expr tyvar var (Fun Nat (Fun Nat Bool))
  (==) = flip (LetRec _) Var $ \eq =>
    Lam _ $ \n => Lam _ $ \m =>
      unGen (do
        case (!(split (Var n)), !(split (Var m))) of
          (Nothing, Nothing) => pure true
          (Just n', Just m') => pure $ App (App (Var eq) n') m'
          _ => pure false) id

  {-
  f : Expr tyvar var (Fun (Tree Nat) (StateT (List Nat) (MaybeT Identity) (Tree Nat)))
  f = LetRec _ (\f =>
    Lam (Tree Nat) $ \t => down $ do
      treeSplit <- liftGen $ split (the (Expr tyvar var ( $ Tree Nat)) $ Var t)
      case treeSplit of
        Leaf => pure leaf
        Node n l r => do
          case !(liftGen $ split (n == 0)) of
            True => fail
            False => pure ()
          ns <- get
          n <- join $ case !(liftGen $ split $ the (Expr tyvar var ( (List Nat))) ns) of
            Nothing => pure n
            Just (n, ns) => do
              put ns
              pure n
          l <- up (App (Var f) l)
          r <- up (App (Var f) r)
          pure (node n l r)) Var
