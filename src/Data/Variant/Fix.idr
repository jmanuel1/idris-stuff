module Data.Variant.Fix

public export covering
data Fix : (Type -> Type) -> Type where
  MkFix : f (Fix f) -> Fix f

-- https://github.com/vmchale/recursion_schemes/blob/master/Data/Functor/Foldable/Instances.idr#L31
-- Mu is the least fixed point represented as the catamorphism. I find it
-- harder to think about, so I don't think I'll use it. Idris accepts it as
-- total though, unlike Fix.
public export total
data Mu : (Type -> Type) -> Type where
  MuF : ({0 a : Type} -> (f a -> a) -> a) -> Mu f

export covering
[showFix] Show (f (Fix f)) => Show (Fix f) where
  showPrec d (MkFix x) = showCon d "MkFix" $ show x

public export
Algebra : (Type -> Type) -> (Type -> Type)
Algebra f a = f a -> a

export covering
cata : Functor f => Algebra f a -> Fix f -> a
cata alg (MkFix op) = alg (map (cata alg) op)
