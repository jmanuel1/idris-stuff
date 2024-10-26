module Data.Variant

import public Data.List.Elem
import public Data.List.Quantifiers
import public Data.Variant.Fix

%default total

export
Show (Any f []) where
  show x impossible

export
[showAnyCons] Show ((the (x -> Type) f) a) => Show (Any f as) => Show (Any f (a :: as)) where
  showPrec d (Here x) = showCon d "Here" $ showArg x
  showPrec d (There x) = showCon d "There" $ showArg x

public export
record AnyF (fs : List (Type -> Type)) (a : Type) where
  constructor MkAnyF
  any : Any ($ a) fs

export
Functor (AnyF []) where
  map f (MkAnyF x) impossible

export
Functor f => Functor (AnyF fs) => Functor (AnyF (f :: fs)) where
  map f (MkAnyF (Here x)) = MkAnyF $ Here $ map f x
  map f (MkAnyF (There x)) = MkAnyF $ There $ (map f (MkAnyF x)).any

export
[showAnyF] Show (Any ($ a) fs) => Show (AnyF fs a) where
  showPrec d x = showCon d "MkAnyF" $ showArg x.any

export
injectF : Elem f fs => f a -> (AnyF fs a)
injectF @{Here} x = MkAnyF (Here x)
injectF @{There i} x = MkAnyF (There (injectF x).any)

export
Elem f fs => Cast (f a) (AnyF fs a) where
  cast = injectF

export covering
fixInject : Elem f fs => f (Fix (AnyF fs)) -> Fix (AnyF fs)
fixInject = MkFix . injectF

export covering
injectFix : Elem f fs => Functor f => Fix f -> Fix (AnyF fs)
injectFix = cata fixInject

export covering
Elem f fs => Cast (f (Fix (AnyF fs))) (Fix (AnyF fs)) where
  cast = fixInject

export
match : All (\x => f x -> a) xs -> Any f xs -> a
match (f :: _) (Here x) = f x
match (_ :: fs) (There x) = match fs x

export
getAlt : Elem x xs => Any f xs -> Maybe (f x)
getAlt @{Here} (Here x) = Just x
getAlt @{There _} (There x) = getAlt x
getAlt _ = Nothing

export covering
getAltLayer : Elem f fs => Fix (AnyF fs) -> Maybe (f (Fix (AnyF fs)))
getAltLayer = getAlt . .any . .unFix

public export
data Subset : List a -> List a -> Type where
  Nil : Subset [] xs
  (::) : Elem x xs -> Subset ys xs -> Subset (x :: ys) xs
