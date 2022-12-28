-- https://reader.elsevier.com/reader/sd/pii/S0304397599001243?token=66698B17B3099B18267A533F6A4121DBA0D1DD34140D52CFBE9920B9D7A372F4C9F15A7E0B6F5592F57DC4174AA212CE&originRegion=us-east-1&originCreation=20221221061024
module Dual.Category

%default total

public export
record Category (object : Type) (arrow : object -> object -> Type) where
  constructor MkCategory
  id : (a : object) -> a `arrow` a
  compose : {a, b, c : object} -> b `arrow` c -> a `arrow` b -> a `arrow` c
  idComposeRight : (a, b : object) -> (f : a `arrow` b) -> (f `compose` id a) === f
  idComposeLeft : (a, b : object) -> (f : a `arrow` b) -> (id b `compose` f) === f
  composeAssociative : (a, b, c, d : object) -> (f : a `arrow` b) -> (g : b `arrow` c) -> (h : c `arrow` d) -> ((h `compose` g) `compose` f) === (h `compose` (g `compose` f))

record Isomorphism (object : Type) (a, b : object) (arrow : object -> object -> Type) (c : Category object arrow) (i : a `arrow` b) where
  constructor MkIsomorphism
  isomorphismReverse : b `arrow` a
  idA : c.compose isomorphismReverse i === c.id a
  idB : c.compose i isomorphismReverse === c.id b

public export
dual : Category object arrow -> Category object (flip arrow)
dual cat = MkCategory {
  id = cat.id,
  compose = (\fOp, gOp => cat.compose gOp fOp),
  idComposeRight = \a, b, fOp => cat.idComposeLeft b a fOp,
  idComposeLeft = \a, b, fOp => cat.idComposeRight b a fOp,
  composeAssociative = \a, b, c, d, fOp, gOp, hOp =>
    let ca = cat.composeAssociative d c b a hOp gOp fOp in sym ca
}

public export
0 Unique : t -> Type
Unique a = (b : t) -> a === b

public export
record Final object arrow (c : Category object arrow) where
  constructor MkFinal
  top : object
  unit : (a : object) -> a `arrow` top
  unitUnique : (a : object) -> Unique (unit a)

public export
record Initial object arrow (c : Category object arrow) where
  constructor MkInitial
  bottom : object
  absurd : (a : object) -> bottom `arrow` a
  absurdUnique : (a : object) -> Unique (absurd a)

public export
record Product object arrow (cat : Category object arrow) (a, b : object) where
  constructor MkProduct
  product : object
  pi : product `arrow` a
  pi' : product `arrow` b
  -- name is from https://en.wikipedia.org/wiki/Product_(category_theory)#Product_of_two_objects
  arrowProduct : (gamma : object) -> gamma `arrow` a -> gamma `arrow` b -> gamma `arrow` product
  diagramCommutes : (c : object) -> (f : c `arrow` a) -> (g : c `arrow` b) -> let h := arrowProduct c f g in (f === (cat.compose pi h), g === (cat.compose pi' h))
  -- https://en.wikipedia.org/wiki/Product_(category_theory)#Equational_definition
  arrowProductUnique : (c : object) -> (g : c `arrow` product) -> arrowProduct c (cat.compose pi g) (cat.compose pi' g) === g

public export
Coproduct : (object, arrow : _) -> Category object arrow -> object -> object -> Type
Coproduct o a cat = Product o (flip a) (dual cat)

-- %hide Prelude.(*)
--
-- (*) : (cat : Category object arrow) => (a, b : object) -> (product : Product object arrow cat a b) => object
-- (*) @{_} a b @{product} = product.product

-- NOTE: produxt of two objects is already inside the Product evidence

--
-- %hide Builtin.MkPair
--
-- MkPair : {0 a, b : object} -> {gamma : object} -> (cat : Category object arrow) => Product object arrow cat a b => gamma `arrow` a -> gamma `arrow` b -> gamma `arrow` (a * b)
-- MkPair @{_} @{product} {gamma} f g = fst $ product.universalProperty gamma f g

-- infixr 9 ><
--
-- (><) : {auto cat : Category object arrow} -> Product object arrow cat a c => Product object arrow cat b d => {a, b, c, d : object} -> a `arrow` b -> c `arrow` d -> (a * c) `arrow` (b * d)
-- (><) @{cat} @{acProduct} f g = (cat.compose f (acProduct.pi), cat.compose g (acProduct.pi'))

-- Name from https://en.wikipedia.org/wiki/Product_(category_theory)#Discussion.
public export
cartesianArrowProduct : (cat : Category object arrow) -> {a, b, c, d : object} -> (ac : Product object arrow cat a c) -> (bd : Product object arrow cat b d) -> a `arrow` b -> c `arrow` d -> ac.product `arrow` bd.product
cartesianArrowProduct cat ac bd f g = bd.arrowProduct ac.product (cat.compose f ac.pi) (cat.compose g ac.pi')

public export
record Exponential object arrow (cat : Category object arrow) (b, a : object) where -- b ** a
  constructor MkExponential
  exp : object
  productARight : (o : object) -> Product object arrow cat o a
  eval : (productARight exp).product `arrow` b
  curry : (gamma : object) -> (f : (productARight gamma).product `arrow` b) -> gamma `arrow` exp
  diagramCommutes : (gamma : object) -> (f : (productARight gamma).product `arrow` b) -> (cat.compose eval (cartesianArrowProduct cat (productARight gamma) (productARight exp) (curry gamma f) (cat.id a))) === f
  -- https://en.wikipedia.org/wiki/Exponential_object#Equational_definition
  curryUnique : (gamma : object) -> (h : gamma `arrow` exp) -> curry gamma (cat.compose eval (cartesianArrowProduct cat (productARight gamma) (productARight exp) h (cat.id a))) === h

public export
record Cartesian object arrow (cat : Category object arrow) where
  constructor MkCartesian
  finiteProduct : (a, b : object) -> Product object arrow cat a b

public export
record CartesianClosed object arrow (cat : Category object arrow) where
  constructor MkCartesianClosed
  cartesian : Cartesian object arrow cat
  exponential : (b, a : object) -> Exponential object arrow cat b a
  -- final : Final object arrow cat

public export
CocartesianCoclosed : (object, arrow : _) -> Category object arrow -> Type
CocartesianCoclosed o a cat = CartesianClosed o (flip a) (dual cat)
