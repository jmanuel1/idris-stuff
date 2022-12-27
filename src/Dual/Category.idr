-- https://reader.elsevier.com/reader/sd/pii/S0304397599001243?token=66698B17B3099B18267A533F6A4121DBA0D1DD34140D52CFBE9920B9D7A372F4C9F15A7E0B6F5592F57DC4174AA212CE&originRegion=us-east-1&originCreation=20221221061024
module Dual.Category

%default total

record Category (object : Type) (arrow : object -> object -> Type) where
  constructor MkCategory
  id : (a : object) -> a `arrow` a
  compose : {a, b, c : object} -> b `arrow` c -> a `arrow` b -> a `arrow` c
  idComposeRight : (a, b : object) -> (f : a `arrow` b) -> (f `compose` id a) === f
  idComposeLeft : (a, b : object) -> (f : a `arrow` b) -> (id b `compose` f) === f
  composeAssociative : (a, b, c, d : object) -> (f : a `arrow` b) -> (g : b `arrow` c) -> (h : c `arrow` d) -> ((h `compose` g) `compose` f) === (h `compose` (g `compose` f))

record Isomorphism (object : Type) (a, b : object) (arrow : object -> object -> Type) (c : Category object arrow) (i : a `arrow` b) where
  constructor MkIsomorphism
  j : b `arrow` a
  idA : c.compose j i === c.id a
  idB : c.compose i j === c.id b

dual : Category object arrow -> Category object (flip arrow)
dual cat = MkCategory {
  id = cat.id,
  compose = (\fOp, gOp => cat.compose gOp fOp),
  idComposeRight = \a, b, fOp => cat.idComposeLeft b a fOp,
  idComposeLeft = \a, b, fOp => cat.idComposeRight b a fOp,
  composeAssociative = \a, b, c, d, fOp, gOp, hOp =>
    let ca = cat.composeAssociative d c b a hOp gOp fOp in sym ca
}

0 Unique : t -> Type
Unique a = (b : t) -> a === b

record Final object arrow (c : Category object arrow) where
  constructor MkFinal
  top : object
  unit : (a : object) -> a `arrow` top
  unitUnique : (a : object) -> Unique (unit a)

record Initial object arrow (c : Category object arrow) where
  constructor MkInitial
  bottom : object
  absurd : (a : object) -> bottom `arrow` a
  absurdUnique : (a : object) -> Unique (absurd a)

record Product object arrow (cat : Category object arrow) (a, b : object) where
  constructor MkProduct
  product : object
  pi : product `arrow` a
  pi' : product `arrow` b
  universalProperty : (c : object) -> (f : c `arrow` a) -> (g : c `arrow` b) -> (h : c `arrow` product ** (Unique h, f === (cat.compose pi h), g === (cat.compose pi' h)))

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

arrowsIntoProduct : (gamma : object) -> (p : Product object arrow cat a b) -> gamma `arrow` a -> gamma `arrow` b -> gamma `arrow` p.product
arrowsIntoProduct gamma p f g = fst $ p.universalProperty gamma f g

-- infixr 9 ><
--
-- (><) : {auto cat : Category object arrow} -> Product object arrow cat a c => Product object arrow cat b d => {a, b, c, d : object} -> a `arrow` b -> c `arrow` d -> (a * c) `arrow` (b * d)
-- (><) @{cat} @{acProduct} f g = (cat.compose f (acProduct.pi), cat.compose g (acProduct.pi'))

bimapProduct : (cat : Category object arrow) -> {a, b, c, d : object} -> (ac : Product object arrow cat a c) -> (bd : Product object arrow cat b d) -> a `arrow` b -> c `arrow` d -> ac.product `arrow` bd.product
bimapProduct cat ac bd f g = arrowsIntoProduct ac.product bd (cat.compose f ac.pi) (cat.compose g ac.pi')

record Exponential object arrow (cat : Category object arrow) (b, a : object) where -- b ** a
  constructor MkExponential
  exp : object
  -- %hint
  productARight : (o : object) -> Product object arrow cat o a
  eval : (productARight exp).product `arrow` b
  curry : (gamma : object) -> (f : (productARight gamma).product `arrow` b) -> gamma `arrow` exp
  diagramCommutes : (gamma : object) -> (f : (productARight gamma).product `arrow` b) -> (cat.compose eval (bimapProduct cat (productARight gamma) (productARight exp) (curry gamma f) (cat.id a))) === f
  curryUnique : (gamma : object) -> (f : (productARight gamma).product `arrow` b) -> let h := curry gamma f in curry gamma (cat.compose eval (bimapProduct cat (productARight gamma) (productARight exp) h (cat.id a))) === h

record Cartesian object arrow (cat : Category object arrow) where
  finiteProduct : (a, b : object) -> Product object arrow cat a b

record CartesianClosed object arrow (cat : Category object arrow) where
  constructor MkCartesianClosed
  cartesian : Cartesian object arrow cat
  exponential : (b, a : object) -> Exponential object arrow cat b a
  -- final : Final object arrow cat

CocartesianCoclosed : (object, arrow : _) -> Category object arrow -> Type
CocartesianCoclosed o a cat = CartesianClosed o (flip a) (dual cat)
