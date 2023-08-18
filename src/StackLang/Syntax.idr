module StackLang.Syntax

import Data.SnocList
import Data.SnocList.Quantifiers

||| A stack.
public export
Stack : SnocList Type -> Type
Stack xs = All id xs

infixr 1 *->

||| A function operating on stacks.
public export
(*->) : SnocList Type -> SnocList Type -> Type
s *-> s' = Stack s -> Stack s'

namespace QuotationNotation
  ||| Empty quotation.
  public export
  Nil : s *-> (s :< (s' *-> s'))
  Nil s = s :< id

  ||| Prepend a word to a quotation.
  public export
  (::) : (s *-> s') -> (s *-> (s'' :< (s' *-> t''))) -> (s *-> (s'' :< (s *-> t'')))
  (qhead :: g) s =
    let (s'' :< qtail) = g s in
    s'' :< (qtail . qhead)
