structure NonEmptyList (α : Type) where
  head : α
  tail : List α

namespace NonEmptyList
def toList (l : NonEmptyList α) : List α :=
  l.head :: l.tail

def ofList (l : List α) (_ : ¬l.isEmpty) : NonEmptyList α :=
  match l with
  | head :: tail => {head, tail}

def ofList? (l : List α) : Option $ NonEmptyList α :=
  if h : l.isEmpty then
    none
  else
    ofList l h

instance [ToString α] : ToString (NonEmptyList α) where
  toString := List.toString ∘ toList
