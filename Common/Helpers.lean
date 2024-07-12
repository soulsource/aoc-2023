def curry (g : (α × β) → γ) : α → β → γ := λ a b ↦ g (a,b)
def uncurry (f : α → β → γ) : (α × β) → γ := λ (a,b) ↦ f a b

-- Default instance for LT, LE for anything that's Ord.
instance {α : Type} [Ord α]: LT α where
  lt := λ a b ↦ Ord.compare a b == Ordering.lt
instance {α : Type} [Ord α]: LE α where
  le := λ a b ↦ Ord.compare a b != Ordering.gt
instance {a b : α} [Ord α] : Decidable (a < b) :=
  if p : Ord.compare a b == Ordering.lt then
    Decidable.isTrue p
  else
    Decidable.isFalse p
