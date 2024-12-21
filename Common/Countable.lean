import Common.Finite

class Countable (α : Type u) where
  enumerate : α → Nat
  injective {a b : α} : enumerate a = enumerate b → a = b

instance {α : Type u} [Finite α] : Countable α where
  enumerate := Fin.val ∘ Finite.enumerate
  injective :=  Finite.injective ∘ Fin.val_inj.mp
