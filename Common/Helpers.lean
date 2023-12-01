def curry (g : (α × β) → γ) : α → β → γ := λ a b ↦ g (a,b)
def uncurry (f : α → β → γ) : (α × β) → γ := λ (a,b) ↦ f a b
