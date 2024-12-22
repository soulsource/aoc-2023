theorem Function.comp_assoc (f : γ → δ) (g : β → γ) (h : α → β) : (f∘g)∘h = f∘g∘h := rfl
theorem Function.comp_id (f : α → β) : f ∘ id = f := rfl
theorem Function.id_comp (f : α → β) : id ∘ f = f := rfl
