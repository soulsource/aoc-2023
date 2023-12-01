namespace Option

def zip (a : Option α) (b : Option β) : Option (α×β) := a >>= λ a ↦ b >>= λ b ↦ (a,b)

def unzip : (a : Option (α×β)) → (Option α) × (Option β)
| none => (none, none)
| some (a, b) => (some a, some b)
