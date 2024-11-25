namespace Option

def zip (a : Option α) (b : Option β) : Option (α×β) := a >>= λ a ↦ b >>= λ b ↦ (a,b)

def unzip : (a : Option (α×β)) → (Option α) × (Option β)
| none => (none, none)
| some (a, b) => (some a, some b)

def toExcept {α : Type u0} {ε : Type u1} { m : Type u0 → Type u2} [Pure m] [MonadExcept m (ε := ε)] (error : ε) : Option α → m α
| none => throw error
| some a => pure a

def bindWithProof (o : Option α) (f : (v : α) → (o = some v) → Option β) : Option β :=
  match o with
  | .some v => f v rfl
  | .none => none

def mapWithProof (o : Option α) (f : (v : α) → (o = some v) → β) : Option β := bindWithProof o (some $ f · ·)

def ofBool : Bool → Option Unit
  | .false => none
  | .true => some ()
