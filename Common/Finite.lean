import Std.Data.HashSet

class Finite (α : Type u) where
  cardinality : Nat
  enumerate : α → Fin cardinality
  nth : Fin cardinality → α
  nth_inverse_enumerate : nth ∘ enumerate = id
  enumerate_inverse_nth : enumerate ∘ nth = id

theorem Finite.surjective {α : Type u} [Finite α] {a b : Fin (Finite.cardinality α)} : nth a = nth b → a = b := λh₃ ↦
  have h₁ := Finite.enumerate_inverse_nth (α := α)
  have h₄ := congrArg enumerate h₃
  have h₂ : ∀(x : Fin (Finite.cardinality α)), (enumerate ∘ nth) x = x := λ_↦h₁.substr rfl
  have h₅ := Function.comp_apply.subst (h₂ a).symm
  have h₆ := Function.comp_apply.subst (h₂ b).symm
  h₅.substr $ h₆.substr h₄

theorem Finite.injective {α : Type u} [Finite α] {a b : α} : enumerate a = enumerate b → a = b := λh₁↦
  have h₂ := Finite.nth_inverse_enumerate (α := α)
  have h₃ := congrArg nth h₁
  have h₄ : ∀(x : α), (nth ∘ enumerate) x = x := λ_↦h₂.substr rfl
  have h₅ := Function.comp_apply.subst (h₄ a).symm
  have h₆ := Function.comp_apply.subst (h₄ b).symm
  h₅.substr $ h₆.substr h₃

def Finite.set (α : Type u) [Finite α] [BEq α] [Hashable α] : Std.HashSet α :=
  match h: (Finite.cardinality α) with
  | 0 => Std.HashSet.empty
  | l+1 => set_worker Std.HashSet.empty ⟨l,h.substr (p := λx ↦ l < x) $ Nat.lt.base l⟩
where set_worker (set : Std.HashSet α) (n : Fin (Finite.cardinality α)) : Std.HashSet α :=
  let e := Finite.nth n
  let set := set.insert e
  match n with
  | ⟨0,_⟩ => set
  | ⟨m+1,h₁⟩ => set_worker set ⟨m, Nat.lt_of_succ_lt h₁⟩

protected theorem Finite.set_worker_contains_self' (α : Type u) [Finite α] [BEq α] [Hashable α] [LawfulBEq α] (a : α) (oldSet : Std.HashSet α) (h₁ : oldSet.contains a) (n : Fin (Finite.cardinality α)) : (Finite.set.set_worker α oldSet n).contains a := by
  cases n
  case mk n h₂ =>
    induction n generalizing oldSet
    case zero => unfold set.set_worker; simp[h₁]
    case succ m hm =>
      unfold set.set_worker
      exact hm (oldSet.insert (nth ⟨m + 1, h₂⟩)) (by simp[h₁]) (Nat.lt_of_succ_lt h₂)

protected theorem Finite.set_worker_contains_self (α : Type u) [Finite α] [BEq α] [Hashable α] [LawfulBEq α] : ∀ (a : α) (set : Std.HashSet α), (Finite.set.set_worker α set (Finite.enumerate a)).contains a := by
  intros a oldSet
  unfold set.set_worker
  rw[←Function.comp_apply (f := nth), Finite.nth_inverse_enumerate, id_def]
  split
  case h_1 => apply Std.HashSet.contains_insert_self
  case h_2 =>
    apply Finite.set_worker_contains_self'
    exact Std.HashSet.contains_insert_self

protected theorem Finite.set_worker_contains (α : Type u) [Finite α] [BEq α] [Hashable α] [LawfulBEq α] : ∀ (a : α) (set : Std.HashSet α) (o : Nat) (h₁ : Finite.enumerate a + o < Finite.cardinality α), (Finite.set.set_worker α set ⟨Finite.enumerate a + o, h₁⟩).contains a := by
  intros a oldSet offset h₁
  induction offset generalizing oldSet
  case zero =>
    exact Finite.set_worker_contains_self _ _ _
  case succ p hi =>
    unfold set.set_worker
    simp
    have : ↑(enumerate a) + p < cardinality α := Nat.lt_of_succ_lt $ (Nat.add_assoc (enumerate a) p 1).substr h₁
    exact hi (oldSet.insert (nth ⟨↑(enumerate a) + (p + 1), h₁⟩)) this

theorem Finite.set_contains (α : Type u) [Finite α] [BEq α] [Hashable α] [LawfulBEq α] : ∀ (a : α), (Finite.set α).contains a := λa ↦ by
    unfold set
    split
    case h_1 h => exact (Fin.cast h $ Finite.enumerate a).elim0
    case h_2 l h =>
      let o := l - enumerate a
      have h₁ : (Finite.enumerate a).val + o = l := by omega
      have h₂ := Finite.set_worker_contains _ a Std.HashSet.empty o (by omega)
      simp[h₁] at h₂
      assumption

protected theorem Finite.set_worker_size (α : Type u) [Finite α] [BEq α] [Hashable α] [LawfulBEq α]
: ∀(set : Std.HashSet α) (n : Fin (Finite.cardinality α)) (_ : ∀(x : Fin (Finite.cardinality α)) (_ : x ≤ n),
   ¬set.contains (Finite.nth x)), (Finite.set.set_worker α set n).size = set.size + n + 1
:= by
  intros set n h₂
  simp at h₂
  unfold Finite.set.set_worker
  cases n
  case mk n h₁ =>
    split
    case h_1 m isLt he =>
      simp at he
      simp[Std.HashSet.size_insert, Std.HashSet.mem_iff_contains, h₂, he]
    case h_2 m isLt he =>
      simp
      have h₄ : m < n := have : n = m.succ := Fin.val_eq_of_eq he; this.substr (Nat.lt_succ_self m)
      have h₅ : ∀ (x : Fin (cardinality α)), x ≤ ⟨m, Nat.lt_of_succ_lt isLt⟩ → ¬(set.insert (nth ⟨n, h₁⟩)).contains (nth x) = true := by
        simp
        intros x hx
        constructor
        case right => exact h₂ x (Nat.le_trans hx (Nat.le_of_lt h₄))
        case left =>
          have h₅ : x ≠ ⟨n, h₁⟩ := Fin.ne_of_val_ne $ Nat.ne_of_lt $ Nat.lt_of_le_of_lt hx h₄
          have h₆ := Finite.surjective (α := α) (a := x) (b := ⟨n,h₁⟩)
          exact Ne.symm (h₅ ∘ h₆)
      have h₃ := Finite.set_worker_size α (set.insert (nth ⟨n, h₁⟩)) ⟨m, Nat.lt_of_succ_lt isLt⟩ (h₅)
      rw[h₃]
      simp at he
      simp[he, Std.HashSet.size_insert]
      split
      case isFalse => rw[Nat.add_assoc, Nat.add_comm 1 m]
      case isTrue hx =>
        subst n
        have h₂ := h₂ ⟨m+1,h₁⟩ (Fin.le_refl _)
        have hx := Std.HashSet.mem_iff_contains.mp hx
        exact absurd hx (Bool.eq_false_iff.mp h₂)
termination_by _ n => n.val

theorem Finite.set_size_eq_cardinality (α : Type u) [Finite α] [BEq α] [Hashable α] [LawfulBEq α] : (Finite.set α).size = Finite.cardinality α := by
  unfold set
  split
  case h_1 h => exact Std.HashSet.size_empty.substr h.symm
  case h_2 l h =>
    rewrite(occs := .pos [3])[h]
    have := Finite.set_worker_size α Std.HashSet.empty ⟨l,h.substr $ Nat.lt_succ_self l⟩ (λx _↦Bool.eq_false_iff.mp (Std.HashSet.contains_empty (a:=Finite.nth x)))
    simp only [this, Std.HashSet.size_empty, Nat.zero_add]
