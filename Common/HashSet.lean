import Std.Data.HashSet
import Common.Finite


open Std.HashSet
namespace Std.HashSet

theorem erase_not_mem {α : Type u} [BEq α] [Hashable α] [LawfulBEq α] (set : HashSet α) (a : α) : a ∉ (set.erase a) := by
  simp only [HashSet.mem_iff_contains, HashSet.contains_erase, beq_self_eq_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, not_false_eq_true]

theorem erase_not_mem_of_not_mem {α : Type u} [BEq α] [Hashable α] [LawfulBEq α] (set : HashSet α) {a : α} (b : α) (h₁ : a ∉ set) : a ∉ (set.erase b) := by
  intro h₂
  rw[HashSet.mem_erase] at h₂
  exact absurd h₂.right h₁

protected theorem size_le_finite_worker_size (α : Type u) [Finite α] [BEq α] [Hashable α] [LawfulBEq α] : ∀ (set : Std.HashSet α) (n : Fin (Finite.cardinality α)) (_h₁ : ∀(o : Fin (Finite.cardinality α)) (_h : o > n), Finite.nth o ∉ set), set.size ≤ (Finite.set.set_worker α HashSet.empty  n).size := by
  intros set n h₁
  cases n
  case mk n h₂ =>
  cases n
  case zero =>
    have h₃ : (Finite.set.set_worker α empty ⟨0,h₂⟩).size = 1 := by simp[Finite.set.set_worker, HashSet.size_insert]
    rw[h₃]
    cases h₄ : set.contains (Finite.nth ⟨0,h₂⟩)
    case false =>
      have h₅ : ∀(o : Fin (Finite.cardinality α)), Finite.nth o ∉ set := by
        simp[←Bool.not_eq_true, ←HashSet.mem_iff_contains] at h₄
        intro o
        cases o
        case mk o ho =>
        cases o
        case zero => exact h₄
        case succ oo => exact h₁ ⟨oo+1, ho⟩ (Nat.succ_pos oo)
      have h₆ : ∀(a : α), a∉set := Finite.forall_nth (λx ↦ x∉set) h₅
      have h₇ : set.isEmpty = true := HashSet.isEmpty_iff_forall_not_mem.mpr h₆
      have h₈ : true = (set.size == 0) := HashSet.isEmpty_eq_size_eq_zero.subst h₇.symm
      have h₈ : set.size = 0 := beq_iff_eq.mp h₈.symm
      rw[h₈]
      exact Nat.zero_le _
    case true =>
      --show that the set from which we erase (nth 0) has size 0, just like in case false.
      --then show that, since we removed one element, set.size equals 1.
      let rset := set.erase $ Finite.nth ⟨0,h₂⟩
      have h₅ : (Finite.nth ⟨0,h₂⟩) ∉ rset := erase_not_mem set (Finite.nth ⟨0,h₂⟩)
      have h₆ : ∀(o : Fin (Finite.cardinality α)), Finite.nth o ∉ rset := by
        intro o
        cases o
        case mk o ho =>
        cases o
        case zero => exact h₅
        case succ oo => exact erase_not_mem_of_not_mem set _ $ h₁ ⟨oo+1, ho⟩ (Nat.succ_pos oo)
      have h₇ : ∀(a : α), a∉rset := Finite.forall_nth (λx ↦ x∉rset) h₆
      have h₈ : rset.isEmpty = true := HashSet.isEmpty_iff_forall_not_mem.mpr h₇
      have h₉ : true = (rset.size == 0) := HashSet.isEmpty_eq_size_eq_zero.subst h₈.symm
      have h₉ : rset.size = 0 := beq_iff_eq.mp h₉.symm
      have h₁₀ : set.size ≤ rset.size + 1 := HashSet.size_le_size_erase
      rw[h₉, Nat.zero_add] at h₁₀
      assumption
  case succ m =>
    --erase (nth m) from the set and recurse.
    --then show that the current set can only be larger by 1, and therefore fulfills the goal
    --HashSet.size_le_size_erase
    let rset := set.erase $ Finite.nth ⟨m+1,h₂⟩
    have h₃ : (Finite.nth ⟨m+1,h₂⟩) ∉ rset := erase_not_mem set (Finite.nth ⟨m+1,h₂⟩)
    have h₄ : ∀(o : Fin (Finite.cardinality α)) (h₄ : o > ⟨m,Nat.lt_of_succ_lt h₂⟩), Finite.nth o ∉ rset := by
      intros o h₄
      cases o
      case mk o h₅ =>
      cases h₆ : o == (m+1) <;> simp at h₆
      case true =>
        simp only[h₆]
        exact erase_not_mem set $ Finite.nth ⟨m+1, h₂⟩
      case false =>
        have h₆ : o > m+1 := by simp at h₄; omega
        exact erase_not_mem_of_not_mem _ _ (h₁ ⟨o,h₅⟩ h₆)
    have h₅ := Std.HashSet.size_le_finite_worker_size α rset ⟨m, Nat.lt_of_succ_lt h₂⟩ h₄
    have h₆ : (Finite.set.set_worker α empty ⟨m, Nat.lt_of_succ_lt h₂⟩).size = empty.size + m + 1 :=
      Finite.set_worker_size α empty ⟨m, Nat.lt_of_succ_lt h₂⟩ (λa _ ↦Bool.eq_false_iff.mp $ HashSet.contains_empty (a := Finite.nth a))
    have h₇ : (Finite.set.set_worker α empty ⟨m+1,h₂⟩).size = empty.size + (m + 1) + 1 :=
      Finite.set_worker_size α empty ⟨m+1,h₂⟩ (λa _ ↦Bool.eq_false_iff.mp $ HashSet.contains_empty (a := Finite.nth a))
    have h₈ := HashSet.size_le_size_erase (m := set) (k:=Finite.nth ⟨m+1,h₂⟩)
    simp[h₆] at h₅
    simp[h₇]
    exact Nat.le_trans h₈ (Nat.succ_le_succ h₅)

theorem size_le_finite_set_size {α : Type u} [Finite α] [BEq α] [LawfulBEq α] [Hashable α] (set : Std.HashSet α) : set.size ≤ (Finite.set α).size := by
  unfold Finite.set
  split
  case h_1 h₁ =>
    if h : set.isEmpty then
      have := HashSet.isEmpty_eq_size_eq_zero (m := set)
      simp[h] at this
      simp[this]
    else
      have := HashSet.isEmpty_eq_false_iff_exists_mem.mp (Bool.eq_false_iff.mpr h)
      cases this
      case intro x hx =>
        let xx := Finite.enumerate x
        exact (Fin.cast h₁ xx).elim0
  case h_2 l h =>
    exact Std.HashSet.size_le_finite_worker_size α set ⟨l,h.substr $ Nat.lt_succ_self l⟩ (λa hx ↦
      by
      have h₁ := a.isLt
      simp_arith[h] at h₁
      have h₂ : a > l := Fin.lt_iff_val_lt_val.mp hx
      exact absurd h₁ (Nat.not_le.mpr h₂)
    )

theorem size_le_finite_cardinality {α : Type u} [Finite α] [BEq α] [LawfulBEq α] [Hashable α] (set : Std.HashSet α) : set.size ≤ Finite.cardinality α :=
  (Finite.set_size_eq_cardinality α).subst (size_le_finite_set_size set)

theorem size_lt_finite_cardinality_of_not_mem {α : Type u} [Finite α] [BEq α] [LawfulBEq α] [Hashable α] (set : Std.HashSet α) (h₁ : ∃(a : α), a ∉ set) : set.size < Finite.cardinality α := by
  have h₂ : set.size ≤ Finite.cardinality α := size_le_finite_cardinality set
  cases h₁
  case intro e h₁ =>
  let iset := set.insert e
  have h₂ : iset.size = set.size + 1 := by
    have := HashSet.size_insert (m := set) (k := e)
    simp[h₁] at this
    assumption
  have h₃ : iset.size ≤ Finite.cardinality α := size_le_finite_cardinality iset
  rw[h₂] at h₃
  exact Nat.lt_of_succ_le h₃
