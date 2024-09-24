namespace List

theorem listFilterSmallerOrEqualList (l : List α) (p : α → Bool) : l.length ≥ (l.filter p).length := by
  induction l with
  | nil => simp[List.filter]
  | cons a as hi =>
    simp[List.length, List.filter]
    cases (p a) with
    | false =>
      simp
      constructor
      assumption
    | true => simp_arith[hi]

def quicksortBy {α : Type} (pred : α → α → Bool): List α → List α
| [] => []
| a :: as =>
  let smallerPred := λ b ↦ pred b a
  let largerEqualPred := not ∘ smallerPred
  have : List.length (List.filter smallerPred as) < Nat.succ (List.length as) := by simp_arith[listFilterSmallerOrEqualList]
  have : List.length (List.filter largerEqualPred as) < Nat.succ (List.length as) := by simp_arith[listFilterSmallerOrEqualList]
  let smallers := as.filter smallerPred
  let biggers := as.filter largerEqualPred
  (quicksortBy pred smallers) ++ [a] ++ (quicksortBy pred biggers)
  termination_by l => l.length

def quicksort {α : Type} [Ord α] : List α → List α := quicksortBy λ a b ↦ Ord.compare a b == Ordering.lt

/-- Maps a List to another list, but keeps state.
    The output list is a list of the state, and **has** the initial state
    prepended!
 -/
def scan {α σ : Type} (step : σ → α → σ) (init : σ): List α → List σ
| [] => [init]
| a :: as =>
  let next := step init a
  init :: scan step next as

def compare {α : Type} [Ord α] (a b : List α) := match a, b with
  | _ :: _, [] => Ordering.gt
  | [], _ :: _ => Ordering.lt
  | [], [] => Ordering.eq
  | a :: as, b :: bs =>
    let ab := Ord.compare a b
    if ab != Ordering.eq then
      ab
    else
      compare as bs

instance {α : Type} [Ord α] : Ord (List α) where
  compare := compare

def not_empty_iff_size_gt_zero {list : List α} : list.isEmpty = false ↔ list.length > 0 :=
  match list with
  | [] => ⟨nofun, nofun⟩
  | l :: ls => ⟨λ_ ↦ (List.length_cons l ls).substr (Nat.succ_pos ls.length), λ_ => rfl⟩

def ne_nil_of_not_empty {list : List α} : list.isEmpty = false ↔ list ≠ [] :=
  match list with
  | [] => ⟨nofun, nofun⟩
  | _ :: _ => ⟨nofun, λ_ ↦ List.isEmpty_cons⟩

def drop_while_length_le (list : List α) (f : α → Bool) : (list.dropWhile f).length ≤ list.length := by
  unfold dropWhile
  split
  case h_1 => exact Nat.le_refl _
  case h_2 =>
    split
    case h_2 => exact Nat.le_refl _
    case h_1 a as _  _ =>
      have := drop_while_length_le as f
      exact Nat.le_trans this (Nat.le_succ as.length)
