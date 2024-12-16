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

def mapWithProof {α : Type u} {β : Type v} (list : List α) (f : (e : α) → (e ∈ list) → β) : List β :=
  worker list f []
where
  worker : (list : List α) → ((e : α) → (e ∈ list) → β) → List β → List β
  | [], _, bs => bs.reverse
  | a :: as, f, bs =>
    let g : (e : α) → (e ∈ as) → β := λ e h ↦ f e (List.mem_cons_of_mem a h)
    worker as g (f a (List.mem_cons_self _ _) :: bs)

protected theorem length_mapWithProof_Aux {α : Type u} {β : Type v} (list : List α) (f : (e : α) → (e ∈ list) → β) (acc : List β) : list.length + acc.length = (List.mapWithProof.worker list f acc).length := by
  induction list generalizing acc
  case nil => unfold mapWithProof.worker; simp only [length_nil, Nat.zero_add, length_reverse]
  case cons l ls hi =>
    unfold mapWithProof.worker
    have hi := hi (λe h ↦ f e (mem_cons_of_mem _ h)) (f l (mem_cons_self _ _) :: acc)
    simp_arith[←hi]

theorem length_mapWithProof {α : Type u} {β : Type v} {list : List α} {f : (e : α) → (e ∈ list) → β} : list.length = (list.mapWithProof f).length :=
  List.length_mapWithProof_Aux list f []

theorem mapWithProof_nil {α : Type u} {β : Type v} {f : (e : α) → (e ∈ []) → β} : [].mapWithProof f = [] := rfl

theorem mapWithProof_neNilIffNeNil {α : Type u} {β : Type v} {list : List α} {f : (e : α) → (e ∈ list) → β} : list ≠ [] ↔ (list.mapWithProof f) ≠ [] :=
  ⟨
    λh₁ ↦ List.length_pos.mp $ length_mapWithProof.subst (List.length_pos.mpr h₁),
    λh₁ ↦ List.length_pos.mp $ length_mapWithProof.substr (List.length_pos.mpr h₁)
  ⟩

theorem map_ne_nil {α : Type u} {β : Type v} {list : List α} {f : α → β} : list ≠ [] ↔ list.map f ≠ [] :=
  ⟨
    λh₁ ↦ λh₂ ↦ absurd (List.map_eq_nil_iff.mp h₂) h₁,
    λh₁ ↦ λh₂ ↦ absurd (List.map_eq_nil_iff.mpr h₂) h₁,
  ⟩

def min [Min α] (l : List α) (_h : l ≠ []) : α :=
  match l with
  | a :: as => as.foldl Min.min a

def max [Max α] (l : List α) (_h : l ≠ []) : α :=
  match l with
  | a :: as => as.foldl Max.max a
