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
  termination_by quicksortBy pred l => l.length

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

/-- Removes repeated entries. [1,2,2,1] becomes [1,2,1]-/
def dedup {α : Type} [BEq α] (input : List α) : List α :=
  let rec helper : List α → α → List α := λ
  | [], _ => []
  | a :: as, b =>
    if a == b then
      helper as a
    else
      a :: helper as a
  match input with
  | [] => []
  | a :: as => a :: helper as a
