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


def quicksort {α : Type} [Ord α] : List α → List α
| [] => []
| a :: as =>
  let smallerPred := λ b ↦ Ord.compare b a == Ordering.lt
  let largerEqualPred := λ b ↦ Ord.compare b a != Ordering.lt
  have : List.length (List.filter smallerPred as) < Nat.succ (List.length as) := by simp_arith[listFilterSmallerOrEqualList]
  have : List.length (List.filter largerEqualPred as) < Nat.succ (List.length as) := by simp_arith[listFilterSmallerOrEqualList]
  let smallers := as.filter smallerPred
  let biggers := as.filter largerEqualPred
  (quicksort smallers) ++ [a] ++ (quicksort biggers)
  termination_by quicksort l => l.length
