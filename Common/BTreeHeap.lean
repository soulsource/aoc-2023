namespace BTreeHeap

/--A heap, represented as a binary indexed tree. The heap predicate is a type parameter, the index is the element count.-/
inductive BTreeHeap (α : Type u) (lt : α → α → Bool ): Nat → Type u
  | leaf : BTreeHeap α lt 0
  | branch : (val : α) → (left : BTreeHeap α lt n) → (right : BTreeHeap α lt m) → m ≤ n → BTreeHeap α lt (n+m+1)

/--Please do not use this for anything meaningful. It's a debug function, with horrible performance.-/
instance {α : Type u} {lt : α → α → Bool} [ToString α] : ToString (BTreeHeap α lt n) where
  toString := λt ↦
    --not very fast, doesn't matter, is for debugging
    let rec max_width := λ {m : Nat} (t : (BTreeHeap α lt m)) ↦ match m, t with
    | 0, .leaf => 0
    | (_+_+1), BTreeHeap.branch a left right _ => max (ToString.toString a).length $ max (max_width left) (max_width right)
    let max_width := max_width t
    let lines_left := Nat.log2 (n+1).nextPowerOfTwo
    let rec print_line := λ (mw : Nat) {m : Nat} (t : (BTreeHeap α lt m)) (lines : Nat)  ↦
      match m, t with
      | 0, _ => ""
      | (_+_+1), BTreeHeap.branch a left right _ =>
        let thisElem := ToString.toString a
        let thisElem := (List.replicate (mw - thisElem.length) ' ').asString ++ thisElem
        let elems_in_last_line := if lines == 0 then 0 else 2^(lines-1)
        let total_chars_this_line := elems_in_last_line * mw + 2*(elems_in_last_line)+1
        let left_offset := (total_chars_this_line - mw) / 2
        let whitespaces := max left_offset 1
        let whitespaces := List.replicate whitespaces ' '
        let thisline := whitespaces.asString ++ thisElem ++ whitespaces.asString ++"\n"
        let leftLines := (print_line mw left (lines-1) ).splitOn "\n"
        let rightLines := (print_line mw right (lines-1) ).splitOn "\n" ++ [""]
        let combined := leftLines.zip (rightLines)
        let combined := combined.map λ (a : String × String) ↦ a.fst ++ a.snd
        thisline ++ combined.foldl (· ++ "\n" ++ ·) ""
    print_line max_width t lines_left

/-- Extracts the element count. For when pattern matching is too much work. -/
def BTreeHeap.length : BTreeHeap α lt n → Nat := λ_ ↦ n

/--Creates an empty BTreeHeap. Needs the heap predicate as parameter.-/
abbrev BTreeHeap.empty {α : Type u} (lt : α → α → Bool ) := BTreeHeap.leaf (α := α) (lt := lt)

theorem blah : n + 1 < m + 1 → n < m := by simp_arith
                                           apply id

/--Adds a new element to a given BTreeHeap.-/
def BTreeHeap.insert (elem : α) (heap : BTreeHeap α lt o) : BTreeHeap α lt (o+1) :=
  match o, heap with
  | 0, .leaf => BTreeHeap.branch elem (BTreeHeap.leaf) (BTreeHeap.leaf) (by simp)
  | (n+m+1), .branch a left right p =>
    let (elem, a) := if lt elem a then (a, elem) else (elem, a)
    -- okay, based on n and m we know if we want to add left or right.
    -- the left tree is full, if (n+1) is a power of two AND n != m
    let leftIsFull : Bool := (n+1).nextPowerOfTwo = n+1
    if r : m < n ∧ leftIsFull  then
      have s : (m + 1 < n + 1) = (m < n) := by simp_arith
      have q : m + 1 ≤ n := by apply Nat.le_of_lt_succ
                               rewrite[Nat.succ_eq_add_one]
                               rw[s]
                               simp[r]
      let result := branch a left (right.insert elem) (q)
      result
    else
      have q : m ≤ n+1 := by apply (Nat.le_of_succ_le)
                             simp_arith[p]
      let result := branch a (left.insert elem) right q
      have letMeSpellItOutForYou : n + 1 + m + 1 = n + m + 1 + 1 := by simp_arith
      letMeSpellItOutForYou ▸ result


/--Helper function for BTreeHeap.indexOf.-/
def BTreeHeap.indexOfAux {α : Type u} {lt : α → α → Bool} [BEq α] (elem : α) (heap : BTreeHeap α lt o) (currentIndex : Nat) : Option (Fin (o+currentIndex)) :=
  match o, heap with
  | 0, .leaf => none
  | (n+m+1), .branch a left right _ =>
    if a == elem then
      let result := Fin.ofNat' currentIndex (by simp_arith)
      some result
    else
      let found_left := left.indexOfAux elem (currentIndex + 1)
      let found_left : Option (Fin (n+m+1+currentIndex)) := found_left.map λ a ↦ Fin.ofNat' a (by simp_arith)
      let found_right :=
        found_left
        <|>
        (right.indexOfAux elem (currentIndex + n + 1)).map ((λ a ↦ Fin.ofNat' a (by simp_arith)) : _ → Fin (n+m+1+currentIndex))
      found_right

/--Finds the first occurance of a given element in the heap and returns its index.-/
def BTreeHeap.indexOf {α : Type u} {lt : α → α → Bool} [BEq α] (elem : α) (heap : BTreeHeap α lt o) : Option (Fin o) :=
  indexOfAux elem heap 0

private inductive Direction
| left
| right
deriving Repr

def BTreeHeap.popLast {α : Type u} {lt : α → α → Bool} (heap : BTreeHeap α lt (o+1)) : (α × BTreeHeap α lt o) :=
  match o, heap with
  | (n+m), .branch a (left : BTreeHeap α lt n) (right : BTreeHeap α lt m) =>
    if p : 0 = (n+m) then
      (a, p▸BTreeHeap.leaf)
    else
      let leftIsFull : Bool := (n+1).nextPowerOfTwo = n+1
      let rightIsFull : Bool := (m+1).nextPowerOfTwo = m+1
      if !leftIsFull || (rightIsFull && n != m) then
        --remove left
        match n, left with
        | 0 , _ => sorry
        | (l+1),  left =>
          let (res, (newLeft : BTreeHeap α lt (l))) := left.popLast
          (res, BTreeHeap.branch a newLeft right)
      else
        --remove right
        sorry

/--Removes the element at a given index. Use `BTreeHeap.indexOf` to find the respective index.-/
def BTreeHeap.removeAt {α : Type u} {lt : α → α → Bool} {o : Nat} (index : Fin (o+1)) (heap : BTreeHeap α lt (o+1)) : BTreeHeap α lt o :=
  -- first remove the last element and remember its value
  sorry

-------------------------------------------------------------------------------------------------------

private def TestHeap := let ins : {n: Nat} → Nat → BTreeHeap Nat (λ (a b : Nat) ↦ a < b) n → BTreeHeap Nat (λ (a b : Nat) ↦ a < b) (n+1) := BTreeHeap.insert
  ins 5 (BTreeHeap.empty (λ (a b : Nat) ↦ a < b))
  |> ins 3
  |> ins 7
  |> ins 12
  |> ins 2
  |> ins 8
  |> ins 97
  |> ins 2
  |> ins 64
  |> ins 71
  |> ins 21
  --|> ins 3
  --|> ins 4
  --|> ins 199


#eval TestHeap
#eval TestHeap.indexOf 5
