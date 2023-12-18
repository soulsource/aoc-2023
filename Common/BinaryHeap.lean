import Common.Nat

namespace BinaryHeap

/--A heap, represented as a binary indexed tree. The heap predicate is a type parameter, the index is the element count.-/
inductive BinaryHeap (α : Type u) (lt : α → α → Bool): Nat → Type u
  | leaf : BinaryHeap α lt 0
  | branch : (val : α) → (left : BinaryHeap α lt n) → (right : BinaryHeap α lt m) → m ≤ n → n < 2*(m+1) → (n+1).isPowerOfTwo ∨ (m+1).isPowerOfTwo → BinaryHeap α lt (n+m+1)

/--Please do not use this for anything meaningful. It's a debug function, with horrible performance.-/
instance {α : Type u} {lt : α → α → Bool} [ToString α] : ToString (BinaryHeap α lt n) where
  toString := λt ↦
    --not very fast, doesn't matter, is for debugging
    let rec max_width := λ {m : Nat} (t : (BinaryHeap α lt m)) ↦ match m, t with
    | 0, .leaf => 0
    | (_+_+1), BinaryHeap.branch a left right _ _ _ => max (ToString.toString a).length $ max (max_width left) (max_width right)
    let max_width := max_width t
    let lines_left := Nat.log2 (n+1).nextPowerOfTwo
    let rec print_line := λ (mw : Nat) {m : Nat} (t : (BinaryHeap α lt m)) (lines : Nat)  ↦
      match m, t with
      | 0, _ => ""
      | (_+_+1), BinaryHeap.branch a left right _ _ _ =>
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
def BinaryHeap.length : BinaryHeap α lt n → Nat := λ_ ↦ n

/--Creates an empty BinaryHeap. Needs the heap predicate as parameter.-/
abbrev BinaryHeap.empty {α : Type u} (lt : α → α → Bool ) := BinaryHeap.leaf (α := α) (lt := lt)

theorem Nat.pred_even_odd {n : Nat} (h₁ : Nat.isEven n) (h₂ : n > 0) : Nat.isOdd n.pred := by
  cases n with
  | zero => contradiction
  | succ o => simp[Nat.isEven] at h₁
              assumption

theorem power_of_two_mul_two_lt {n m : Nat} (h₁ : m.isPowerOfTwo) (h₂ : n < 2*m) (h₃ : ¬(n+1).isPowerOfTwo) : n+1 < 2*m :=
  if h₄ : n+1 > 2*m then by
    have h₂ := Nat.succ_le_of_lt h₂
    rewrite[←Nat.not_ge_eq] at h₂
    simp_arith at h₄
    contradiction
  else if h₅ : n+1 = 2*m then by
    have h₆ := Nat.mul2_isPowerOfTwo_of_isPowerOfTwo h₁
    rewrite[Nat.mul_comm 2 m] at h₅
    rewrite[←h₅] at h₆
    contradiction
  else by
    simp_arith at h₄
    exact Nat.lt_of_le_of_ne h₄ h₅

theorem power_of_two_mul_two_le {n m : Nat} (h₁ : (n+1).isPowerOfTwo) (h₂ : n < 2*(m+1)) (h₃ : ¬(m+1).isPowerOfTwo) (h₄ : m > 0): n < 2*m :=
  if h₅ : n > 2*m then by
    simp_arith at h₂
    simp_arith at h₅
    have h₆ : n+1 = 2*(m+1) := by simp_arith[Nat.le_antisymm h₂ h₅]
    rewrite[h₆] at h₁
    rewrite[←(Nat.mul2_ispowerOfTwo_iff_isPowerOfTwo (m+1))] at h₁
    contradiction
  else if h₆ : n = 2*m then by
    -- since (n+1) is a power of 2, n cannot be an even number, but n = 2*m means it's even
    -- ha, thought I wouldn't see that, didn't you? Thought you're smarter than I, computer?
    have h₇ : n > 0 := by rewrite[h₆]
                          apply Nat.mul_lt_mul_of_pos_left h₄ (by decide :2 > 0)
    have h₈ : n ≠ 0 := Ne.symm $ Nat.ne_of_lt h₇
    have h₉ := Nat.isPowerOfTwo_even_or_one h₁
    simp[h₈] at h₉
    have h₉ := Nat.pred_even_odd h₉ (by simp_arith[h₇])
    simp at h₉
    have h₁₀ := Nat.mul_2_is_even h₆
    have h₁₀ := Nat.even_not_odd_even.mp h₁₀
    contradiction
  else by
    simp[Nat.not_gt_eq] at h₅
    have h₅ := Nat.eq_or_lt_of_le h₅
    simp[h₆] at h₅
    assumption

/--Adds a new element to a given BinaryHeap.-/
def BinaryHeap.insert (elem : α) (heap : BinaryHeap α lt o) : BinaryHeap α lt (o+1) :=
  match o, heap with
  | 0, .leaf => BinaryHeap.branch elem (BinaryHeap.leaf) (BinaryHeap.leaf) (by simp) (by simp) (by simp[Nat.one_isPowerOfTwo])
  | (n+m+1), .branch a left right p max_height_difference subtree_complete =>
    let (elem, a) := if lt elem a then (a, elem) else (elem, a)
    -- okay, based on n and m we know if we want to add left or right.
    -- the left tree is full, if (n+1) is a power of two AND n != m
    let leftIsFull := (n+1).nextPowerOfTwo = n+1
    if r : m < n ∧ leftIsFull  then
      have s : (m + 1 < n + 1) = (m < n) := by simp_arith
      have q : m + 1 ≤ n := by apply Nat.le_of_lt_succ
                               rewrite[Nat.succ_eq_add_one]
                               rewrite[s]
                               simp[r]
      have difference_decreased := Nat.le_succ_of_le $ Nat.le_succ_of_le max_height_difference
      let result := branch a left (right.insert elem) (q) difference_decreased (by simp[(Nat.power_of_two_iff_next_power_eq (n+1)), r])
      result
    else
      have q : m ≤ n+1 := by apply (Nat.le_of_succ_le)
                             simp_arith[p]
      have right_is_power_of_two : (m+1).isPowerOfTwo :=
        if s : n = m then by
          rewrite[s] at subtree_complete
          simp at subtree_complete
          exact subtree_complete
        else if h₁ : leftIsFull then by
          simp at h₁
          rewrite[Decidable.not_and_iff_or_not (m<n) leftIsFull] at r
          cases r
          case inl h₂ => rewrite[Nat.not_lt_eq] at h₂
                         have h₃ := Nat.not_le_of_gt $ Nat.lt_of_le_of_ne h₂ s
                         contradiction
          case inr h₂ => simp at h₂
                         contradiction
        else by
          simp at h₁
          rewrite[←Nat.power_of_two_iff_next_power_eq] at h₁
          cases subtree_complete
          case inl => contradiction
          case inr => trivial
      have still_in_range : n + 1 < 2 * (m + 1) := by
        rewrite[Decidable.not_and_iff_or_not (m<n) leftIsFull] at r
        cases r
        case inl h₁ => rewrite[Nat.not_gt_eq n m] at h₁
                       simp_arith[Nat.le_antisymm h₁ p]
        case inr h₁ => simp[←Nat.power_of_two_iff_next_power_eq] at h₁
                       simp[h₁] at subtree_complete
                       exact power_of_two_mul_two_lt subtree_complete max_height_difference h₁
      let result := branch a (left.insert elem) right q still_in_range (Or.inr right_is_power_of_two)
      have letMeSpellItOutForYou : n + 1 + m + 1 = n + m + 1 + 1 := by simp_arith
      letMeSpellItOutForYou ▸ result


/--Helper function for BinaryHeap.indexOf.-/
def BinaryHeap.indexOfAux {α : Type u} {lt : α → α → Bool} [BEq α] (elem : α) (heap : BinaryHeap α lt o) (currentIndex : Nat) : Option (Fin (o+currentIndex)) :=
  match o, heap with
  | 0, .leaf => none
  | (n+m+1), .branch a left right _ _ _ =>
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
def BinaryHeap.indexOf {α : Type u} {lt : α → α → Bool} [BEq α] (elem : α) (heap : BinaryHeap α lt o) : Option (Fin o) :=
  indexOfAux elem heap 0

private inductive Direction
| left
| right
deriving Repr

theorem two_n_not_zero_n_not_zero (n : Nat) (p : ¬2*n = 0) : (¬n = 0) := by
  cases n
  case zero => contradiction
  case succ => simp

def BinaryHeap.popLast {α : Type u} {lt : α → α → Bool} (heap : BinaryHeap α lt (o+1)) : (α × BinaryHeap α lt o) :=
  match o, heap with
  | (n+m), .branch a (left : BinaryHeap α lt n) (right : BinaryHeap α lt m) m_le_n max_height_difference subtree_complete =>
    if p : 0 = (n+m) then
      (a, p▸BinaryHeap.leaf)
    else
      --let leftIsFull : Bool := (n+1).nextPowerOfTwo = n+1
      let rightIsFull : Bool := (m+1).nextPowerOfTwo = m+1
      have m_gt_0_or_rightIsFull : m > 0 ∨ rightIsFull := by cases m <;> simp_arith
      if r : m < n ∧ rightIsFull then
        --remove left
        match n, left with
        | (l+1), left =>
          let (res, (newLeft : BinaryHeap α lt l)) := left.popLast
          have q : l + m + 1 = l + 1 +m := by simp_arith
          have s : m ≤ l := match r with
          | .intro a _ => by apply Nat.le_of_lt_succ
                             simp[a]
          have rightIsFull : (m+1).isPowerOfTwo := by
            have r := And.right r
            simp[←Nat.power_of_two_iff_next_power_eq] at r
            assumption
          have l_lt_2_m_succ : l < 2 * (m+1) := by apply Nat.lt_of_succ_lt; assumption
          (res, q▸BinaryHeap.branch a newLeft right s l_lt_2_m_succ (Or.inr rightIsFull))
      else
        --remove right
        have : m > 0 := by
          cases m_gt_0_or_rightIsFull
          case inl => assumption
          case inr h => simp_arith [h] at r
                        -- p, r, m_le_n combined
                        -- r and m_le_n yield m == n and p again done
                        simp_arith
                        --clear left right heap lt a h rightIsFull
                        have n_eq_m : n = m := Nat.le_antisymm r m_le_n
                        rewrite[n_eq_m] at p
                        simp_arith at p
                        apply Nat.zero_lt_of_ne_zero
                        simp_arith[p]
                        apply (two_n_not_zero_n_not_zero m)
                        intro g
                        have g := Eq.symm g
                        revert g
                        assumption
        match h₂ : m, right with
        | (l+1), right =>
          let (res, (newRight : BinaryHeap α lt l)) := right.popLast
          have s : l ≤ n := by have x := (Nat.add_le_add_left (Nat.zero_le 1) l)
                               have x := Nat.le_trans x m_le_n
                               assumption
          have leftIsFull : (n+1).isPowerOfTwo := by
            rewrite[Decidable.not_and_iff_or_not] at r
            cases r
            case inl h₁ => rewrite[Nat.not_lt_eq] at h₁
                           have h₂ := Nat.le_antisymm h₁ m_le_n
                           rewrite[←h₂] at subtree_complete
                           simp at subtree_complete
                           assumption
            case inr h₁ => simp_arith[←Nat.power_of_two_iff_next_power_eq] at h₁
                           rewrite[h₂] at h₁
                           simp[h₁] at subtree_complete
                           assumption
          have still_in_range : n < 2*(l+1) := by
            rewrite[Decidable.not_and_iff_or_not (l+1<n) rightIsFull] at r
            cases r with
            | inl h₁ => simp_arith at h₁
                        have h₃ := Nat.le_antisymm m_le_n h₁
                        subst n
                        have h₄ := Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) this
                        simp at h₄
                        assumption
            | inr h₁ => simp[←Nat.power_of_two_iff_next_power_eq, h₂] at h₁
                        apply power_of_two_mul_two_le <;> assumption

          (res, BinaryHeap.branch a left newRight s still_in_range (Or.inl leftIsFull))

/--Removes the element at a given index. Use `BinaryHeap.indexOf` to find the respective index.-/
def BinaryHeap.removeAt {α : Type u} {lt : α → α → Bool} {o : Nat} (index : Fin (o+1)) (heap : BinaryHeap α lt (o+1)) : BinaryHeap α lt o :=
  -- first remove the last element and remember its value
  sorry

-------------------------------------------------------------------------------------------------------

private def TestHeap := let ins : {n: Nat} → Nat → BinaryHeap Nat (λ (a b : Nat) ↦ a < b) n → BinaryHeap Nat (λ (a b : Nat) ↦ a < b) (n+1) := BinaryHeap.insert
  ins 5 (BinaryHeap.empty (λ (a b : Nat) ↦ a < b))
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
  |> ins 3
  |> ins 4
  |> ins 199
  |> ins 24
  |> ins 3

#eval TestHeap
#eval TestHeap.popLast
#eval TestHeap.indexOf 71
