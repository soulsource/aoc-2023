import Common.Nat

namespace BinaryHeap

inductive CompleteTree (α : Type u) : Nat → Type u
  | leaf : CompleteTree α 0
  | branch :
    (val : α)
    → (left : CompleteTree α n)
    → (right : CompleteTree α m)
    → m ≤ n
    → n < 2*(m+1)
    → (n+1).isPowerOfTwo ∨ (m+1).isPowerOfTwo
    → CompleteTree α (n+m+1)

def CompleteTree.root (tree : CompleteTree α n) (_ : 0 < n) : α := match tree with
| .branch a _ _ _ _ _ => a

structure TotalOrder (lt : α → α → Bool) : Prop where
  asymmetric : ∀ (a b : α), lt a b → ¬lt b a
  transitive : ∀ (a b c : α), lt a b ∧ lt b c → lt a c
  connected : ∀ (a b : α), a = b ∨ lt a b ∨ lt b a -- equivalently: a ≠ b → lt a b ∨ lt b a

def HeapPredicate {α : Type u} {n : Nat} (heap : CompleteTree α n) (lt : α → α → Bool) : Prop :=
  match heap with
  | .leaf => True
  | .branch a left right _ _ _ =>
    HeapPredicate left lt ∧ HeapPredicate right lt ∧ notSmallerOrLeaf a left ∧ notSmallerOrLeaf a right
    where notSmallerOrLeaf := λ {m : Nat} (v : α) (h : CompleteTree α m) ↦ match m with
                              | .zero => true
                              | .succ o => !lt (h.root (by simp_arith)) v

structure BinaryHeap (α : Type u) (lt : α → α → Bool) (n : Nat) where
  tree : CompleteTree α n
  valid : HeapPredicate tree lt
  wellDefinedLt : TotalOrder lt

theorem TotalOrder.irreflexive (a : α) {lt : α → α → Bool} (h₁ : TotalOrder lt) : lt a a = false :=
  if hc : lt a a = true then by
    simp[h₁.asymmetric a a hc]
  else by
    simp[hc]

theorem TotalOrder.not_lt_eq_or_lt {lt : α → α → Bool} (h₁ : TotalOrder lt) (h₂ : ¬lt a b) : a = b ∨ lt b a := by
  have h₃ := h₁.connected a b
  simp[h₂] at h₃
  assumption

theorem TotalOrder.not_lt_trans {lt : α → α → Bool} (h₁ : TotalOrder lt) : ∀ (a b c : α), ¬lt a b ∧ ¬lt b c → ¬lt a c := by
  intros a b c h₂
  have h₃ := h₁.asymmetric
  have h₄ := h₁.transitive
  have h₆ := not_lt_eq_or_lt h₁ h₂.left
  have h₇ := not_lt_eq_or_lt h₁ h₂.right
  cases h₆
  case inl h₈ =>
    cases h₇
    case inl h₉ =>
      have h₁₀ : a = c := h₈.substr h₉
      simp[h₁₀]
      exact (h₁.irreflexive c)
    case inr h₉ =>
      apply h₃
      simp[*]
  case inr h₈ =>
    cases h₇
    case inl h₉ =>
      apply h₃
      simp[←h₉,h₈]
    case inr h₉ =>
      exact h₃ c a $ h₄ c b a ⟨h₉, h₈⟩

/--Please do not use this for anything meaningful. It's a debug function, with horrible performance.-/
instance {α : Type u} [ToString α] : ToString (CompleteTree α n) where
  toString := λt ↦
    --not very fast, doesn't matter, is for debugging
    let rec max_width := λ {m : Nat} (t : (CompleteTree α m)) ↦ match m, t with
    | 0, .leaf => 0
    | (_+_+1), CompleteTree.branch a left right _ _ _ => max (ToString.toString a).length $ max (max_width left) (max_width right)
    let max_width := max_width t
    let lines_left := Nat.log2 (n+1).nextPowerOfTwo
    let rec print_line := λ (mw : Nat) {m : Nat} (t : (CompleteTree α m)) (lines : Nat)  ↦
      match m, t with
      | 0, _ => ""
      | (_+_+1), CompleteTree.branch a left right _ _ _ =>
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
def CompleteTree.length : CompleteTree α n → Nat := λ_ ↦ n

/--Creates an empty CompleteTree. Needs the heap predicate as parameter.-/
abbrev CompleteTree.empty {α : Type u} := CompleteTree.leaf (α := α)

theorem CompleteTree.emptyIsHeap {α : Type u} (lt : α → α → Bool) : HeapPredicate CompleteTree.empty lt := by trivial

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

/--Adds a new element to a given CompleteTree.-/
private def CompleteTree.heapInsert (lt : α → α → Bool) (elem : α) (heap : CompleteTree α o) : CompleteTree α (o+1) :=
  match o, heap with
  | 0, .leaf => CompleteTree.branch elem (CompleteTree.leaf) (CompleteTree.leaf) (by simp) (by simp) (by simp[Nat.one_isPowerOfTwo])
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
      let result := branch a left (right.heapInsert lt elem) (q) difference_decreased (by simp[(Nat.power_of_two_iff_next_power_eq (n+1)), r])
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
      let result := branch a (left.heapInsert lt elem) right q still_in_range (Or.inr right_is_power_of_two)
      have letMeSpellItOutForYou : n + 1 + m + 1 = n + m + 1 + 1 := by simp_arith
      letMeSpellItOutForYou ▸ result

private theorem CompleteTree.rootSeesThroughCast
  (n m : Nat)
  (h₁ : n+1+m+1=n+m+1+1)
  (h₂ : 0<n+1+m+1)
  (h₃ : 0<n+m+1+1)
  (heap : CompleteTree α (n+1+m+1)) : (h₁▸heap).root h₃ = heap.root h₂ := by
  induction m generalizing n
  case zero => simp
  case succ o ho =>
    have h₄ := ho (n+1)
    have h₅ : n+1+1+o+1 = n+1+(Nat.succ o)+1 := by simp_arith
    rewrite[h₅] at h₄
    have h₆ : n + 1 + o + 1 + 1 = n + (Nat.succ o + 1 + 1) := by simp_arith
    rewrite[h₆] at h₄
    revert heap h₁ h₂ h₃
    assumption

theorem CompleteTree.heapInsertRootSameOrElem (elem : α) (heap : CompleteTree α o) (lt : α → α → Bool) (h₂ : 0 < o): (CompleteTree.root (heap.heapInsert lt elem) (by simp_arith) = elem) ∨ (CompleteTree.root (heap.heapInsert lt elem) (by simp_arith) = CompleteTree.root heap h₂) :=
  match o, heap with
  | (n+m+1), .branch v l r _ _ _ =>
    if h : m < n ∧ Nat.nextPowerOfTwo (n + 1) = n + 1 then by
      unfold CompleteTree.heapInsert
      simp[h]
      cases (lt elem v) <;> simp[instDecidableEqBool, Bool.decEq, CompleteTree.root]
    else by
      unfold CompleteTree.heapInsert
      simp[h]
      rw[rootSeesThroughCast n m (by simp_arith) (by simp_arith) (by simp_arith)]
      cases (lt elem v)
      <;> simp[instDecidableEqBool, Bool.decEq, CompleteTree.root]

theorem CompleteTree.heapInsertEmptyElem (elem : α) (heap : CompleteTree α o) (lt : α → α → Bool) (h₂ : ¬0 < o) : (CompleteTree.root (heap.heapInsert lt elem) (by simp_arith) = elem) :=
  have : o = 0 := Nat.eq_zero_of_le_zero $ (Nat.not_lt_eq 0 o).mp h₂
  match o, heap with
  | 0, .leaf => by simp[CompleteTree.heapInsert, root]


private theorem HeapPredicate.notSmallerOrLeaf_transitive (h₁ : TotalOrder lt) : lt a b → HeapPredicate.notSmallerOrLeaf lt b h → HeapPredicate.notSmallerOrLeaf lt a h := by
  have h₂ := h₁.asymmetric
  have h₁ := h₁.not_lt_trans
  unfold notSmallerOrLeaf
  rename_i n _
  cases n <;> simp
  rename_i n
  simp at h₂
  intros h₃ h₄
  have h₅ := h₂ a b h₃
  simp at *
  exact h₁ _ _ _ ⟨h₄, h₅⟩

private theorem HeapPredicate.seesThroughCast
  (n m : Nat)
  (lt : α → α → Bool)
  (h₁ : n+1+m+1=n+m+1+1)
  (h₂ : 0<n+1+m+1)
  (h₃ : 0<n+m+1+1)
  (heap : CompleteTree α (n+1+m+1)) : HeapPredicate heap lt → HeapPredicate (h₁▸heap) lt := by
  unfold HeapPredicate
  intro h₄
  induction m generalizing n
  case zero => simp[h₄]
  case succ o ho =>
    have h₅ := ho (n+1)
    have h₆ : n+1+1+o+1 = n+1+(Nat.succ o)+1 := by simp_arith
    rw[h₆] at h₅
    have h₆ : n + 1 + o + 1 + 1 = n + (Nat.succ o + 1 + 1) := by simp_arith
    rewrite[h₆] at h₅
    revert heap h₁ h₂ h₃
    assumption

theorem CompleteTree.heapInsertIsHeap {elem : α} {heap : CompleteTree α o} {lt : α → α → Bool} (h₁ : HeapPredicate heap lt) (h₂ : TotalOrder lt) : HeapPredicate (heap.heapInsert lt elem) lt :=
  match o, heap with
  | 0, .leaf => by trivial
  | (n+m+1), .branch v l r m_le_n _ _ =>
    if h₃ : m < n ∧ Nat.nextPowerOfTwo (n + 1) = n + 1 then by
      unfold CompleteTree.heapInsert
      simp[h₃]
      cases h₄ : (lt elem v) <;> simp[instDecidableEqBool, Bool.decEq]
      <;> unfold HeapPredicate
      <;> unfold HeapPredicate at h₁
      case true =>
        have h₅ : (HeapPredicate (CompleteTree.heapInsert lt v r) lt) := CompleteTree.heapInsertIsHeap h₁.right.left h₂
        simp[h₁, h₅]
        simp[HeapPredicate.notSmallerOrLeaf_transitive h₂ h₄ h₁.right.right.left]
        have h₇ := h₂.asymmetric
        simp at h₇
        cases m
        case zero =>
          have h₆ := heapInsertEmptyElem v r lt (by simp_arith)
          simp[HeapPredicate.notSmallerOrLeaf, h₆]
          apply h₇
          assumption
        case succ _ =>
          simp[HeapPredicate.notSmallerOrLeaf]
          cases heapInsertRootSameOrElem v r lt (by simp_arith)
          <;> rename_i h₆
          <;> simp[h₆]
          apply h₇
          . assumption
          have h₈ := h₂.not_lt_trans
          simp at h₈
          apply h₈ _ v elem
          simp[h₄, h₇]
          have h₉ := h₁.right.right.right
          unfold HeapPredicate.notSmallerOrLeaf at h₉
          simp at h₉
          assumption
      case false =>
        have h₅ : (HeapPredicate (CompleteTree.heapInsert lt elem r) lt) := CompleteTree.heapInsertIsHeap h₁.right.left h₂
        simp[h₁, h₅]
        unfold HeapPredicate.notSmallerOrLeaf
        simp_arith
        cases h₆: (0 < m : Bool)
        case false =>
          have h₆ : ¬0 < m := of_decide_eq_false h₆
          have h₇ := heapInsertEmptyElem elem r lt h₆
          simp[*]
        case true =>
          simp at h₆
          have h₇ := heapInsertRootSameOrElem elem r lt h₆
          cases h₇ <;> simp[*]
          have h₈ := h₁.right.right.right
          unfold HeapPredicate.notSmallerOrLeaf at h₈
          simp at h₈
          cases m <;> simp at h₈
          case inr.zero => contradiction
          case inr.succ => simp[h₈]
    else by
      unfold CompleteTree.heapInsert
      simp[h₃]
      apply HeapPredicate.seesThroughCast <;> try simp_arith[h₂] --gets rid of annoying cast.
      -- this should be more or less identical to the other branch, just with l r m n swapped.
      -- todo: Try to make this shorter...
      cases h₄ : (lt elem v) <;> simp[instDecidableEqBool, Bool.decEq]
      <;> unfold HeapPredicate
      <;> unfold HeapPredicate at h₁
      case a.true =>
        have h₅ : (HeapPredicate (CompleteTree.heapInsert lt v l) lt) := CompleteTree.heapInsertIsHeap h₁.left h₂
        simp[h₁, h₅]
        simp[HeapPredicate.notSmallerOrLeaf_transitive h₂ h₄ h₁.right.right.right]
        have h₇ := h₂.asymmetric
        simp at h₇
        cases n
        case zero =>
          have h₆ := heapInsertEmptyElem v l lt (by simp_arith)
          simp[HeapPredicate.notSmallerOrLeaf, h₆]
          apply h₇
          assumption
        case succ _ =>
          simp[HeapPredicate.notSmallerOrLeaf]
          cases heapInsertRootSameOrElem v l lt (by simp_arith)
          <;> rename_i h₆
          <;> simp[h₆]
          apply h₇
          . assumption
          have h₈ := h₂.not_lt_trans
          simp at h₈
          apply h₈ _ v elem
          simp[h₄, h₇]
          have h₉ := h₁.right.right.left
          unfold HeapPredicate.notSmallerOrLeaf at h₉
          simp at h₉
          assumption
      case a.false =>
        have h₅ : (HeapPredicate (CompleteTree.heapInsert lt elem l) lt) := CompleteTree.heapInsertIsHeap h₁.left h₂
        simp[h₁, h₅]
        unfold HeapPredicate.notSmallerOrLeaf
        simp_arith
        cases h₆: (0 < n : Bool)
        case false =>
          have h₆ : ¬0 < n := of_decide_eq_false h₆
          have h₇ := heapInsertEmptyElem elem l lt h₆
          simp[*]
        case true =>
          simp at h₆
          have h₇ := heapInsertRootSameOrElem elem l lt h₆
          cases h₇ <;> simp[*]
          have h₈ := h₁.right.right.left
          unfold HeapPredicate.notSmallerOrLeaf at h₈
          simp at h₈
          cases n <;> simp at h₈
          case inr.zero => contradiction
          case inr.succ => simp[h₈]

def BinaryHeap.insert {α : Type u} {lt : α → α → Bool} {n : Nat} : α → BinaryHeap α lt n → BinaryHeap α lt (n+1)
| elem, BinaryHeap.mk tree valid wellDefinedLt =>
  let valid := tree.heapInsertIsHeap valid wellDefinedLt
  let tree := tree.heapInsert lt elem
  {tree, valid, wellDefinedLt}

/--Helper function for CompleteTree.indexOf.-/
def CompleteTree.indexOfAux {α : Type u} [BEq α] (elem : α) (heap : CompleteTree α o) (currentIndex : Nat) : Option (Fin (o+currentIndex)) :=
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
def CompleteTree.indexOf {α : Type u} [BEq α] (elem : α) (heap : CompleteTree α o) : Option (Fin o) :=
  indexOfAux elem heap 0

private inductive Direction
| left
| right
deriving Repr

theorem two_n_not_zero_n_not_zero (n : Nat) (p : ¬2*n = 0) : (¬n = 0) := by
  cases n
  case zero => contradiction
  case succ => simp

def CompleteTree.popLast {α : Type u} (heap : CompleteTree α (o+1)) : (α × CompleteTree α o) :=
  match o, heap with
  | (n+m), .branch a (left : CompleteTree α n) (right : CompleteTree α m) m_le_n max_height_difference subtree_complete =>
    if p : 0 = (n+m) then
      (a, p▸CompleteTree.leaf)
    else
      --let leftIsFull : Bool := (n+1).nextPowerOfTwo = n+1
      let rightIsFull : Bool := (m+1).nextPowerOfTwo = m+1
      have m_gt_0_or_rightIsFull : m > 0 ∨ rightIsFull := by cases m <;> simp_arith
      if r : m < n ∧ rightIsFull then
        --remove left
        match n, left with
        | (l+1), left =>
          let (res, (newLeft : CompleteTree α l)) := left.popLast
          have q : l + m + 1 = l + 1 +m := by simp_arith
          have s : m ≤ l := match r with
          | .intro a _ => by apply Nat.le_of_lt_succ
                             simp[a]
          have rightIsFull : (m+1).isPowerOfTwo := by
            have r := And.right r
            simp[←Nat.power_of_two_iff_next_power_eq] at r
            assumption
          have l_lt_2_m_succ : l < 2 * (m+1) := by apply Nat.lt_of_succ_lt; assumption
          (res, q▸CompleteTree.branch a newLeft right s l_lt_2_m_succ (Or.inr rightIsFull))
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
          let (res, (newRight : CompleteTree α l)) := right.popLast
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

          (res, CompleteTree.branch a left newRight s still_in_range (Or.inl leftIsFull))

/--Removes the element at a given index. Use `CompleteTree.indexOf` to find the respective index.-/
--def CompleteTree.heapRemoveAt {α : Type u} (lt : α → α → Bool) {o : Nat} (index : Fin (o+1)) (heap : CompleteTree α (o+1)) : CompleteTree α o :=
--  -- first remove the last element and remember its value
--  sorry

-------------------------------------------------------------------------------------------------------

private def TestHeap :=
  let ins : {n: Nat} → Nat → CompleteTree Nat n → CompleteTree Nat (n+1) := λ x y ↦ CompleteTree.heapInsert (.<.) x y
  ins 5 CompleteTree.empty
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
