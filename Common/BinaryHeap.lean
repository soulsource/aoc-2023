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

/-- Returns the element stored in the root node. -/
def CompleteTree.root (tree : CompleteTree α n) (_ : 0 < n) : α := match tree with
| .branch a _ _ _ _ _ => a

/-- Same as CompleteTree.root, but a bit more ergonomic to use. However, CompleteTree.root is better suited for proofs-/
def CompleteTree.root' (tree : CompleteTree α (n+1)) : α := tree.root (Nat.zero_lt_succ n)

def transitive_le {α : Type u} (le : α → α → Bool) : Prop := ∀(a b c : α), (le a b) ∧ (le b c) → le a c
def total_le {α : Type u} (le : α → α → Bool) : Prop := ∀(a b : α), le a b ∨ le b a

def not_le_imp_le {α : Type u} {le : α → α → Bool} (h₁ : total_le le) : ∀(a b : α), ¬le a b → le b a := by
  intros a b h₂
  have h₁ := h₁ a b
  cases h₁
  . contradiction
  . trivial

def HeapPredicate {α : Type u} {n : Nat} (heap : CompleteTree α n) (le : α → α → Bool) : Prop :=
  match heap with
  | .leaf => True
  | .branch a left right _ _ _ =>
    HeapPredicate left le ∧ HeapPredicate right le ∧ leOrLeaf a left ∧ leOrLeaf a right
    where leOrLeaf := λ {m : Nat} (v : α) (h : CompleteTree α m) ↦ match m with
                              | .zero => true
                              | .succ o => le v (h.root (by simp_arith))

structure BinaryHeap (α : Type u) (le : α → α → Bool) (n : Nat) where
  tree : CompleteTree α n
  valid : HeapPredicate tree le
  wellDefinedLe : transitive_le le ∧ total_le le

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

/-- Returns the lenght of the left sub-tree. Mostly exists as a helper for expressing the return type of CompleteTree.left -/
def CompleteTree.leftLen (tree : CompleteTree α n) (_ : n > 0) : Nat := match n, tree with
| (_+_), .branch _ l _ _ _ _ => l.length

def CompleteTree.leftLen' (tree : CompleteTree α (n+1)) : Nat := tree.leftLen (Nat.zero_lt_succ n)

/-- Returns the lenght of the right sub-tree. Mostly exists as a helper for expressing the return type of CompleteTree.right -/
def CompleteTree.rightLen (tree : CompleteTree α n) (_ : n > 0) : Nat := match n, tree with
| (_+_), .branch _ _ r _ _ _ => r.length

def CompleteTree.rightLen' (tree : CompleteTree α (n+1)) : Nat := tree.rightLen (Nat.zero_lt_succ n)

def CompleteTree.left (tree : CompleteTree α n) (h₁ : n > 0) : CompleteTree α (tree.leftLen h₁) := match n, tree with
| (_+_), .branch _ l _ _ _ _ => l

def CompleteTree.left' (tree : CompleteTree α (n+1)) : CompleteTree α (tree.leftLen (Nat.zero_lt_succ n)) := tree.left (Nat.zero_lt_succ n)

def CompleteTree.right (tree : CompleteTree α n) (h₁ : n > 0) : CompleteTree α (tree.rightLen h₁) := match n, tree with
| (_+_), .branch _ _ r _ _ _ => r

def CompleteTree.right' (tree : CompleteTree α (n+1)) : CompleteTree α (tree.rightLen (Nat.zero_lt_succ n)) := tree.right (Nat.zero_lt_succ n)

/--Creates an empty CompleteTree. Needs the heap predicate as parameter.-/
abbrev CompleteTree.empty {α : Type u} := CompleteTree.leaf (α := α)

theorem CompleteTree.emptyIsHeap {α : Type u} (le : α → α → Bool) : HeapPredicate CompleteTree.empty le := by trivial

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
private def CompleteTree.heapInsert (le : α → α → Bool) (elem : α) (heap : CompleteTree α o) : CompleteTree α (o+1) :=
  match o, heap with
  | 0, .leaf => CompleteTree.branch elem (CompleteTree.leaf) (CompleteTree.leaf) (by simp) (by simp) (by simp[Nat.one_isPowerOfTwo])
  | (n+m+1), .branch a left right p max_height_difference subtree_complete =>
    let (elem, a) := if le elem a then (a, elem) else (elem, a)
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
      let result := branch a left (right.heapInsert le elem) (q) difference_decreased (by simp[(Nat.power_of_two_iff_next_power_eq (n+1)), r])
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
          rewrite[Decidable.not_and_iff_or_not (m<n) leftIsFull] at r
          cases r
          case inl h₂ => rewrite[Nat.not_lt_eq] at h₂
                         have h₃ := Nat.not_le_of_gt $ Nat.lt_of_le_of_ne h₂ s
                         contradiction
          case inr h₂ => simp at h₂
                         contradiction
        else by
          simp[leftIsFull] at h₁
          rewrite[←Nat.power_of_two_iff_next_power_eq] at h₁
          cases subtree_complete
          case inl => contradiction
          case inr => trivial
      have still_in_range : n + 1 < 2 * (m + 1) := by
        rewrite[Decidable.not_and_iff_or_not (m<n) leftIsFull] at r
        cases r
        case inl h₁ => rewrite[Nat.not_gt_eq n m] at h₁
                       simp_arith[Nat.le_antisymm h₁ p]
        case inr h₁ => simp[←Nat.power_of_two_iff_next_power_eq, leftIsFull] at h₁
                       simp[h₁] at subtree_complete
                       exact power_of_two_mul_two_lt subtree_complete max_height_difference h₁
      let result := branch a (left.heapInsert le elem) right q still_in_range (Or.inr right_is_power_of_two)
      have letMeSpellItOutForYou : n + 1 + m + 1 = n + m + 1 + 1 := by simp_arith
      letMeSpellItOutForYou ▸ result

private theorem CompleteTree.rootSeesThroughCast
  (n m : Nat)
  (h₁ : n + 1 + m = n + m + 1)
  (h₂ : 0 < n + 1 + m)
  (h₃ : 0 < n + m + 1)
  (heap : CompleteTree α (n+1+m)) : (h₁▸heap).root h₃ = heap.root h₂ := by
  induction m generalizing n
  case zero => simp
  case succ o ho =>
    have h₄ := ho (n+1)
    have h₅ : n + 1 + 1 + o = n + 1 + (Nat.succ o) := by simp_arith
    have h₆ : n + 1 + o + 1 = n + (Nat.succ o + 1) := by simp_arith
    rewrite[h₅, h₆] at h₄
    revert heap h₁ h₂ h₃
    assumption

--- Same as rootSeesThroughCast, but in the other direction.
private theorem CompleteTree.rootSeesThroughCast2
  (n m : Nat)
  (h₁ : n + m + 1 = n + 1 + m)
  (h₂ : 0 < n + m + 1)
  (h₃ : 0 < n + 1 + m)
  (heap : CompleteTree α (n+m+1)) : (h₁▸heap).root h₃ = heap.root h₂ := by
  induction m generalizing n
  case zero => simp
  case succ mm mh =>
    have h₄ := mh (n+1)
    have h₅ : n + 1 + mm + 1 = n + Nat.succ mm + 1 := by simp_arith
    have h₆ : n + 1 + 1 + mm = n + 1 + Nat.succ mm := by simp_arith
    rw[h₅, h₆] at h₄
    revert heap h₁ h₂ h₃
    assumption

theorem CompleteTree.heapInsertRootSameOrElem (elem : α) (heap : CompleteTree α o) (lt : α → α → Bool) (h₂ : 0 < o): (CompleteTree.root (heap.heapInsert lt elem) (by simp_arith) = elem) ∨ (CompleteTree.root (heap.heapInsert lt elem) (by simp_arith) = CompleteTree.root heap h₂) := by
  unfold heapInsert
  split --match o, heap
  contradiction
  simp
  rename_i n m v l r _ _ _
  split -- if h : m < n ∧ Nat.nextPowerOfTwo (n + 1) = n + 1 then
  case h_2.isTrue h =>
    cases (lt elem v) <;> simp[instDecidableEqBool, Bool.decEq, CompleteTree.root]
  case h_2.isFalse h =>
    rw[rootSeesThroughCast n (m+1) (by simp_arith) (by simp_arith) (by simp_arith)]
    cases (lt elem v)
     <;> simp[instDecidableEqBool, Bool.decEq, CompleteTree.root]

theorem CompleteTree.heapInsertEmptyElem (elem : α) (heap : CompleteTree α o) (lt : α → α → Bool) (h₂ : ¬0 < o) : (CompleteTree.root (heap.heapInsert lt elem) (by simp_arith) = elem) :=
  have : o = 0 := Nat.eq_zero_of_le_zero $ (Nat.not_lt_eq 0 o).mp h₂
  match o, heap with
  | 0, .leaf => by simp[CompleteTree.heapInsert, root]


private theorem HeapPredicate.leOrLeaf_transitive (h₁ : transitive_le le) : le a b → HeapPredicate.leOrLeaf le b h → HeapPredicate.leOrLeaf le a h := by
  unfold leOrLeaf
  intros h₂ h₃
  rename_i n
  cases n <;> simp
  apply h₁ a b _
  simp[*]

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

theorem CompleteTree.heapInsertIsHeap {elem : α} {heap : CompleteTree α o} {le : α → α → Bool} (h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate (heap.heapInsert le elem) le := by
  unfold heapInsert
  split -- match o, heap with
  trivial
  case h_2 n m v l r m_le_n _ _ =>
    simp
    split -- if h₅ : m < n ∧ Nat.nextPowerOfTwo (n + 1) = n + 1 then
    case isTrue h₅ =>
      cases h₆ : (le elem v) <;> simp[instDecidableEqBool, Bool.decEq]
      <;> unfold HeapPredicate
      <;> unfold HeapPredicate at h₁
      case true =>
        have h₇ : (HeapPredicate (CompleteTree.heapInsert le v r) le) := CompleteTree.heapInsertIsHeap h₁.right.left h₂ h₃
        simp[h₁, h₇]
        simp[HeapPredicate.leOrLeaf_transitive h₂ h₆ h₁.right.right.left]
        cases m
        case zero =>
          have h₇ := heapInsertEmptyElem v r le (by simp_arith)
          simp[HeapPredicate.leOrLeaf, h₇]
          assumption
        case succ _ =>
          simp[HeapPredicate.leOrLeaf]
          cases heapInsertRootSameOrElem v r le (by simp_arith)
          <;> rename_i h₇
          <;> rw[h₇]
          . assumption
          apply h₂ elem v
          simp[h₆]
          exact h₁.right.right.right
      case false =>
        have h₇ : (HeapPredicate (CompleteTree.heapInsert le elem r) le) := CompleteTree.heapInsertIsHeap h₁.right.left h₂ h₃
        simp[h₁, h₇]
        have h₈ : le v elem := not_le_imp_le h₃ elem v (by simp[h₆])
        cases m
        case zero =>
          have h₇ := heapInsertEmptyElem elem r le (by simp_arith)
          simp[HeapPredicate.leOrLeaf, h₇]
          assumption
        case succ _ =>
          cases heapInsertRootSameOrElem elem r le (by simp_arith)
          <;> rename_i h₉
          <;> simp[HeapPredicate.leOrLeaf, h₉, h₈]
          exact h₁.right.right.right
    case isFalse h₅ =>
      apply HeapPredicate.seesThroughCast <;> try simp_arith[h₂] --gets rid of annoying cast.
      -- this should be more or less identical to the other branch, just with l r m n swapped.
      -- todo: Try to make this shorter...
      cases h₆ : (le elem v) <;> simp[instDecidableEqBool, Bool.decEq]
      <;> unfold HeapPredicate
      <;> unfold HeapPredicate at h₁
      case a.true =>
        have h₇ : (HeapPredicate (CompleteTree.heapInsert le v l) le) := CompleteTree.heapInsertIsHeap h₁.left h₂ h₃
        simp[h₁, h₇]
        simp[HeapPredicate.leOrLeaf_transitive h₂ h₆ h₁.right.right.right]
        cases n
        case zero =>
          have h₇ := heapInsertEmptyElem v l le (by simp)
          simp[HeapPredicate.leOrLeaf, h₇]
          assumption
        case succ _ =>
          simp[HeapPredicate.leOrLeaf]
          cases heapInsertRootSameOrElem v l le (by simp_arith)
          <;> rename_i h₇
          <;> rw[h₇]
          . assumption
          apply h₂ elem v
          simp[h₆]
          exact h₁.right.right.left
      case a.false =>
        have h₇ : (HeapPredicate (CompleteTree.heapInsert le elem l) le) := CompleteTree.heapInsertIsHeap h₁.left h₂ h₃
        simp[h₁, h₇]
        have h₈ : le v elem := not_le_imp_le h₃ elem v (by simp[h₆])
        cases n
        case zero =>
          have h₇ := heapInsertEmptyElem elem l le (by simp)
          simp[HeapPredicate.leOrLeaf, h₇]
          assumption
        case succ _ =>
          cases heapInsertRootSameOrElem elem l le (by simp_arith)
          <;> rename_i h₉
          <;> simp[HeapPredicate.leOrLeaf, h₉, h₈]
          exact h₁.right.right.left

def BinaryHeap.insert {α : Type u} {lt : α → α → Bool} {n : Nat} : α → BinaryHeap α lt n → BinaryHeap α lt (n+1)
| elem, BinaryHeap.mk tree valid wellDefinedLe =>
  let valid := tree.heapInsertIsHeap valid wellDefinedLe.left wellDefinedLe.right
  let tree := tree.heapInsert lt elem
  {tree, valid, wellDefinedLe}

/--Helper function for CompleteTree.indexOf.-/
def CompleteTree.indexOfAux {α : Type u} (heap : CompleteTree α o) (pred : α → Bool) (currentIndex : Nat) : Option (Fin (o+currentIndex)) :=
  match o, heap with
  | 0, .leaf => none
  | (n+m+1), .branch a left right _ _ _ =>
    if pred a then
      let result := Fin.ofNat' currentIndex (by simp_arith)
      some result
    else
      let found_left := left.indexOfAux pred (currentIndex + 1)
      let found_left : Option (Fin (n+m+1+currentIndex)) := found_left.map λ a ↦ Fin.ofNat' a (by simp_arith)
      let found_right :=
        found_left
        <|>
        (right.indexOfAux pred (currentIndex + n + 1)).map ((λ a ↦ Fin.ofNat' a (by simp_arith)) : _ → Fin (n+m+1+currentIndex))
      found_right

/--Finds the first occurance of a given element in the heap and returns its index.-/
def CompleteTree.indexOf {α : Type u} (heap : CompleteTree α o) (pred : α → Bool) : Option (Fin o) :=
  indexOfAux heap pred 0

def CompleteTree.get {α : Type u} {n : Nat} (index : Fin (n+1)) (heap : CompleteTree α (n+1)) : α :=
  match h₁ : index, h₂ : n, heap with
  | 0, (_+_), .branch v _ _ _ _ _ => v
  | ⟨j+1,h₃⟩, (o+p), .branch _ l r _ _ _ =>
    if h₄ : j < o then
      match o with
      | (oo+1) => get ⟨j, h₄⟩ l
    else
      have h₅ : n - o = p := Nat.sub_eq_of_eq_add $ (Nat.add_comm o p).subst h₂
      have : p ≠ 0 :=
        have h₆ : o < n := Nat.lt_of_le_of_lt (Nat.ge_of_not_lt h₄) (Nat.lt_of_succ_lt_succ h₃)
        h₅.symm.substr $ Nat.sub_ne_zero_of_lt h₆
      have h₆ : j - o < p := h₅.subst $ Nat.sub_lt_sub_right (Nat.ge_of_not_lt h₄) $ Nat.lt_of_succ_lt_succ h₃
      have : j - o < index.val := by simp_arith[h₁, Nat.sub_le]
      match p with
      | (pp + 1) => get ⟨j - o, h₆⟩ r


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
      have m_gt_0_or_rightIsFull : m > 0 ∨ rightIsFull := by cases m <;> simp_arith (config := { ground:=true })[rightIsFull]
      if r : m < n ∧ rightIsFull then
        --remove left
        match n, left with
        | (l+1), left =>
          let (res, (newLeft : CompleteTree α l)) := left.popLast
          have q : l + m + 1 = l + 1 + m := Nat.add_right_comm l m 1
          have s : m ≤ l := match r with
          | .intro a _ => by apply Nat.le_of_lt_succ
                             simp[a]
          have rightIsFull : (m+1).isPowerOfTwo := by
            have r := And.right r
            simp (config := {zetaDelta := true })[←Nat.power_of_two_iff_next_power_eq] at r
            assumption
          have l_lt_2_m_succ : l < 2 * (m+1) := by apply Nat.lt_of_succ_lt; assumption
          (res, q▸CompleteTree.branch a newLeft right s l_lt_2_m_succ (Or.inr rightIsFull))
      else
        --remove right
        have m_gt_0 : m > 0 := by
          cases m_gt_0_or_rightIsFull
          case inl => assumption
          case inr h =>
            simp_arith [h] at r
            cases n
            case zero =>
              simp[Nat.zero_lt_of_ne_zero] at p
              exact Nat.zero_lt_of_ne_zero (Ne.symm p)
            case succ q =>
              cases m
              . have := Nat.not_succ_le_zero q
                contradiction
              . simp_arith
        let l := m.pred
        have h₂ : l.succ = m := (Nat.succ_pred $ Nat.not_eq_zero_of_lt (Nat.gt_of_not_le $ Nat.not_le_of_gt m_gt_0))
        let (res, (newRight : CompleteTree α l)) := (h₂.symm▸right).popLast
        have s : l ≤ n := Nat.le_trans ((Nat.add_zero l).subst (motive := λ x ↦ x ≤ m) $ h₂.subst (Nat.add_le_add_left (Nat.zero_le 1) l)) (h₂.substr m_le_n)
        have leftIsFull : (n+1).isPowerOfTwo := by
          rewrite[Decidable.not_and_iff_or_not] at r
          cases r
          case inl h₁ => rewrite[Nat.not_lt_eq] at h₁
                         have h₂ := Nat.le_antisymm h₁ m_le_n
                         rewrite[←h₂] at subtree_complete
                         simp at subtree_complete
                         assumption
          case inr h₁ => simp_arith(config := {zetaDelta := true })[←Nat.power_of_two_iff_next_power_eq] at h₁
                         simp[h₁] at subtree_complete
                         assumption
        have still_in_range : n < 2*(l+1) := by
          rewrite[Decidable.not_and_iff_or_not (m<n) rightIsFull] at r
          rw[←Nat.add_one] at h₂
          cases r with
          | inl h₁ => simp_arith at h₁
                      have h₃ := Nat.le_antisymm m_le_n h₁
                      subst n
                      have h₄ := Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) m_gt_0
                      simp at h₄
                      rw[h₂]
                      assumption
          | inr h₁ => simp(config := {zetaDelta := true })[←Nat.power_of_two_iff_next_power_eq, h₂] at h₁
                      rw[h₂]
                      apply power_of_two_mul_two_le <;> assumption
        (res, h₂▸CompleteTree.branch a left newRight s still_in_range (Or.inl leftIsFull))


theorem CompleteTree.castZeroHeap (n m : Nat) (heap : CompleteTree α 0) (h₁ : 0=n+m) {le : α → α → Bool} : HeapPredicate (h₁ ▸ heap) le := by
  have h₂ : heap = (CompleteTree.empty : CompleteTree α 0) := by
    simp[empty]
    match heap with
    | .leaf => trivial
  have h₂ : HeapPredicate heap le := by simp[h₂, empty, emptyIsHeap]
  cases m
  case succ => contradiction
  case zero =>
    cases n
    case succ => contradiction
    case zero =>
      simp[h₁, h₂]

private theorem HeapPredicate.seesThroughCast2
  (n m : Nat)
  (lt : α → α → Bool)
  (h₁ : n+m+1=n+1+m)
  (h₂ : 0<n+1+m)
  (h₃ : 0<n+m+1)
  (heap : CompleteTree α (n+m+1)) : HeapPredicate heap lt → HeapPredicate (h₁▸heap) lt := by
  unfold HeapPredicate
  intro h₄
  induction m generalizing n
  case zero => simp[h₄]
  case succ o ho =>
    have h₅ := ho (n+1)
    have h₆ : n+1+o+1 = n+(Nat.succ o)+1 := by simp_arith
    rw[h₆] at h₅
    have h₆ : n + 1 + 1 + o = n + 1 + Nat.succ o := by simp_arith
    rewrite[h₆] at h₅
    revert heap h₁ h₂ h₃
    assumption

-- If there is only one element left, the result is a leaf.
theorem CompleteTree.popLastLeaf (heap : CompleteTree α 1) : heap.popLast.snd = CompleteTree.leaf := by
  let l := heap.popLast.snd
  have h₁ : l = CompleteTree.leaf := match l with
    | .leaf => rfl
  exact h₁

theorem CompleteTree.popLastLeavesRoot (heap : CompleteTree α (n+1)) (h₁ : n > 0) : heap.root (Nat.zero_lt_of_ne_zero $ Nat.succ_ne_zero n) = heap.popLast.snd.root (h₁) := by
  unfold popLast
  split
  rename_i o p v l r _ _ _
  have h₃ : (0 ≠ o + p) := Ne.symm $ Nat.not_eq_zero_of_lt h₁
  simp[h₃]
  exact
    if h₄ : p < o ∧ Nat.nextPowerOfTwo (p + 1) = p + 1 then by
      simp[h₄]
      cases o
      case zero => exact absurd h₄.left $ Nat.not_lt_zero p
      case succ oo _ _ _ =>
        simp -- redundant, but makes goal easier to read
        rw[rootSeesThroughCast2 oo p _ (by simp_arith) _]
        unfold root
        simp
    else by
      simp[h₄]
      cases p
      case zero =>
        simp_arith at h₁ -- basically o ≠ 0
        simp_arith (config := {ground := true})[h₁] at h₄ -- the second term in h₄ is decidable and True. What remains is ¬(0 < o), or o = 0
      case succ pp hp =>
        simp_arith
        unfold root
        simp


set_option linter.unusedVariables false in -- Lean 4.2 thinks h₁ is unused. It very much is not unused.
theorem CompleteTree.popLastIsHeap {heap : CompleteTree α (o+1)} {le : α → α → Bool} (h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate (heap.popLast.snd) le := by
  unfold popLast
  split
  rename_i n m v l r _ _ _
  exact
    if h₄ : 0 = (n+m) then by
      simp[h₄, castZeroHeap]
    else by
      simp[h₄]
      exact
        if h₅ : (m<n ∧ Nat.nextPowerOfTwo (m+1) = m+1) then by
          simp[h₅]
          cases n
          case zero =>
            exact absurd h₅.left $ Nat.not_lt_zero m
          case succ ll h₆ h₇ h₈  =>
            simp
            apply HeapPredicate.seesThroughCast2 <;> try simp_arith
            cases ll
            case a.zero => -- if ll is zero, then (popLast l).snd is a leaf.
              have h₆ : l.popLast.snd = .leaf := popLastLeaf l
              rw[h₆]
              unfold HeapPredicate at *
              have h₇ : HeapPredicate .leaf le := by trivial
              have h₈ : HeapPredicate.leOrLeaf le v .leaf := by trivial
              exact ⟨h₇,h₁.right.left, h₈, h₁.right.right.right⟩
            case a.succ nn => -- if ll is not zero, then the root element before and after popLast is the same.
              unfold HeapPredicate at *
              simp[h₁.right.left, h₁.right.right.right, popLastIsHeap h₁.left h₂ h₃]
              unfold HeapPredicate.leOrLeaf
              simp
              rw[←popLastLeavesRoot]
              exact h₁.right.right.left
        else by
          simp[h₅]
          cases m
          case zero =>
            simp_arith at h₄ -- n ≠ 0
            simp_arith (config :={ground:=true})[Ne.symm h₄] at h₅ -- the second term in h₅ is decidable and True. What remains is ¬(0 < n), or n = 0
          case succ mm h₆ h₇ h₈ =>
            simp
            unfold HeapPredicate at *
            simp[h₁, popLastIsHeap h₁.right.left h₂ h₃]
            unfold HeapPredicate.leOrLeaf
            exact match mm with
            | 0 => rfl
            | o+1 =>
              have h₉ : le v ((r.popLast).snd.root (Nat.zero_lt_succ o)) := by
                rw[←popLastLeavesRoot]
                exact h₁.right.right.right
              h₉

def BinaryHeap.popLast {α : Type u} {le : α → α → Bool} {n : Nat} : (BinaryHeap α le (n+1)) → (α × BinaryHeap α le n)
| {tree, valid, wellDefinedLe} =>
  let result := tree.popLast
  let resultValid := CompleteTree.popLastIsHeap valid wellDefinedLe.left wellDefinedLe.right
  (result.fst, { tree := result.snd, valid := resultValid, wellDefinedLe})

/--
  Helper for CompleteTree.heapReplaceElementAt. Makes proofing heap predicate work in Lean 4.9
  -/
def CompleteTree.heapReplaceRoot  {α : Type u} {n : Nat} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) : α × CompleteTree α n :=
match n, heap with
  | (o+p+1), .branch v l r h₃ h₄ h₅ =>
    if h₆ : o = 0 then
      -- have : p = 0 := (Nat.le_zero_eq p).mp $ h₇.subst h₃ --not needed, left here for reference
      (v, .branch value l r h₃ h₄ h₅)
    else
      have h₇ : o > 0 := Nat.zero_lt_of_ne_zero h₆
      let lr := l.root h₇
      if h₈ : p = 0 then
        if le value lr then
          (v, .branch value l r h₃ h₄ h₅)
        else
          -- We would not need to recurse further, because we know o = 1.
          -- However, that would introduce type casts, what makes proving harder...
          -- have h₉: o = 1 := Nat.le_antisymm (by simp_arith[h₈] at h₄; exact h₄) (Nat.succ_le_of_lt h₇)
          let ln := heapReplaceRoot le value l h₇
          (v, .branch ln.fst ln.snd r h₃ h₄ h₅)
      else
        have h₉ : p > 0 := Nat.zero_lt_of_ne_zero h₈
        let rr := r.root h₉
        if le value lr ∧ le value rr then
          (v, .branch value l r h₃ h₄ h₅)
        else if le lr rr then -- value is gt either left or right root. Move it down accordingly
          let ln := heapReplaceRoot le value l h₇
          (v, .branch ln.fst ln.snd r h₃ h₄ h₅)
        else
          let rn := heapReplaceRoot le value r h₉
          (v, .branch rn.fst l rn.snd h₃ h₄ h₅)
/--
  Helper for CompleteTree.heapRemoveAt.
  Removes the element at index, and instead inserts the given value.
  Returns the element at index, and the resulting tree.
  -/
def CompleteTree.heapReplaceElementAt {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) : α × CompleteTree α n :=
  if h₂ : index == ⟨0,h₁⟩ then
    heapReplaceRoot le value heap h₁
  else
    match n, heap with
    | (o+p+1), .branch v l r h₃ h₄ h₅ =>
      let (v, value) := if le v value then (v, value) else (value, v)
      if h₆ : index ≤ o then
        have h₇ : Nat.pred index.val < o := Nat.lt_of_lt_of_le (Nat.pred_lt $ Fin.val_ne_of_ne (ne_of_beq_false $ Bool.of_not_eq_true h₂)) h₆
        let index_in_left : Fin o := ⟨index.val.pred, h₇⟩
        have h₈ : 0 < o := Nat.zero_lt_of_lt h₇
        let result := heapReplaceElementAt le index_in_left value l h₈
        (result.fst, .branch v result.snd r h₃ h₄ h₅)
      else
        have h₇ : index.val - (o + 1) < p :=
          -- tactic rewrite failed, result is not type correct.
          have h₈ : index.val < p + o + 1 := index.isLt
            |> (Nat.add_assoc o p 1).subst
            |> (Nat.add_comm p 1).subst (motive := λx ↦ index.val < o + x)
            |> (Nat.add_assoc o 1 p).symm.subst
            |> (Nat.add_comm (o+1) p).subst
          Nat.sub_lt_of_lt_add h₈ $ (Nat.not_le_eq index.val o).mp h₆
        let index_in_right : Fin p := ⟨index.val - o - 1, h₇⟩
        have h₈ : 0 < p := Nat.zero_lt_of_lt h₇
        let result := heapReplaceElementAt le index_in_right value r h₈
        (result.fst, .branch v l result.snd h₃ h₄ h₅)

private theorem CompleteTree.heapReplaceRootReturnsRoot {α : Type u} {n : Nat} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) : (heap.heapReplaceRoot le value h₁).fst = heap.root h₁ := by
  unfold heapReplaceRoot
  split
  rename_i o p v l r h₃ h₄ h₅ h₁
  simp
  cases o <;> simp
  case zero =>
    unfold root
    simp
  case succ =>
    cases p <;> simp
    case zero =>
      cases le value (root l _)
      <;> simp
      <;> unfold root
      <;> simp
    case succ =>
      cases le value (root l _) <;> cases le value (root r _)
      <;> simp
      case true.true =>
        unfold root
        simp
      case true.false | false.true | false.false =>
        cases le (root l _) (root r _)
        <;> simp
        <;> unfold root
        <;> simp

private theorem CompleteTree.heapReplaceRootPossibleRootValuesAuxL {α : Type u} (heap : CompleteTree α n) (h₁ : n > 1) : 0 < heap.leftLen (Nat.lt_trans (Nat.lt_succ_self 0) h₁) :=
  match h₅: n, heap with
  | (o+p+1), .branch v l r h₂ h₃ h₄ => by
    simp[leftLen, length]
    cases o
    case zero => rewrite[(Nat.le_zero_eq p).mp h₂] at h₁; contradiction
    case succ q => exact Nat.zero_lt_succ q

private theorem CompleteTree.heapReplaceRootPossibleRootValuesAuxR {α : Type u} (heap : CompleteTree α n) (h₁ : n > 2) : 0 < heap.rightLen (Nat.lt_trans (Nat.lt_succ_self 0) $ Nat.lt_trans (Nat.lt_succ_self 1) h₁) :=
  match h₅: n, heap with
  | (o+p+1), .branch v l r h₂ h₃ h₄ => by
    simp[rightLen, length]
    cases p
    case zero => simp_arith at h₁; simp at h₃; exact absurd h₁ (Nat.not_le_of_gt h₃)
    case succ q => exact Nat.zero_lt_succ q

private theorem CompleteTree.heapReplaceRootPossibleRootValues1Aux {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n = 1) (hx : n > 0) : (heap.heapReplaceRoot le value (hx)).snd.root (hx) = value := by
  unfold heapReplaceRoot
  split
  rename_i o p v l r _ _ _ h₁
  have h₃ : o + p = 0 := Nat.succ.inj h₁
  have h₃ : o = 0 := (Nat.add_eq_zero.mp h₃).left
  unfold root
  simp_all

private theorem CompleteTree.heapReplaceRootPossibleRootValues1 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n = 1) : (heap.heapReplaceRoot le value (by simp[h₁])).snd.root (by simp[h₁]) = value :=
  heapReplaceRootPossibleRootValues1Aux le value heap h₁ (by simp[h₁])

private theorem CompleteTree.heapReplaceRootPossibleRootValues2 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n = 2) :
have h₂ : 0 < n := Nat.lt_trans (Nat.lt_succ_self 0) $  h₁.substr (Nat.lt_succ_self 1)
have h₃ : 0 < leftLen heap h₂ := heapReplaceRootPossibleRootValuesAuxL heap (h₁.substr (Nat.lt_succ_self 1))
(heap.heapReplaceRoot le value h₂).snd.root h₂ = value
∨ (heap.heapReplaceRoot le value h₂).snd.root h₂ = (heap.left h₂).root h₃
:=
  sorry

private theorem CompleteTree.heapReplaceRootPossibleRootValues3 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 2) :
have h₂ : 0 < n := Nat.lt_trans (Nat.lt_succ_self 0) $ Nat.lt_trans (Nat.lt_succ_self 1) h₁
have h₃ : 0 < leftLen heap h₂ := heapReplaceRootPossibleRootValuesAuxL heap $ Nat.lt_trans (Nat.lt_succ_self 1) h₁
have h₄ : 0 < rightLen heap h₂ := heapReplaceRootPossibleRootValuesAuxR heap h₁
(heap.heapReplaceRoot le value h₂).snd.root h₂ = value
∨ (heap.heapReplaceRoot le value h₂).snd.root h₂ = (heap.left h₂).root h₃
∨ (heap.heapReplaceRoot le value h₂).snd.root h₂ = (heap.right h₂).root h₄
:=
  sorry

private theorem CompleteTree.heapReplaceRootIsHeapLeRootAux {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : HeapPredicate heap le) (h₂ : n > 0) (h₃ : le (root heap h₂) value) : HeapPredicate.leOrLeaf le (root heap h₂) (heapReplaceRoot le value heap h₂).snd :=
  if h₄ : n = 1 then by
    have h₅ : le (heap.root h₂) ( (heapReplaceRoot le value heap h₂).snd.root h₂) := by simp only[h₃, h₄, heapReplaceRootPossibleRootValues1]
    unfold HeapPredicate.leOrLeaf
    split <;> simp[h₅]
  else if h₅ : n = 2 then by
    have h₆ := heapReplaceRootPossibleRootValues2 le value heap h₅
    simp at h₆
    cases h₆
    case inl h₆ =>
      have h₇ : le (heap.root h₂) ( (heapReplaceRoot le value heap h₂).snd.root h₂) := by simp only [h₆, h₃]
      unfold HeapPredicate.leOrLeaf
      split <;> simp[h₇]
    case inr h₆ =>
      unfold HeapPredicate.leOrLeaf
      unfold HeapPredicate at h₁
      split at h₁
      case h_1 => contradiction
      case h_2 o p v l r h₇ h₈ h₉ =>
        have h₁₁ : p = 0 := by
         simp at h₅
         cases o; simp[h₅] at h₇; exact h₇; simp_arith[Nat.add_eq_zero ] at h₅; exact h₅.right
        have h₁₀ : o = 1 := by simp_arith[h₁₁] at h₅; assumption
        simp
        rw[h₆]
        have h₁₂ := h₁.right.right.left
        unfold HeapPredicate.leOrLeaf at h₁₂
        cases o ; contradiction;
        case succ =>
          exact h₁₂
  else by
    have h₆ : n > 2 := by omega
    have h₇ := heapReplaceRootPossibleRootValues3 le value heap h₆
    simp at h₇
    unfold HeapPredicate at h₁
    cases h₇
    case inl h₇ =>
      have h₈ : le (heap.root h₂) ( (heapReplaceRoot le value heap h₂).snd.root h₂) := by simp only [h₇, h₃]
      unfold HeapPredicate.leOrLeaf
      split <;> simp[h₈]
    case inr h₇ =>
      cases h₇
      case inl h₇ | inr h₇ =>
        unfold HeapPredicate.leOrLeaf
        split at h₁
        contradiction
        simp_all
        case h_2 o p v l r _ _ _ =>
          cases o
          omega
          cases p
          omega
          have h₈ := h₁.right.right.left
          have h₉ := h₁.right.right.right
          assumption

private theorem CompleteTree.heapReplaceRootIsHeapLeRootAuxLe {α : Type u} (le : α → α → Bool) {a b c : α} (h₁ : transitive_le le) (h₂ : total_le le) (h₃ : le b c) : ¬le a c ∨ ¬ le a b → le b a
| .inr h₅ => not_le_imp_le h₂ _ _ h₅
| .inl h₅ => h₁ b c a ⟨h₃,not_le_imp_le h₂ _ _ h₅⟩

theorem CompleteTree.heapReplaceRootIsHeap {α : Type u} {n: Nat} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) (h₂ : HeapPredicate heap le) (h₃ : transitive_le le) (h₄ : total_le le) : HeapPredicate (heap.heapReplaceRoot le value h₁).snd le := by
    unfold heapReplaceRoot
    split
    rename_i o p v l r h₇ h₈ h₉ heq
    exact
      if h₁₀ : o = 0 then by
        simp[*]
        unfold HeapPredicate at h₂ ⊢
        simp[h₂]
        unfold HeapPredicate.leOrLeaf
        have : p = 0 := by rw[h₁₀, Nat.le_zero_eq] at h₇; assumption
        apply And.intro
        case left => match o, l with
        | Nat.zero, _ => trivial
        case right => match p, r with
        | Nat.zero, _ => trivial
      else if h₁₁ : p = 0 then by
        simp[*]
        cases h₉ : le value (root l (_ : 0 < o)) <;> simp
        case true =>
          unfold HeapPredicate at *
          simp[h₂]
          unfold HeapPredicate.leOrLeaf
          apply And.intro
          case right => match p, r with
          | Nat.zero, _ => trivial
          case left => match o, l with
          | Nat.succ _, _ => assumption
        case false =>
          rw[heapReplaceRootReturnsRoot]
          have h₁₂ : le (l.root (Nat.zero_lt_of_ne_zero h₁₀)) value := by simp[h₉, h₄, not_le_imp_le]
          have h₁₃ : o = 1 := Nat.le_antisymm (by simp_arith[h₁₁] at h₈; exact h₈) (Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero h₁₀))
          unfold HeapPredicate at *
          simp[h₂] --closes one sub-goal
          apply And.intro <;> try apply And.intro
          case right.right => match p, r with
            | 0, .leaf => simp[HeapPredicate.leOrLeaf]
          case right.left =>
            simp[HeapPredicate.leOrLeaf, h₁₃]
            cases o <;> simp[heapReplaceRootPossibleRootValues1, *]
          case left =>
            apply heapReplaceRootIsHeap
            <;> simp[*]
      else if h₁₂ : le value (root l (Nat.zero_lt_of_ne_zero h₁₀)) ∧ le value (root r (Nat.zero_lt_of_ne_zero h₁₁)) then by
        unfold HeapPredicate at *
        simp[*]
        unfold HeapPredicate.leOrLeaf
        cases o
        . contradiction
        cases p
        . contradiction
        simp
        assumption
      else by
        simp[*]
        have h₁₃ : ¬le value (root l _) ∨ ¬le value (root r _) := (Decidable.not_and_iff_or_not (le value (root l (Nat.zero_lt_of_ne_zero h₁₀)) = true) (le value (root r (Nat.zero_lt_of_ne_zero h₁₁)) = true)).mp h₁₂
        cases h₁₄ : le (root l (_ : 0 < o)) (root r (_ : 0 < p))
        <;> simp
        <;> unfold HeapPredicate at *
        <;> simp[*]
        <;> apply And.intro
        <;> try apply And.intro
        case false.left | true.left =>
          apply heapReplaceRootIsHeap
          <;> simp[*]
        case false.right.left =>
          unfold HeapPredicate.leOrLeaf
          have h₁₅ : le (r.root _) (l.root _) = true := not_le_imp_le h₄ (l.root _) (r.root _) $ (Bool.not_eq_true $ le (root l (_ : 0 < o)) (root r (_ : 0 < p))).substr h₁₄
          simp[heapReplaceRootReturnsRoot]
          cases o <;> simp[h₁₅]
        case true.right.right =>
          unfold HeapPredicate.leOrLeaf
          simp[heapReplaceRootReturnsRoot]
          cases p <;> simp[h₁₄]
        case false.right.right =>
          simp[heapReplaceRootReturnsRoot]
          have h₁₅ : le (r.root _) (l.root _) = true := not_le_imp_le h₄ (l.root _) (r.root _) $ (Bool.not_eq_true $ le (root l (_ : 0 < o)) (root r (_ : 0 < p))).substr h₁₄
          have h₁₆ : le (r.root _) value := heapReplaceRootIsHeapLeRootAuxLe le h₃ h₄ h₁₅ h₁₃
          simp[heapReplaceRootIsHeapLeRootAux, *]
        case true.right.left =>
          simp[heapReplaceRootReturnsRoot]
          have h₁₆ : le (l.root _) value := heapReplaceRootIsHeapLeRootAuxLe le h₃ h₄ h₁₄ h₁₃.symm
          simp[heapReplaceRootIsHeapLeRootAux, *]

theorem CompleteTree.heapReplaceElementAtIsHeap {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) (h₂ : HeapPredicate heap le) (h₃ : transitive_le le) (h₄ : total_le le) : HeapPredicate (heap.heapReplaceElementAt le index value h₁).snd le := by
  unfold heapReplaceElementAt
  split
  case isTrue h₅ =>
    exact heapReplaceRootIsHeap le value heap h₁ h₂ h₃ h₄
  case isFalse h₅ => sorry

/--Removes the element at a given index. Use `CompleteTree.indexOf` to find the respective index.-/
def CompleteTree.heapRemoveAt {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin (n+1)) (heap : CompleteTree α (n+1)) : α × CompleteTree α n :=
  --Since we cannot even temporarily break the completeness property, we go with the
  --version from Wikipedia: We first remove the last element, and then update values in the tree
  let l := heap.popLast
  if p : index = n then
    l
  else
    have n_gt_zero : n > 0 := by
      cases n
      case succ nn => exact Nat.zero_lt_of_ne_zero $ Nat.succ_ne_zero nn
      case zero => exact absurd ((Nat.le_zero_eq index.val).mp (Nat.le_of_lt_succ ((Nat.zero_add 1).subst index.isLt))) p
    let index : Fin n := ⟨index, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ index.isLt) p⟩
    heapReplaceElementAt le index l.fst l.snd n_gt_zero

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
#eval TestHeap.indexOf (71 = ·)
