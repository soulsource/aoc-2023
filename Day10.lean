import «Common»
import «BinaryHeap»

namespace Day10

structure Coordinate (width : Nat) (height : Nat) where
  x : Fin width
  y : Fin height
deriving DecidableEq

def Coordinate.toIndex {w h : Nat} (c : Coordinate w h) : Fin (w*h) :=
  Fin.mk (c.x.val + w * c.y.val) (
    Nat.le_pred_of_lt c.y.isLt
      |> Nat.mul_le_mul_left w
      |> Nat.add_le_add_iff_right.mpr
      |> (Nat.mul_pred w h).subst (motive :=λx↦w * c.y.val + w ≤ x + w)
      |> (Nat.sub_add_cancel (Nat.le_mul_of_pos_right w (Nat.zero_lt_of_lt c.y.isLt))).subst
      |> (Nat.add_comm _ _).subst (motive := λx↦x ≤ w*h)
      |> Nat.le_sub_of_add_le
      |> Nat.lt_of_lt_of_le c.x.isLt
      |> λx↦(Nat.add_lt_add_right) x (w * c.y.val)
      |> (Nat.sub_add_cancel (Nat.le_of_lt ((Nat.mul_lt_mul_left (Nat.zero_lt_of_lt c.x.isLt)).mpr c.y.isLt))).subst
  )

def Coordinate.fromIndex {w h : Nat} (index : Fin (w*h)) : Coordinate w h :=
  have : w > 0 :=
    have := index.isLt
    match w with
    | Nat.zero => absurd ((Nat.zero_mul h).subst this) (Nat.not_lt_zero index.val)
    | Nat.succ ww => Nat.succ_pos ww
  {
    x := ⟨index.val % w, Nat.mod_lt index.val this⟩
    y := ⟨index.val / w, Nat.div_lt_of_lt_mul index.isLt⟩
  }

def Coordinate.goEast (c : Coordinate w h) : Option (Coordinate w h) :=
  if h : c.x.succ.val < w then
    some { c with x:= Fin.castLT c.x.succ h}
  else
    none

def Coordinate.goSouth (c : Coordinate w h) : Option (Coordinate w h) :=
  if h : c.y.succ.val < h then
    some { c with y := Fin.castLT c.y.succ h}
  else
    none

def Coordinate.goWest (c : Coordinate w h) : Option (Coordinate w h) :=
  if h : ⟨0,Nat.zero_lt_of_lt c.x.isLt⟩ < c.x then
    have : Fin.castLT c.x (Nat.lt_trans c.x.isLt (Nat.lt_succ_self _)) ≠ 0 := by
      simp only [←Fin.val_ne_iff, Nat.succ_eq_add_one, Fin.coe_castLT, Fin.val_zero]
      exact (Nat.ne_of_lt h).symm
    some { c with x := (Fin.castLT c.x (Nat.lt_trans c.x.isLt (Nat.lt_succ_self _))).pred this}
  else
    none

def Coordinate.goNorth (c : Coordinate w h) : Option (Coordinate w h) :=
  if h : ⟨0,Nat.zero_lt_of_lt c.y.isLt⟩ < c.y then
    have : Fin.castLT c.y (Nat.lt_trans c.y.isLt (Nat.lt_succ_self _)) ≠ 0 := by
      simp only [←Fin.val_ne_iff, Nat.succ_eq_add_one, Fin.coe_castLT, Fin.val_zero]
      exact (Nat.ne_of_lt h).symm
    some { c with y := (Fin.castLT c.y (Nat.lt_trans c.y.isLt (Nat.lt_succ_self _))).pred this}
  else
    none

theorem Coordinate.toIndex_inv_fromIndex {w h : Nat} (index : Fin (w*h)) : Coordinate.toIndex (Coordinate.fromIndex index) = index := by
  simp only [toIndex, fromIndex, Nat.mod_add_div, Fin.eta]

inductive Pipe
| NS : Pipe
| WE : Pipe
| NE : Pipe
| ES : Pipe
| SW : Pipe
| WN : Pipe
deriving BEq

instance : LawfulBEq Pipe where
  eq_of_beq := by
    intros a b
    cases a <;> cases b
    <;> simp
    all_goals rfl
  rfl := by
    intro a
    cases a
    all_goals rfl


inductive Tile
| pipe : Pipe → Tile
| ground : Tile
| start : Tile
deriving BEq

instance : LawfulBEq Tile where
  eq_of_beq := by
    intros a b
    cases a <;> cases b
    <;> simp
    all_goals try rfl
    case pipe.pipe =>
      intros h
      exact eq_of_beq h
  rfl := by
    intro a
    cases a
    all_goals try rfl
    case pipe =>
      rename_i p
      cases p
      <;> rfl

instance : Inhabited Tile where
  default := Tile.ground

-- The invariants are maybe overdoing it a bit, but (in the voice of king Leonidas) "This is Lean4!"
structure Area where
  width : Nat
  height : Nat
  start : Coordinate width height
  fields : Array Tile
  size_invariant : fields.size = width * height
  start_invariant : fields[start.toIndex] = Tile.start
  -- It would also be possible to prove the inverse - that having an index that gives Tile.start
  -- implies that this index is equal to start.toIndex, but that is not needed in the solution
  -- I have a half-finished proof on a local branch.

instance : ToString Area where
  toString := λ
  | {width, height, start, fields, ..} => Id.run do
    let mut s := s!"Width: {width}, Height: {height}, Start x: {start.x}, Start y: {start.y}"
    let mut p := 0
    for t in fields do
      if p % width = 0 then
        s := s.push '\n'
      s := s.push $ toChar t
      p := p + 1
    s
  where toChar := λ
  | Tile.ground => ' '
  | Tile.start => 'X'
  | Tile.pipe .NE => '└'
  | Tile.pipe .ES => '┌'
  | Tile.pipe .SW => '┐'
  | Tile.pipe .WN => '┘'
  | Tile.pipe .NS => '│'
  | Tile.pipe .WE => '─'

inductive Area.ParseError
| NoInput
| UnexpectedCharacter : Char → Area.ParseError
| NoStart
| MoreThanOneStart
| NotRectangular

instance : ToString Area.ParseError where
  toString := λ
  | .NoInput => "Parse Error: No input supplied."
  | .UnexpectedCharacter c => s!"Parse Error: Unexpected character in input. Expected '|', '-', 'L', 'J', '7', 'F', or '.', but got {c}."
  | .NoStart => "Parse Error: The input did not contain a Start field ('s')."
  | .MoreThanOneStart => "Parse Error: Multiple Start values supplied."
  | .NotRectangular => "Parse Error: Input was not rectangular (line lengths did not match)."

private structure Area.Raw where
  width : Nat
  height : Nat
  start : Option $ Fin (width * height)
  fields : Array Tile


private def Area.parseLine (previous : Area.Raw) (pos : Nat) (line : Substring) (hh : previous.height > 0) : Except Area.ParseError (Nat × Area.Raw) :=
  if h : line.isEmpty then
    Except.ok (pos, previous)
  else if h₀ : pos ≥ previous.width then
    throw Area.ParseError.NotRectangular
  else do
    let tile ← Except.mapError Area.ParseError.UnexpectedCharacter $ parseCharacter line.front
    let rest := line.drop 1
    if tile == Tile.start then
      if previous.start.isSome then
        throw Area.ParseError.MoreThanOneStart
      else
        have : previous.width * (previous.height - 1) + pos < previous.width * previous.height := by
          have := Nat.mul_pred previous.width previous.height
          simp only [Nat.pred_eq_sub_one] at this
          rw[this]
          have : previous.width ≤ previous.width*previous.height := Nat.le_mul_of_pos_right _ hh
          rw[←Nat.sub_add_comm this]
          omega
        let start := ⟨previous.width * (previous.height - 1) + pos, this⟩
        Area.parseLine {previous with fields := previous.fields.push tile, start := some start} (pos + 1) rest hh
    else
      Area.parseLine {previous with fields := previous.fields.push tile} (pos + 1) rest hh
termination_by previous.width - pos
where parseCharacter : Char → Except Char Tile := λ c ↦ match c with
  | '|' => Except.ok $ Tile.pipe Pipe.NS
  | '-' => Except.ok $ Tile.pipe Pipe.WE
  | 'L' => Except.ok $ Tile.pipe Pipe.NE
  | 'J' => Except.ok $ Tile.pipe Pipe.WN
  | '7' => Except.ok $ Tile.pipe Pipe.SW
  | 'F' => Except.ok $ Tile.pipe Pipe.ES
  | 'S' => Except.ok Tile.start
  | '.' => Except.ok Tile.ground
  | c => Except.error c

private theorem Nat.mul_le_succ_right : ∀ (n m : Nat), n*m ≤ n*m.succ := by
  intro n m
  rw[Nat.mul_succ]
  omega

private def Area.parseLines (previous : Area.Raw) (input : List String) : Except Area.ParseError Area.Raw :=
  match input with
  | [] => pure previous
  | l :: ls => do
    let current := {
      previous with
      height := previous.height + 1
      start := Fin.castLE (Nat.mul_le_succ_right _ _) <$> previous.start
    }
    let (parsed_width, parsed_line) ← Area.parseLine current 0 l.toSubstring (by simp only [gt_iff_lt, Nat.zero_lt_succ])
    if parsed_width = previous.width then
      Area.parseLines parsed_line ls
    else
      throw Area.ParseError.NotRectangular

private def Area.parseRaw (input : String) : Except Area.ParseError Area.Raw :=
  let lines := input.trim.splitTrim (· == '\n')
  if h₁ : lines.isEmpty then
    throw Area.ParseError.NoInput
  else
    have : 0 < lines.length := by
      cases hl : lines
      case nil => exact absurd (List.isEmpty_nil) (hl.subst (motive := λx↦¬x.isEmpty = true) h₁)
      case cons => exact Nat.succ_pos _
    let width := lines[0].length
    if width > 0 then
      let initial : Area.Raw := {
        width,
        height := 0,
        start := none,
        fields := Array.empty
      }
      Area.parseLines initial lines
    else
      throw Area.ParseError.NoInput

private def Except.get (e : Except ε α) (_ : e.isOk) : α :=
  match e with
  | .ok a => a

private theorem Area.ParseLine_adds_returned_count (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) : (h : (Area.parseLine previous pos line h₁).isOk) → (Except.get (Area.parseLine previous pos line h₁) h).2.fields.size = previous.fields.size + (Except.get (Area.parseLine previous pos line h₁) h).1 - pos := by
  intros h₂
  generalize h₃ : Day10.Area.parseLine previous pos line h₁ = r at *
  unfold parseLine at h₃
  simp at h₃
  split at h₃
  case isTrue =>
    subst r
    unfold Except.get
    simp
  case isFalse =>
    split at h₃
    case isTrue => rw[←h₃] at h₂; contradiction
    case isFalse =>
      unfold bind Monad.toBind Except.instMonad at h₃
      simp at h₃
      cases h₄ : (Day10.Area.parseLine.parseCharacter line.front)
      <;> simp[h₄, Option.toExcept, Except.bind] at h₃
      case error => rw[←h₃] at h₂; contradiction
      case ok =>
        split at h₃
        case h_1 => rw[←h₃] at h₂; contradiction
        case h_2 d1 h₅ char₂ d2 char h₆ =>
        simp[Except.mapError] at h₆
        subst char₂
        clear d1 d2
        split at h₃
        case' isTrue =>
          split at h₃
          case isTrue.isTrue => rw[←h₃] at h₂; contradiction
          have : previous.width * (previous.height - 1) + pos < previous.width * previous.height := by
            have := Nat.mul_pred previous.width previous.height
            simp only [Nat.pred_eq_sub_one] at this
            rw[this]
            have : previous.width ≤ previous.width*previous.height := Nat.le_mul_of_pos_right _ h₁
            rw[←Nat.sub_add_comm this]
            omega
          generalize hc :{ width := previous.width, height := previous.height, start := some ⟨previous.width * (previous.height - 1) + pos, this⟩, fields := previous.fields.push char : Area.Raw} = c
        case' isFalse =>
          generalize hc :{ width := previous.width, height := previous.height, start := previous.start, fields := previous.fields.push char : Area.Raw} = c
        case isTrue | isFalse =>
          simp[hc] at h₃
          have : c.height = previous.height := by rw[←hc]
          have h₆ := Area.ParseLine_adds_returned_count c (pos+1) (line.drop 1) (this▸h₁) (by simp_all)
          simp[h₃] at h₆
          have h₇ : c.fields.size = previous.fields.size + 1 := by
            rw[←hc]
            simp
          rw[h₇] at h₆
          omega
termination_by previous.width - pos

private theorem Area.ParseLine_leaves_width_and_height (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) : (h : (Area.parseLine previous pos line h₁).isOk) → (Except.get (Area.parseLine previous pos line h₁) h).2.width = previous.width ∧ (Except.get (Area.parseLine previous pos line h₁) h).2.height = previous.height := by
  intros h₂
  generalize h₃ : Day10.Area.parseLine previous pos line h₁ = r at *
  unfold parseLine at h₃
  simp at h₃
  split at h₃
  case isTrue =>
    subst r
    unfold Except.get
    simp
  case isFalse =>
    split at h₃
    case isTrue => rw[←h₃] at h₂; contradiction
    case isFalse =>
      unfold bind Monad.toBind Except.instMonad at h₃
      simp at h₃
      cases h₄ : (Day10.Area.parseLine.parseCharacter line.front)
      <;> simp[h₄, Option.toExcept, Except.bind] at h₃
      case error => rw[←h₃] at h₂; contradiction
      case ok =>
        split at h₃
        case h_1 => rw[←h₃] at h₂; contradiction
        case h_2 d1 h₅ char₂ d2 char h₆ =>
        simp[Except.mapError] at h₆
        subst char₂
        clear d1 d2
        split at h₃
        case' isTrue =>
          split at h₃
          case isTrue.isTrue => rw[←h₃] at h₂; contradiction
          have : previous.width * (previous.height - 1) + pos < previous.width * previous.height := by
            have := Nat.mul_pred previous.width previous.height
            simp only [Nat.pred_eq_sub_one] at this
            rw[this]
            have : previous.width ≤ previous.width*previous.height := Nat.le_mul_of_pos_right _ h₁
            rw[←Nat.sub_add_comm this]
            omega
          generalize hc :{ width := previous.width, height := previous.height, start := some ⟨previous.width * (previous.height - 1) + pos, this⟩, fields := previous.fields.push char : Area.Raw} = c
        case' isFalse =>
          generalize hc :{ width := previous.width, height := previous.height, start := previous.start, fields := previous.fields.push char : Area.Raw} = c
        case isTrue | isFalse =>
          simp[hc] at h₃
          have h₇ : c.height = previous.height := by rw[←hc]
          have h₆ := Area.ParseLine_leaves_width_and_height c (pos+1) (line.drop 1) (h₇▸h₁) (by simp_all)
          simp[h₃] at h₆
          have h₈ : c.width = previous.width := by rw[←hc]
          omega
termination_by previous.width - pos

private theorem Area.ParseLines_array_size (input : Area.Raw) (lines : List String) (h₁ : input.fields.size = input.width * input.height) : (h : (Area.parseLines input lines).isOk) → (Except.get (Area.parseLines input lines) h).fields.size = (Except.get (Area.parseLines input lines) h).width * (Except.get (Area.parseLines input lines) h).height := by
  intro h₂
  generalize h₃ : Day10.Area.parseLines input lines = r at *
  unfold Area.parseLines at h₃
  cases lines <;> simp at h₃
  case nil =>
    simp[←h₃]
    exact h₁
  case cons l ls =>
    unfold bind Monad.toBind Except.instMonad at h₃
    simp at h₃
    unfold Except.bind at h₃
    split at h₃
    case h_1 => rw[←h₃] at h₂; contradiction
    case h_2 d lineResult h₄ =>
      clear d
      simp at h₃
      split at h₃
      case isFalse => rw[←h₃] at h₂; contradiction
      case isTrue h₅ =>
        simp[←h₃]
        apply Area.ParseLines_array_size
        have : (Area.parseLine { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _)).isOk := by
          cases hx : (Area.parseLine { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _))
          case error => rw[hx] at h₄; contradiction
          case ok => rfl
        have h₆ : lineResult.snd.width = input.width := by
          have := Area.ParseLine_leaves_width_and_height { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _) this
          simp[Except.get] at this
          split at this
          rename_i lineResult₂ _ h₄₂ _
          simp[h₄] at h₄₂
          subst lineResult₂
          exact this.left
        have h₇ : lineResult.snd.height = input.height + 1 := by
          have := Area.ParseLine_leaves_width_and_height { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _) this
          simp[Except.get] at this
          split at this
          rename_i lineResult₂ _ h₄₂ _
          simp[h₄] at h₄₂
          subst lineResult₂
          exact this.right
        have h₈ : lineResult.snd.fields.size = input.fields.size + lineResult.fst := by
          have := Area.ParseLine_adds_returned_count { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _) this
          simp[Except.get] at this
          split at this
          rename_i lineResult₂ _ h₄₂ _
          simp[h₄] at h₄₂
          subst lineResult₂
          assumption
        rw[h₈, h₇, h₆, h₁, h₅]
        exact Nat.mul_succ _ _


private theorem Area.ParseRaw_array_size :
  ∀ (input : String), (h : (Area.parseRaw input).isOk) → (Except.get (Area.parseRaw input) h).fields.size = (Except.get (Area.parseRaw input) h).width * (Except.get (Area.parseRaw input) h).height := by
  intros input h₁
  generalize h₂ : Day10.Area.parseRaw input = r at *
  unfold Area.parseRaw at h₂
  simp at h₂
  split at h₂
  case isTrue => rw[←h₂] at h₁; contradiction
  split at h₂
  case isFalse.isFalse => rw[←h₂] at h₁; contradiction
  case isFalse.isTrue =>
    simp[←h₂]
    apply Area.ParseLines_array_size
    rfl

private theorem Except.isOk_exists {e : Except ε α} : (e.isOk = true) ↔ ∃a, e = Except.ok a := by
  constructor
  <;> intro h₁
  case mp =>
    match e with
    | .ok v => exists v
  case mpr =>
    cases h₁
    subst e
    rfl

private theorem Except.get_unfold {α : Type u1} {ε : Type u2} (v : α) : Except.get (α := α) (ε := ε) (Except.ok v) (rfl) = v := rfl

private theorem Except.get_unfold' {α : Type u1} {ε : Type u2} {e : Except ε α} {v : α} (h₁ : e = Except.ok v) (h₂ : e.isOk) : Except.get e h₂ = v := by
  simp[h₁]
  apply Except.get_unfold

private theorem Except.get_pure {α : Type u1} (ε : Type u2) (v : α) : Except.get (α := α) (ε := ε) (pure v) (rfl) = v := rfl

private theorem Array.getElem!_eq_getElem {α : Type u} [Inhabited α] {a : Array α} {index : Nat} (h : index < a.size ): a[index] = a[index]! := by
  unfold getElem getElem! instGetElem?OfGetElemOfDecidable Array.instGetElemNatLtSize decidableGetElem?
  simp
  split
  <;> rename_i blah
  <;> simp[h] at blah
  assumption

private theorem Array.get_push {α : Type u} (arr : Array α) (v : α) (index : Nat) (h₁ : index < arr.size) : arr[index] = (arr.push v)[index]'(by simp[Nat.lt_succ.mpr (Nat.le_of_lt h₁)]) := by
  cases arr
  unfold Array.push getElem Array.instGetElemNatLtSize Array.get
  simp[List.getElem_append, h₁]

private theorem Area.ParseLine_leaves_start_if_some (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) {res : (Nat × Area.Raw)} (h₂ : (Area.parseLine previous pos line h₁) = Except.ok res) (h₃ : previous.start.isSome) : Fin.val <$> res.2.start = Fin.val <$> previous.start := by
  unfold Area.parseLine at h₂
  split at h₂
  case isTrue => simp at h₂; rw[←h₂]
  case isFalse h₄ =>
    split at h₂ ; contradiction
    case isFalse h₅ =>
      unfold bind Monad.toBind Except.instMonad Except.bind at h₂
      simp at h₂
      split at h₂; simp at h₂
      case h_2 d1 tile _ =>
        clear d1
        split at h₂; contradiction
        exact Area.ParseLine_leaves_start_if_some  { width := previous.width, height := previous.height, start := previous.start, fields := previous.fields.push tile } (pos + 1) (line.drop 1) h₁ h₂ h₃
termination_by previous.width - pos

private theorem Area.ParseLine_only_adds_to_fields (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) {res : (Nat × Area.Raw)} (h₂ : (Area.parseLine previous pos line h₁) = Except.ok res) (index : Fin (previous.fields.size)) : previous.fields[index.val]! = res.2.fields[index.val]! := by
  unfold Area.parseLine at h₂
  split at h₂
  case isTrue => simp at h₂; rw[←h₂]
  case isFalse h₃ =>
    split at h₂; contradiction
    case isFalse h₄ =>
      unfold bind Monad.toBind Except.instMonad Except.bind at h₂
      simp at h₂
      split at h₂; simp at h₂
      case h_2 d1 tile _ =>
        clear d1
        split at h₂
        case' isFalse =>
          have h₅ := Area.ParseLine_only_adds_to_fields { width := previous.width, height := previous.height, start := previous.start, fields := previous.fields.push tile } (pos + 1) (line.drop 1) h₁ h₂ (Fin.castLE (by simp) index)
        case' isTrue =>
          split at h₂; contradiction
          have h₅ := Area.ParseLine_only_adds_to_fields { width := previous.width, height := previous.height, start := some ⟨previous.width * (previous.height - 1) + pos, _⟩, fields := previous.fields.push tile } (pos + 1) (line.drop 1) h₁ h₂ (Fin.castLE (by simp) index)
        all_goals
          simp at h₅
          rw[←h₅]
          have h₆ : ↑index < (previous.fields.push tile).size := by simp; exact Nat.lt_succ.mpr (Nat.le_of_lt index.isLt)
          simp[←Array.getElem!_eq_getElem]
          simp[←Array.getElem!_eq_getElem h₆]
          apply Array.get_push
termination_by previous.width - pos

private theorem Area.ParseLine_start_at_tile (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) (h₂ : previous.fields.size = previous.width * (previous.height - 1) + pos) (h₃ : previous.start = none) {res : Area.Raw} {added : Nat} (h₄ : (Area.parseLine previous pos line h₁) = Except.ok (added, res)) : match res.start with | none => True | some s => res.fields[s]! = Tile.start := by
  split; trivial
  case h_2 d1 index hindex =>
    clear d1
    unfold Area.parseLine at h₄
    simp at h₄
    split at h₄
    case isTrue => simp at h₄; rw[h₄.right] at h₃; rw[hindex] at h₃; contradiction
    case isFalse d2 =>
      clear d2
      split at h₄
      case isTrue => contradiction
      case isFalse h₅ =>
        unfold bind Monad.toBind Except.instMonad Except.bind at h₄
        simp at h₄
        split at h₄; contradiction
        case h_2 d3 t ht =>
          clear d3
          split at h₄
          case isTrue h₆ =>
            split at h₄; contradiction
            case isFalse h₇ =>
              have h₈ : (previous.fields.push t)[previous.width * (previous.height - 1) + pos]! = t := by
                have := Array.get_push_eq previous.fields t
                simp[h₂, Array.getElem!_eq_getElem] at this
                assumption
              have : t = Tile.start := beq_iff_eq.mp h₆
              subst t
              have : previous.width * (previous.height - 1) + pos < previous.width * previous.height := by
                have := Nat.mul_pred previous.width previous.height
                simp only [Nat.pred_eq_sub_one] at this
                rw[this]
                have : previous.width ≤ previous.width*previous.height := Nat.le_mul_of_pos_right _ h₁
                rw[←Nat.sub_add_comm this]
                omega
              have h₉ := Area.ParseLine_only_adds_to_fields { width := previous.width, height := previous.height, start := some ⟨previous.width * (previous.height - 1) + pos, this⟩, fields := previous.fields.push Tile.start } (pos + 1) (line.drop 1) h₁ h₄ ⟨previous.width * (previous.height - 1) + pos, (by simp_all)⟩
              simp at h₉
              have h₁₀ := Area.ParseLine_leaves_start_if_some { width := previous.width, height := previous.height, start := some ⟨previous.width * (previous.height - 1) + pos, this⟩, fields := previous.fields.push Tile.start } (pos + 1) (line.drop 1) h₁ h₄ rfl
              simp[hindex] at h₁₀
              simp[←h₁₀] at h₉ h₈
              simp[←h₉]
              assumption
          case isFalse =>
            have : (previous.fields.push t).size = previous.width * (previous.height - 1) + (pos + 1) := by simp_arith[h₂]
            have h₆ := Area.ParseLine_start_at_tile { width := previous.width, height := previous.height, start := previous.start, fields := previous.fields.push t } (pos + 1) (line.drop 1) h₁ this h₃ h₄
            simp[hindex] at h₆
            assumption
termination_by previous.width - pos

private theorem Area.ParseLines_start_position (input : Area.Raw) (lines : List String) (h₁ : (Area.parseLines input lines).isOk) (h₀ : input.fields.size = input.width * input.height) (h₂ : match input.start with | .some i => input.fields[i]! = Tile.start | .none => True) :
  match (Except.get (Area.parseLines input lines) h₁).start with
  | .some index => (Except.get (Area.parseLines input lines) h₁).fields[index]! = Tile.start
  | .none => True
  := by
  split
  case h_2 => trivial
  case h_1 d1 index hi =>
    clear d1
    generalize hr : Area.parseLines input lines = r at *
    unfold Area.parseLines at hr
    split at hr
    case h_1 =>
      subst r
      simp[Except.get_pure] at hi ⊢
      rw[hi] at h₂
      exact h₂
    case h_2 d1 l ls =>
      clear d1
      simp[bind, Except.bind] at hr
      split at hr
      case h_1 => rw[←hr] at h₁; contradiction
      case h_2 d1 o h₃ =>
        clear d1
        split at hr
        case isFalse => rw[←hr] at h₁; contradiction
        case isTrue h₄ =>
          subst r
          have : o.snd.fields.size = o.snd.width * o.snd.height := by
            have g₁ := Area.ParseLine_adds_returned_count { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _) (Except.isOk_exists.mpr ⟨o, h₃⟩)
            have g₂ := Area.ParseLine_leaves_width_and_height { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _) (Except.isOk_exists.mpr ⟨o, h₃⟩)
            rw[Except.get_unfold' h₃] at g₁ g₂
            rw[g₁, g₂.left, g₂.right, h₄, h₀]
            simp[Nat.mul_succ]
          have h₅ := Area.ParseLines_start_position o.snd ls h₁ this
          cases ho : o.snd.start
          case none =>
            simp[ho, hi] at h₅
            assumption
          case some lo =>
            simp[ho, hi] at h₅
            have : o.snd.fields[lo]! = Tile.start := by
              cases his : input.start
              case some is =>
                have := Area.ParseLine_leaves_start_if_some { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _) h₃ (by simp[his])
                simp[his] at this
                cases this
                case intro lo₂ hlo₂ =>
                  simp[hlo₂.left] at ho
                  subst lo₂
                  have : input.width * input.height ≤ input.fields.size := Nat.le_of_eq h₀.symm
                  have := Area.ParseLine_only_adds_to_fields { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _) h₃ (Fin.castLE this is)
                  simp at this ⊢
                  rw[←hlo₂.right] at this
                  rw[←this]
                  simp[his] at h₂
                  rw[hlo₂.right]
                  exact h₂
              case none =>
                have h₆ := Area.ParseLine_start_at_tile { width := input.width, height := input.height + 1, start := Option.map (Fin.castLE (Nat.mul_le_succ_right _ _)) input.start, fields := input.fields } 0 l.toSubstring (Nat.succ_pos _) h₀ (by simp[his]) h₃
                simp[ho] at h₆
                assumption
            rw[←h₅ this]
            rfl


private theorem Area.ParseRaw_start_position_aux :
  ∀ (input : String), (h₁ : (Area.parseRaw input).isOk) →
  match (Except.get (Area.parseRaw input) h₁).start with
  | .some index => (Except.get (Area.parseRaw input) h₁).fields[index]! = Tile.start
  | .none => True
  := by
  intros input h₁
  split
  case h_2 => trivial
  case h_1  maybeIndex index hi=>
    clear maybeIndex
    generalize hr: Day10.Area.parseRaw input = r at *
    unfold Area.parseRaw at hr
    simp at hr
    split at hr
    case isTrue => rw[←hr] at h₁; contradiction
    case isFalse =>
      split at hr
      case isFalse => rw[←hr] at h₁; contradiction
      case isTrue =>
        rename_i hs _
        have : 0 < (String.splitTrim (fun x => x == '\n') input.trim).length := by let hs := List.isEmpty_eq_false.mpr hs; unfold List.isEmpty at hs; split at hs; contradiction; rename_i hx; simp[hx]
        have := Area.ParseLines_start_position { width := (String.splitTrim (fun x => x == '\n') input.trim)[0].length, height := 0, start := none, fields := #[] } (String.splitTrim (fun x => x == '\n') input.trim) (hr.substr h₁)
        simp at this
        subst r
        split at this
        case h_2 hix => exact absurd (Option.isSome_iff_exists.mpr ⟨index,hi⟩) (Option.not_isSome_iff_eq_none.mpr hix)
        case h_1 index₂ hi₂=>
          have := hi.subst (motive :=λx↦x = some index₂) hi₂
          simp at this
          subst index₂
          exact this

private theorem Area.ParseRaw_start_position :
  ∀ (input : String), (h₁ : (Area.parseRaw input).isOk) → (h₂ : (Except.get (Area.parseRaw input) h₁).start.isSome) → (Except.get (Area.parseRaw input) h₁).fields[(Except.get (Area.parseRaw input) h₁).start.get h₂]'((Area.ParseRaw_array_size input h₁).substr ((Except.get (Area.parseRaw input) h₁).start.get h₂).isLt) = Tile.start := by
  intros input h₁ h₂
  have := Area.ParseRaw_start_position_aux input h₁
  split at this
  case h_2 hx => exact absurd h₂ (Option.not_isSome_iff_eq_none.mpr hx)
  case h_1 maybeIndex index he =>
    simp at this
    simp_all
    rw[←this]
    apply Array.getElem!_eq_getElem

-- Finally.
private def Area.parse (input : String) : Except Area.ParseError Area :=
  let raw := Area.parseRaw input
  match he : raw with
  | Except.error e => throw e
  | Except.ok vraw =>
    match hs : vraw.start with
    | .none => throw Area.ParseError.NoStart
    | .some s =>
      have except_ok := (Except.isOk_exists.mpr ⟨vraw, he⟩)
      have hw : (Day10.Except.get (Day10.Area.parseRaw input) except_ok).width = vraw.width := by have : raw = Day10.Area.parseRaw input := rfl; simp[←this]; rw[Except.get_unfold' he]
      have hh : (Day10.Except.get (Day10.Area.parseRaw input) except_ok).height = vraw.height := by have : raw = Day10.Area.parseRaw input := rfl; simp[←this]; rw[Except.get_unfold' he]
      have finc : vraw.width * vraw.height = (Day10.Except.get (Day10.Area.parseRaw input) except_ok).width * (Day10.Except.get (Day10.Area.parseRaw input) except_ok).height := by rw[hh,hw]
      have is_some : (Day10.Except.get (Day10.Area.parseRaw input) except_ok).start.isSome := by
        have : raw = Day10.Area.parseRaw input := rfl
        unfold Except.get
        split
        simp_all
        rename_i d _ _ _ _
        subst d
        simp[hs]
      have as := Area.ParseRaw_array_size input (Except.isOk_exists.mpr ⟨vraw, he⟩)
      have as : vraw.fields.size = vraw.width * vraw.height := (Except.get_unfold' he except_ok).subst (motive := λx↦ x.fields.size = x.width * x.height) as
      have sp := ParseRaw_start_position input (Except.isOk_exists.mpr ⟨vraw, he⟩) is_some
      have sp : vraw.fields[(Coordinate.fromIndex s).toIndex] = Tile.start := by
        simp[Except.get_unfold' he except_ok] at sp
        simp[Coordinate.toIndex_inv_fromIndex]
        rw[Array.getElem!_eq_getElem] at sp ⊢
        have : ((Day10.Except.get (Day10.Area.parseRaw input) _).start.get is_some).val = s.val := by
          unfold Option.get
          split
          rename_i s₂ _ h₁ _
          have : (Day10.Except.get (Day10.Area.parseRaw input) except_ok) = vraw := by
            rw[Except.get_unfold']
            exact he
          subst this
          simp[hs] at h₁
          exact Fin.ext_iff.mp h₁.symm
        rw[this] at sp
        exact sp

      Except.ok {
        width := vraw.width --: Nat
        height := vraw.height --: Nat
        start := Coordinate.fromIndex s -- Coordinate width height
        fields := vraw.fields--: Array Tile
        size_invariant := as --: fields.size = width * height
        start_invariant := sp --: fields[start.toIndex] = Tile.start
      }

------------------------------------------------------------------------------------------------------------

def Area.getTile (area : Area) (c : Coordinate area.width area.height) : Tile :=
  area.fields[c.toIndex]'(area.size_invariant.substr c.toIndex.is_lt)

instance {w h : Nat} : GetElem Area (Coordinate w h) Tile (λ c _ ↦ c.width = w ∧ c.height = h) where
  getElem := λa c h₁ ↦ a.getTile (h₁.left▸h₁.right▸c)

-- North is negative y, South positive y
-- West is negative x, East positive x
private def Area.can_connect_to.is_succ := λ {n : Nat} (a b : Fin n) ↦ if h: a.succ.val < n then b = Fin.castLT a.succ h else False
private def Area.is_west_of (area : Area) (current other : Coordinate area.width area.height) : Prop := (can_connect_to.is_succ current.x other.x ∧ current.y = other.y)
private def Area.is_north_of (area : Area) (current other : Coordinate area.width area.height) : Prop := (can_connect_to.is_succ current.y other.y ∧ current.x = other.x)
private def Area.is_east_of (area : Area) (current other : Coordinate area.width area.height) : Prop := area.is_west_of other current
private def Area.is_south_of (area : Area) (current other : Coordinate area.width area.height) : Prop := area.is_north_of other current

private theorem Area.can_connect_to.is_succ.irrefl {n : Nat} {a b : Fin n} : Area.can_connect_to.is_succ a b → Area.can_connect_to.is_succ b a → False := by
  intros h₁ h₂
  unfold Area.can_connect_to.is_succ at *
  split at h₁
  split at h₂
  case isTrue.isFalse | isFalse => assumption
  case isTrue.isTrue => simp[Fin.ext_iff] at h₂ h₁; omega

instance {n : Nat} {a b : Fin n} : Decidable (Area.can_connect_to.is_succ a b) :=
  if h : a.succ.val < n then
    have : (Area.can_connect_to.is_succ a b) = (b = Fin.castLT a.succ h) := (dite_cond_eq_true (eq_true h)).subst rfl
    if h₂ : b = Fin.castLT a.succ h then
      Decidable.isTrue (this▸h₂)
    else
      Decidable.isFalse (this▸h₂)
  else
    have : Area.can_connect_to.is_succ a b = False := (dite_cond_eq_false (eq_false h)).subst (rfl)
    this▸(inferInstance : Decidable False)

instance {area : Area} {current other : Coordinate area.width area.height} : Decidable (Area.is_west_of area current other) := (inferInstance : Decidable (And _ _))
instance {area : Area} {current other : Coordinate area.width area.height} : Decidable (Area.is_east_of area current other) := (inferInstance : Decidable (And _ _))
instance {area : Area} {current other : Coordinate area.width area.height} : Decidable (Area.is_north_of area current other) := (inferInstance : Decidable (And _ _))
instance {area : Area} {current other : Coordinate area.width area.height} : Decidable (Area.is_south_of area current other) := (inferInstance : Decidable (And _ _))

private inductive Area.can_connect_to (area : Area) (current other : Coordinate area.width area.height) : Prop where
  | NE : area[current] = Tile.pipe .NE → area.is_north_of other current ∨ area.is_east_of other current → Area.can_connect_to area current other
  | ES : area[current] = Tile.pipe .ES → area.is_south_of other current ∨ area.is_east_of other current → Area.can_connect_to area current other
  | SW : area[current] = Tile.pipe .SW → area.is_south_of other current ∨ area.is_west_of other current → Area.can_connect_to area current other
  | WN : area[current] = Tile.pipe .WN → area.is_north_of other current ∨ area.is_west_of other current → Area.can_connect_to area current other
  | WE : area[current] = Tile.pipe .WE → area.is_west_of other current ∨ area.is_east_of other current → Area.can_connect_to area current other
  | NS : area[current] = Tile.pipe .NS → area.is_north_of other current ∨ area.is_south_of other current → Area.can_connect_to area current other

instance {area : Area} {current other : Coordinate area.width area.height} : Decidable (Area.can_connect_to area current other) :=
  match h : area[current] with
  | Tile.ground | Tile.start =>
    have : Area.can_connect_to area current other → False := by intro x; cases x <;> rename_i hx _ <;> rw[h] at hx <;> contradiction
    Decidable.isFalse this
  | Tile.pipe .NE =>
    if h₁ : area.is_north_of other current ∨ area.is_east_of other current then
      Decidable.isTrue $ Area.can_connect_to.NE h h₁
    else
      have : Area.can_connect_to area current other → False := by
        intro x; cases x <;> rename_i hx hx₂ <;> rw[hx] at h
        all_goals
          try simp at h
          try exact absurd hx₂ h₁
      Decidable.isFalse this
  | Tile.pipe .ES =>
    if h₁ : area.is_south_of other current ∨ area.is_east_of other current then
      Decidable.isTrue $ Area.can_connect_to.ES h h₁
    else
      have : Area.can_connect_to area current other → False := by
        intro x; cases x <;> rename_i hx hx₂ <;> rw[hx] at h
        all_goals
          try simp at h
          try exact absurd hx₂ h₁
      Decidable.isFalse this
  | Tile.pipe .SW =>
    if h₁ : area.is_south_of other current ∨ area.is_west_of other current then
      Decidable.isTrue $ Area.can_connect_to.SW h h₁
    else
      have : Area.can_connect_to area current other → False := by
        intro x; cases x <;> rename_i hx hx₂ <;> rw[hx] at h
        all_goals
          try simp at h
          try exact absurd hx₂ h₁
      Decidable.isFalse this
  | Tile.pipe .WN =>
    if h₁ : area.is_north_of other current ∨ area.is_west_of other current then
      Decidable.isTrue $ Area.can_connect_to.WN h h₁
    else
      have : Area.can_connect_to area current other → False := by
        intro x; cases x <;> rename_i hx hx₂ <;> rw[hx] at h
        all_goals
          try simp at h
          try exact absurd hx₂ h₁
      Decidable.isFalse this
  | Tile.pipe .NS =>
    if h₁ : area.is_north_of other current ∨ area.is_south_of other current then
      Decidable.isTrue $ Area.can_connect_to.NS h h₁
    else
      have : Area.can_connect_to area current other → False := by
        intro x; cases x <;> rename_i hx hx₂ <;> rw[hx] at h
        all_goals
          try simp at h
          try exact absurd hx₂ h₁
      Decidable.isFalse this
  | Tile.pipe .WE =>
    if h₁ : area.is_west_of other current ∨ area.is_east_of other current then
      Decidable.isTrue $ Area.can_connect_to.WE h h₁
    else
      have : Area.can_connect_to area current other → False := by
        intro x; cases x <;> rename_i hx hx₂ <;> rw[hx] at h
        all_goals
          try simp at h
          try exact absurd hx₂ h₁
      Decidable.isFalse this

theorem Coordinate.go_east_is_east_of (area : Area) (c o : Coordinate area.width area.height) (h₁ : c.goEast = some o) : area.is_east_of o c := by
  unfold Coordinate.goEast at h₁
  split at h₁ <;> simp at h₁
  case isTrue h₂ =>
    unfold Area.is_east_of Area.is_west_of Area.can_connect_to.is_succ
    simp[←h₁]
    exact h₂

theorem Coordinate.go_west_is_west_of (area : Area) (c o : Coordinate area.width area.height) (h₁ : c.goWest = some o) : area.is_west_of o c := by
  unfold Coordinate.goWest at h₁
  split at h₁ <;> simp at h₁
  case isTrue h₂ =>
    unfold Area.is_west_of Area.can_connect_to.is_succ
    simp[←h₁, Fin.ext_iff]

theorem Coordinate.go_north_is_north_of (area : Area) (c o : Coordinate area.width area.height) (h₁ : c.goNorth = some o) : area.is_north_of o c := by
  unfold Coordinate.goNorth at h₁
  split at h₁ <;> simp at h₁
  case isTrue h₂ =>
    unfold Area.is_north_of Area.can_connect_to.is_succ
    simp[←h₁, Fin.ext_iff]

theorem Coordinate.go_south_is_south_of (area : Area) (c o : Coordinate area.width area.height) (h₁ : c.goSouth = some o) : area.is_south_of o c := by
  unfold Coordinate.goSouth at h₁
  split at h₁ <;> simp at h₁
  case isTrue h₂ =>
    unfold Area.is_south_of Area.is_north_of Area.can_connect_to.is_succ
    simp[←h₁]
    exact h₂

def Area.are_connected (area : Area) (current : Coordinate area.width area.height) (previous : Coordinate area.width area.height) : Prop :=
  area.can_connect_to current previous ∧ area.can_connect_to previous current

structure Area.PathHead (area : Area) where
  current : Coordinate area.width area.height
  previous : Coordinate area.width area.height
  current_can_connect_to_previous : area.can_connect_to current previous

structure Area.BidirPathHead (area : Area) extends Area.PathHead area where
  previous_can_connect_to_current : area.can_connect_to previous current

private theorem Area.can_connect_to_imp_not_start_not_ground (h₁ : Area.can_connect_to area c t) : area[c] ≠ Tile.ground ∧ area[c] ≠ Tile.start :=
  have h₂ : area[c] ≠ Tile.ground := by
    cases ht : (area[c] == Tile.ground) <;> simp at ht
    case false => assumption
    case true =>
      cases h₁ <;> simp_all
  have h₃ : area[c] ≠ Tile.start := by
    cases ht : (area[c] == Tile.start) <;> simp at ht
    case false => assumption
    case true =>
      cases h₁ <;> simp_all
  And.intro h₂ h₃

private theorem Area.PathHead.current_not_start_not_ground (pathHead : Area.PathHead area) : area[pathHead.current] ≠ Tile.ground ∧ area[pathHead.current] ≠ Tile.start :=
  Area.can_connect_to_imp_not_start_not_ground pathHead.current_can_connect_to_previous

section
variable (area : Area)
local infixl:55 "is_west_of" => area.is_west_of
local infixl:55 "is_north_of" => area.is_north_of
local infixl:55 "is_east_of" => area.is_east_of
local infixl:55 "is_south_of" => area.is_south_of

private def Area.nextPathStep (last_step: Area.PathHead area) : Option (Area.BidirPathHead area) :=
  let can_connect_to_current := (area.can_connect_to · last_step.current)
  let currentTile := area[last_step.current]'(And.intro rfl rfl)
  have h₀ : area[last_step.current] = currentTile := rfl
  have ⟨(_h₁ : currentTile ≠ Tile.ground), (_h₂ : currentTile ≠ Tile.start)⟩ := Area.PathHead.current_not_start_not_ground last_step

  let next : Option $ (next : Coordinate area.width area.height) ×' (area.can_connect_to last_step.current next) := match h₃ : currentTile with
  | .pipe .NE =>
    if h₄ : last_step.previous is_north_of last_step.current then
      last_step.current.goEast.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.NE h₃ (Or.inr $ Coordinate.go_east_is_east_of _ _ _ h₅)
    else
      -- not that those proofs would be needed, but as kind of an assert:
      have := by cases hc : last_step.current_can_connect_to_previous <;> rw[h₀] at * <;> simp_all; rename_i x; exact x
      have : last_step.previous is_east_of last_step.current := by simp[h₄] at this; exact this
      last_step.current.goNorth.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.NE h₃ (Or.inl $ Coordinate.go_north_is_north_of _ _ _ h₅)
  | .pipe .ES =>
    if h₄ : last_step.previous is_east_of last_step.current then
      last_step.current.goSouth.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.ES h₃ (Or.inl $ Coordinate.go_south_is_south_of _ _ _ h₅)
    else
      have := by cases hc : last_step.current_can_connect_to_previous <;> rw[h₀] at * <;> simp_all; rename_i x; exact x
      have : last_step.previous is_south_of last_step.current := by simp[h₄] at this; exact this
      last_step.current.goEast.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.ES h₃ (Or.inr $ Coordinate.go_east_is_east_of _ _ _ h₅)
  | .pipe .SW =>
    if h₄ : last_step.previous is_south_of last_step.current then
      last_step.current.goWest.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.SW h₃ (Or.inr $ Coordinate.go_west_is_west_of _ _ _ h₅)
    else
      have := by cases hc : last_step.current_can_connect_to_previous <;> rw[h₀] at * <;> simp_all; rename_i x; exact x
      have : last_step.previous is_west_of last_step.current := by simp[h₄] at this; exact this
      last_step.current.goSouth.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.SW h₃ (Or.inl $ Coordinate.go_south_is_south_of _ _ _ h₅)
  | .pipe .WN =>
    if h₄ : last_step.previous is_west_of last_step.current then
      last_step.current.goNorth.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.WN h₃ (Or.inl $ Coordinate.go_north_is_north_of _ _ _ h₅)
    else
      have := by cases hc : last_step.current_can_connect_to_previous <;> rw[h₀] at * <;> simp_all; rename_i x; exact x
      have : last_step.previous is_north_of last_step.current := by simp[h₄] at this; exact this
      last_step.current.goWest.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.WN h₃ (Or.inr $ Coordinate.go_west_is_west_of _ _ _ h₅)
  | .pipe .NS =>
    if h₄ : last_step.previous is_north_of last_step.current then
      last_step.current.goSouth.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.NS h₃ (Or.inr $ Coordinate.go_south_is_south_of _ _ _ h₅)
    else
      have := by cases hc : last_step.current_can_connect_to_previous <;> rw[h₀] at * <;> simp_all; rename_i x; exact x
      have : last_step.previous is_south_of last_step.current := by simp[h₄] at this; exact this
      last_step.current.goNorth.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.NS h₃ (Or.inl $ Coordinate.go_north_is_north_of _ _ _ h₅)
  | .pipe .WE =>
    if h₄ : last_step.previous is_west_of last_step.current then
      last_step.current.goEast.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.WE h₃ (Or.inr $ Coordinate.go_east_is_east_of _ _ _ h₅)
    else
      have := by cases hc : last_step.current_can_connect_to_previous <;> rw[h₀] at * <;> simp_all; rename_i x; exact x
      have : last_step.previous is_east_of last_step.current := by simp[h₄] at this; exact this
      last_step.current.goWest.mapWithProof λ next h₅ ↦
        PSigma.mk next $ Area.can_connect_to.WE h₃ (Or.inl $ Coordinate.go_west_is_west_of _ _ _ h₅)

  next.bind λ (PSigma.mk next h₇) ↦
    if h₆ : can_connect_to_current next then
      some {
        current := next
        previous := last_step.current
        current_can_connect_to_previous := h₆
        previous_can_connect_to_current := h₇
      }
    else
      none

private theorem Area.nextPathStep_previous_current {area : Area} (p: area.PathHead) {n : BidirPathHead area} (h₁ : area.nextPathStep p = some n) : n.previous = p.current := by
  unfold Area.nextPathStep Option.bind at h₁
  simp at h₁
  split at h₁
  split at h₁
  case h_1 => contradiction
  case h_2 =>
    dsimp only at h₁
    split at h₁
    case isFalse => contradiction
    case isTrue =>
      simp only [Option.some.injEq] at h₁
      simp[←h₁]

private structure Area.PathStarts where
  north : Option (Σ'(h: PathHead area), h.previous = area.start ×' h.current is_north_of area.start)
  east : Option (Σ'(h: PathHead area), h.previous = area.start ×' h.current is_east_of area.start)
  south : Option (Σ'(h: PathHead area), h.previous = area.start ×' h.current is_south_of area.start)
  west : Option (Σ'(h: PathHead area), h.previous = area.start ×' h.current is_west_of area.start)

private def Area.pathStarts : Area.PathStarts area :=
  let toStart : {p : Coordinate area.width area.height → Prop} → (c : Option $ Coordinate area.width area.height) → (h₁ : ∀o, c = some o → (p o)) → Option (Σ' (h:area.PathHead),(h.previous = area.start ×' p h.current))  := λc h₁↦
    c.bindWithProof λ o hc =>
      if h₂ : area.can_connect_to o area.start then
        let ph : PathHead area := {current := o, previous := area.start, current_can_connect_to_previous := h₂}
        let h₃ : ph.previous = area.start := rfl
        some $ ⟨ph, (PProd.mk h₃ $ h₁ ph.current hc)⟩
      else
        none
  {
    north := toStart (area.start.goNorth) (Coordinate.go_north_is_north_of area area.start)
    east := toStart (area.start.goEast) (Coordinate.go_east_is_east_of area area.start)
    south := toStart (area.start.goSouth) (Coordinate.go_south_is_south_of area area.start)
    west := toStart (area.start.goWest) (Coordinate.go_west_is_west_of area area.start)
  }

private def Area.pathStartsList : List (Area.PathHead area) :=
  let starts := area.pathStarts
  [ PSigma.fst <$> starts.north, PSigma.fst <$> starts.east, PSigma.fst <$> starts.south, PSigma.fst <$> starts.west].filterMap id

private def removePathsMet {area : Area} : (List $ Area.PathHead area) → (List $ Area.PathHead area)
| [] => []
| p :: ps =>
  let rest := ps.filter λs ↦ s.current ≠ p.current
  if rest.length = ps.length then -- no match, keep current path too
    p :: removePathsMet rest
  else --removed another path. Remove current too.
    removePathsMet rest
termination_by x => x.length
decreasing_by
  all_goals
    simp_wf
    exact Nat.lt_succ.mpr $ List.listFilterSmallerOrEqualList _ _


private def noSolution {area : Area} : (List $ Area.PathHead area) → Bool
| [] => true
| _ :: [] => true
| _ => false

section ListMonad
local instance : Monad List where
  bind := List.bind
  pure := List.pure

def part1 (area : Area) : List Nat := do
  let mut paths : List (Area.PathHead area) := area.pathStartsList

  --Lean does not do termination checking here, but that would fail.
  --One could, however, prove that this terminates, because the paths cannot cross, do not reverse
  --and the search space is finite.
  let mut steps := 1
  let mut solutions : List Nat := []
  while !noSolution paths do
    steps := steps + 1 -- it's fine to do the first step without checking for a result. The first result is at least 2 steps from start.
    paths := paths.filterMap (Functor.map Area.BidirPathHead.toPathHead ∘ area.nextPathStep)
    let newPaths := removePathsMet paths
    if paths.length ≠ newPaths.length then
      solutions := steps :: solutions
    paths := newPaths
  solutions

end ListMonad

------------------------------------------------------------------------------------------------------------

private def Area.ConnectedPathPart {area : Area} (path : List $ Coordinate area.width area.height) : Prop := match path with
| [] => False
| s :: [] => area.can_connect_to s area.start
| s :: ss :: sss => area.are_connected s ss ∧ Area.ConnectedPathPart (ss :: sss)

private structure Area.PathsPart where
  steps : List $ Coordinate area.width area.height
  connected : Area.ConnectedPathPart steps

private theorem Area.PathsPart.list_not_empty {area : Area} (pp : area.PathsPart) : pp.steps ≠ [] := match pp.steps, pp.connected with
| [], hx => hx.elim
| s :: ss, _ => List.cons_ne_nil s ss

private theorem Area.PathsPart.tail_connect_start {area : Area} (pp : area.PathsPart) : area.can_connect_to (pp.steps.getLast pp.list_not_empty) area.start :=
  match hs : pp.steps, pp.list_not_empty, pp.connected with
  | _ :: [], _, h₁ => h₁
  | s :: ss :: sss, _, ⟨_,h₂⟩ =>
    have : (ss :: sss).length < pp.steps.length := hs.substr $ (List.length_cons s (ss :: sss)).substr $ Nat.lt.base (ss :: sss).length
    Area.PathsPart.tail_connect_start ⟨ss::sss,h₂⟩
termination_by pp.steps.length



private def Area.PathsPart.pathHead {area : Area} : area.PathsPart → area.PathHead
| { steps := s :: [], connected} =>
  {
    current := s
    previous := area.start
    current_can_connect_to_previous := connected
  }
| { steps := s :: ss :: _, connected} =>
  {
    current := s
    previous := ss
    current_can_connect_to_previous := connected.left.left
  }

private structure Area.Paths where
  north : Option $ Area.PathsPart area
  east : Option $ Area.PathsPart area
  south : Option $ Area.PathsPart area
  west : Option $ Area.PathsPart area
  north_valid : ∀n, north = some n → (n.steps.getLast (Area.PathsPart.list_not_empty n)) is_north_of area.start
  east_valid : ∀e, east = some e → (e.steps.getLast (Area.PathsPart.list_not_empty e)) is_east_of area.start
  south_valid : ∀s, south = some s → (s.steps.getLast (Area.PathsPart.list_not_empty s)) is_south_of area.start
  west_valid : ∀w, west = some w → (w.steps.getLast (Area.PathsPart.list_not_empty w)) is_west_of area.start

private def Area.Paths.fromPathStarts {area : Area} (starts : Area.PathStarts area) : Area.Paths area :=
  let toPathsPart : (h : area.PathHead) → (h.previous = area.start) → area.PathsPart := λh h₁ ↦ { steps := [h.current], connected := h₁.subst h.current_can_connect_to_previous}
  {
    north := starts.north.map λ ⟨c, ⟨h₁, _⟩⟩ ↦ toPathsPart c h₁
    east := starts.east.map λ ⟨c, ⟨h₁, _⟩⟩ ↦ toPathsPart c h₁
    south := starts.south.map λ ⟨c, ⟨h₁, _⟩⟩ ↦ toPathsPart c h₁
    west := starts.west.map λ ⟨c, ⟨h₁, _⟩⟩ ↦ toPathsPart c h₁
    north_valid := λn h₁ ↦ by
      have : (starts.north.get (Option.isSome_map.subst $ (Option.isSome_iff_exists.mpr ⟨n,h₁⟩).symm).symm).fst.current = n.steps.getLast n.list_not_empty :=
        let ⟨w, h₁⟩ := Option.map_eq_some'.mp h₁
        by simp only [h₁.left, Option.get_some, ←h₁.right, List.getLast_singleton]
      have h₂ := (starts.north.get (Option.isSome_map.subst $ (Option.isSome_iff_exists.mpr ⟨n,h₁⟩).symm).symm).snd.snd
      simp[this] at h₂
      assumption
    east_valid := λe h₁ ↦ by
      have : (starts.east.get (Option.isSome_map.subst $ (Option.isSome_iff_exists.mpr ⟨e,h₁⟩).symm).symm).fst.current = e.steps.getLast e.list_not_empty :=
        let ⟨w, h₁⟩ := Option.map_eq_some'.mp h₁
        by simp only [h₁.left, Option.get_some, ←h₁.right, List.getLast_singleton]
      have h₂ := (starts.east.get (Option.isSome_map.subst $ (Option.isSome_iff_exists.mpr ⟨e,h₁⟩).symm).symm).snd.snd
      simp[this] at h₂
      assumption
    south_valid := λs h₁ ↦ by
      have : (starts.south.get (Option.isSome_map.subst $ (Option.isSome_iff_exists.mpr ⟨s,h₁⟩).symm).symm).fst.current = s.steps.getLast s.list_not_empty :=
        let ⟨w, h₁⟩ := Option.map_eq_some'.mp h₁
        by simp only [h₁.left, Option.get_some, ←h₁.right, List.getLast_singleton]
      have h₂ := (starts.south.get (Option.isSome_map.subst $ (Option.isSome_iff_exists.mpr ⟨s,h₁⟩).symm).symm).snd.snd
      simp[this] at h₂
      assumption
    west_valid := λw h₁ ↦ by
      have : (starts.west.get (Option.isSome_map.subst $ (Option.isSome_iff_exists.mpr ⟨w,h₁⟩).symm).symm).fst.current = w.steps.getLast w.list_not_empty :=
        let ⟨w, h₁⟩ := Option.map_eq_some'.mp h₁
        by simp only [h₁.left, Option.get_some, ←h₁.right, List.getLast_singleton]
      have h₂ := (starts.west.get (Option.isSome_map.subst $ (Option.isSome_iff_exists.mpr ⟨w,h₁⟩).symm).symm).snd.snd
      simp[this] at h₂
      assumption
  }

private def Area.Paths.step : (paths : area.Paths) →  area.Paths
| {north, east, south, west, north_valid, east_valid, south_valid, west_valid} =>
  -- This lambda is so fugly, because I couldn't prove the equality of the list ends outside of it...
  let progress : {p : area.PathsPart → Prop} → (i : area.PathsPart) → (∀(j:area.PathsPart), j.steps.getLast j.list_not_empty = i.steps.getLast i.list_not_empty → (p j)) → Option (Σ' (r : area.PathsPart), p r) := λ pp h₀ ↦
      (area.nextPathStep pp.pathHead).mapWithProof λ ph h₁ ↦
      have h₂ : ph.previous = pp.pathHead.current := Area.nextPathStep_previous_current pp.pathHead h₁
      have h₃ : pp.steps.head pp.list_not_empty = pp.pathHead.current :=
        match pp with
        | {steps := s :: [], connected} => rfl
        | {steps := s :: ss, connected} =>
          match { steps := s :: ss, connected := connected : area.PathsPart} with
          | {steps := s :: [], connected} => rfl
          | {steps := s :: ss :: _, connected} => rfl
      let r : area.PathsPart := {
        steps := ph.current :: pp.steps
        connected := by
          have h₄ := ph.current_can_connect_to_previous
          have h₅ := ph.previous_can_connect_to_current
          rw[←h₃] at h₂
          rw[h₂] at h₄ h₅
          have h₆ := pp.connected
          unfold Area.ConnectedPathPart
          split ;
          case h_1 => contradiction
          case h_2 hx => simp at hx; exact absurd hx.right pp.list_not_empty
          case h_3 d1 s ss sss he =>
            clear d1
            have h₇ : ss = pp.steps.head pp.list_not_empty := by simp only [List.cons.injEq] at he; simp only [he.right, List.head_cons]
            have h₈ : s = ph.current := by simp only [List.cons.injEq] at he; simp only [he.left]
            constructor
            case left =>
              subst s ss
              exact ⟨h₄, h₅⟩
            case right =>
              have h₉ : pp.steps = ss::sss := by simp at he; exact he.right
              rw[←h₉]
              exact h₆
      }
      have : r.steps.getLast r.list_not_empty = pp.steps.getLast pp.list_not_empty :=
        match hr : r.steps, r.list_not_empty with
        | r₁ :: r₁s , _=> (And.right $ List.cons.inj hr.symm)▸(List.getLast_cons (a:=r₁) pp.list_not_empty)
      ⟨r, h₀ r this⟩

  -- Of course one could factor out the predicate and make this a function too, but it's a two-liner. Without explicit types a one-liner...
  let northPred : (area.PathsPart → Prop) := λ i ↦ i.steps.getLast i.list_not_empty is_north_of area.start
  have hn : (j:area.PathsPart) → (h₁ : northPred j) → ∀(i:area.PathsPart), (he : i.steps.getLast i.list_not_empty = j.steps.getLast j.list_not_empty) → northPred i :=
    λ j h₁ ↦ λ i he ↦ he.substr (p := λx ↦ x is_north_of area.start) h₁

  let eastPred : (area.PathsPart → Prop) := λ i ↦ i.steps.getLast i.list_not_empty is_east_of area.start
  have he : (j:area.PathsPart) → (h₁ : eastPred j) → ∀(i:area.PathsPart), (he : i.steps.getLast i.list_not_empty = j.steps.getLast j.list_not_empty) → eastPred i :=
    λ j h₁ ↦ λ i he ↦ he.substr (p := λx ↦ x is_east_of area.start) h₁

  let southPred : (area.PathsPart → Prop) := λ i ↦ i.steps.getLast i.list_not_empty is_south_of area.start
  have hs : (j:area.PathsPart) → (h₁ : southPred j) → ∀(i:area.PathsPart), (he : i.steps.getLast i.list_not_empty = j.steps.getLast j.list_not_empty) → southPred i :=
    λ j h₁ ↦ λ i he ↦ he.substr (p := λx ↦ x is_south_of area.start) h₁

  let westPred : (area.PathsPart → Prop) := λ i ↦ i.steps.getLast i.list_not_empty is_west_of area.start
  have hw : (j:area.PathsPart) → (h₁ : westPred j) → ∀(i:area.PathsPart), (he : i.steps.getLast i.list_not_empty = j.steps.getLast j.list_not_empty) → westPred i :=
    λ j h₁ ↦ λ i he ↦ he.substr (p := λx ↦ x is_west_of area.start) h₁


  let nn := extractProof $ north.bindWithProof λ x h ↦ progress x (hn x $ north_valid x h)
  let ne := extractProof $ east.bindWithProof λ x h ↦ progress x (he x $ east_valid x h)
  let ns := extractProof $ south.bindWithProof λ x h ↦ progress x (hs x $ south_valid x h)
  let nw := extractProof $ west.bindWithProof λ x h ↦ progress x (hw x $ west_valid x h)

  {
    north := nn.fst
    east := ne.fst
    south := ns.fst
    west := nw.fst
    north_valid := nn.snd
    east_valid := ne.snd
    south_valid := ns.snd
    west_valid := nw.snd
  }
where
  extractProof : {a : Type} → {b : a → Prop} → (Option (PSigma b)) → ((h: Option a) ×' ∀aa, h = some aa → b aa) :=
  λ i ↦ ⟨match i with | .none => none | .some v => some v.fst, by cases i <;> simp; case some b => exact b.snd⟩

private structure Area.ClosedPath extends area.PathsPart where
  closed : area.can_connect_to (steps.head (toPathsPart.list_not_empty)) area.start
  start : Pipe
  start_valid : match start with
  | .NE => toPathsPart.steps.getLast (toPathsPart.list_not_empty) is_north_of area.start ∧ toPathsPart.steps.head (toPathsPart.list_not_empty) is_east_of area.start
  | .ES => toPathsPart.steps.getLast (toPathsPart.list_not_empty) is_east_of area.start ∧ toPathsPart.steps.head (toPathsPart.list_not_empty) is_south_of area.start
  | .SW => toPathsPart.steps.getLast (toPathsPart.list_not_empty) is_south_of area.start ∧ toPathsPart.steps.head (toPathsPart.list_not_empty) is_west_of area.start
  | .WN => toPathsPart.steps.getLast (toPathsPart.list_not_empty) is_west_of area.start ∧ toPathsPart.steps.head (toPathsPart.list_not_empty) is_north_of area.start
  | .NS => toPathsPart.steps.getLast (toPathsPart.list_not_empty) is_north_of area.start ∧ toPathsPart.steps.head (toPathsPart.list_not_empty) is_south_of area.start
  | .WE => toPathsPart.steps.getLast (toPathsPart.list_not_empty) is_west_of area.start ∧ toPathsPart.steps.head (toPathsPart.list_not_empty) is_east_of area.start

private def Area.PathsPart.join (a b : area.PathsPart) (h₁ : area.are_connected (a.steps.head a.list_not_empty) (b.steps.head b.list_not_empty)) : area.PathsPart :=
  --Proofs in this function would get much simpler if the pattern match contained h₁.
  --But then the proof below (Area.PathsPart.join_b_last_head) gets really hard...
  match hb : b.steps, ha : a.steps, a.list_not_empty, b.list_not_empty, a.connected, b.connected with
  | bh :: [], ah :: as, _, _, h₂, _ =>
    {
      steps := bh :: ah :: as
      connected := by
        simp[Area.ConnectedPathPart, h₂] at h₁ ⊢
        simp[ha, hb] at h₁
        exact h₁.symm
    }
  | bh :: b1 :: bs, ah :: as, _, _, h₂, h₃=>
    let c : area.PathsPart := {
      steps := bh :: ah :: as
      connected := ⟨by simp[ha, hb] at h₁; exact h₁.symm, h₂⟩
    }
    let d : area.PathsPart := {
      steps := b1 :: bs
      connected := h₃.right
    }
    have : bs.length + 1 < b.steps.length := by simp only [hb, List.length_cons, Nat.lt_add_one]
    Area.PathsPart.join c d h₃.left
termination_by b.steps.length

--private def Area.PathsPart.join (a b : area.PathsPart) (h₁ : area.are_connected (a.steps.head a.list_not_empty) (b.steps.head b.list_not_empty)) : area.PathsPart :=
--  match hb : b.steps, a.steps, a.list_not_empty, b.list_not_empty, h₁, a.connected, b.connected with
--  | bh :: [], ah :: as, _, _, h₁, h₂, _ =>
--    {
--      steps := bh :: ah :: as
--      connected := by
--        simp[Area.ConnectedPathPart, h₂] at h₁ ⊢
--        exact h₁.symm
--    }
--  | bh :: b1 :: bs, ah :: as, _, _, h₁, h₂, h₃=>
--    let c : area.PathsPart := {
--      steps := bh :: ah :: as
--      connected := ⟨h₁.symm, h₂⟩
--    }
--    let d : area.PathsPart := {
--      steps := b1 :: bs
--      connected := h₃.right
--    }
--    have : bs.length + 1 < b.steps.length := by simp only [hb, List.length_cons, Nat.lt_add_one]
--    Area.PathsPart.join c d h₃.left
--termination_by b.steps.length

private theorem Area.PathsPart.join_b_last_head (a b : area.PathsPart) (h₁ : area.are_connected (a.steps.head a.list_not_empty) (b.steps.head b.list_not_empty)) : (Area.PathsPart.join area a b h₁).steps.head (Area.PathsPart.join area a b h₁).list_not_empty = b.steps.getLast b.list_not_empty := by
  generalize h₂ : (Day10.Area.PathsPart.join area a b h₁) = o
  unfold Area.PathsPart.join at h₂
  split at h₂
  case h_1 bh ah as _ _ h₄ h₃ _ _ _ _ hb ha _ _ _ _ =>
    simp[hb, ←h₂]
  case h_2 bh b1 bs ah as _ _ h₄ h₃ d4 d3 d2 d1 hb ha d5 d6 d7 d8 =>
    clear d1 d2 d3 d4 d5 d6 d7 d8
    simp only at h₂
    simp[hb]
    have : ∀ g₁ g₂, (bh :: b1 ::bs).getLast g₁ = (b1 :: bs).getLast g₂ := by intros; exact List.getLast_cons (by simp : b1 :: bs ≠ [])
    rw[this]
    case g₂ => simp
    subst o
    have : bs.length + 1 < b.steps.length := by simp only [hb, List.length_cons, Nat.lt_add_one]
    apply Area.PathsPart.join_b_last_head
termination_by b.steps.length

private theorem Area.PathsPart.join_a_last_last (a b : area.PathsPart) (h₁ : area.are_connected (a.steps.head a.list_not_empty) (b.steps.head b.list_not_empty)) : (Area.PathsPart.join area a b h₁).steps.getLast (Area.PathsPart.join area a b h₁).list_not_empty = a.steps.getLast a.list_not_empty := by
  generalize h₂ : (Day10.Area.PathsPart.join area a b h₁) = o
  unfold Area.PathsPart.join at h₂
  split at h₂
  case h_1 bh ah as _ _ h₄ h₃ _ _ _ _ hb ha _ _ _ _ =>
    simp[hb, ←h₂, ←ha]
    apply List.getLast_cons
  case h_2 bh b1 bs ah as _ _ h₄ h₃ d4 d3 d2 d1 hb ha d5 d6 d7 d8 =>
    clear d1 d2 d3 d4 d5 d6 d7 d8
    simp only at h₂
    simp[hb, ←h₂, ←ha]
    rw[←List.getLast_cons (a := bh) a.list_not_empty]
    have : bs.length + 1 < b.steps.length := by simp only [hb, List.length_cons, Nat.lt_add_one]
    apply Area.PathsPart.join_a_last_last
termination_by b.steps.length

-- Don't have the brain right now to write a dependent function that expresses this.
macro "def_Area.ClosedPath.from" fn:ident ":" p1:term ", "  p2:term " : " p3:term : command =>
  `(private def $fn (n : area.PathsPart) (hn : $p1 (n.steps.getLast n.list_not_empty) area.start) (e : area.PathsPart) (he : $p2 (e.steps.getLast e.list_not_empty) area.start) (h₁ : n.steps.head n.list_not_empty = e.steps.head e.list_not_empty) : area.ClosedPath :=
  --if this function would also demand equal path part length, the following branch could be eliminated.
  let ⟨joinedPath, ⟨h₁, h₂⟩⟩ : ((p : area.PathsPart) ×' (PProd (p.steps.head p.list_not_empty = e.steps.getLast e.list_not_empty) (p.steps.getLast p.list_not_empty = n.steps.getLast n.list_not_empty))) :=
    match hn₁ : n.steps, n.list_not_empty, n.connected with
    | [n1], _, _ =>
      have : e.steps.tail ≠ [] := match he₁ : e.steps, e.list_not_empty with
      | _ :: e2 :: es, _ => by simp only [List.tail_cons, reduceCtorEq, ne_eq, not_false_eq_true]
      | e1 :: [], _ => by
        simp[he₁, hn₁] at *
        subst e1
        try exact Area.can_connect_to.is_succ.irrefl hn.left he.left -- NS and WE cases
        try -- other cases
          try unfold Area.is_east_of at he
          try unfold Area.is_south_of at he
          try unfold Area.is_north_of at he
          try unfold Area.is_west_of at he
          rw[hn.right] at he
          unfold Area.can_connect_to.is_succ at he
          split at he <;> simp[Fin.ext_iff] at he
      match he₁ : e.steps, e.list_not_empty, this, e.connected with
      | e1 :: e2 :: es, _, _, ⟨hc₁ ,hc₂⟩ =>
        let b : area.PathsPart := {
          steps := e2 :: es
          connected := hc₂
        }
        have h₂: area.are_connected (n.steps.head n.list_not_empty) (b.steps.head b.list_not_empty) := by simp[hn₁]; simp[hn₁, he₁] at h₁; exact h₁▸hc₁
        ⟨Area.PathsPart.join area n b h₂, ⟨Area.PathsPart.join_b_last_head area n b h₂, by simp[Area.PathsPart.join_a_last_last area n b h₂, hn₁]⟩ ⟩
    | n1 :: n2 :: ns, _, ⟨hc₁, hc₂⟩ =>
      let a : area.PathsPart := {
        steps := n2 :: ns
        connected := hc₂
      }
      have h₂ : area.are_connected (a.steps.head a.list_not_empty) (e.steps.head e.list_not_empty) := by simp[hn₁]; simp[hn₁] at h₁; exact h₁▸(hc₁.symm)
      ⟨Area.PathsPart.join area a e h₂, ⟨Area.PathsPart.join_b_last_head area a e h₂, Area.PathsPart.join_a_last_last area a e h₂⟩⟩
  --Area.PathsPart.tail_connect_start
  {
    toPathsPart := joinedPath
    closed := h₁▸(Area.PathsPart.tail_connect_start e)
    start := $p3
    start_valid := ⟨h₂▸hn, h₁▸he⟩
  })

def_Area.ClosedPath.from Area.ClosedPath.fromNE : area.is_north_of, area.is_east_of : Pipe.NE
def_Area.ClosedPath.from Area.ClosedPath.fromES : area.is_east_of, area.is_south_of : Pipe.ES
def_Area.ClosedPath.from Area.ClosedPath.fromSW : area.is_south_of, area.is_west_of : Pipe.SW
def_Area.ClosedPath.from Area.ClosedPath.fromWN : area.is_west_of, area.is_north_of : Pipe.WN
def_Area.ClosedPath.from Area.ClosedPath.fromNS : area.is_north_of, area.is_south_of : Pipe.NS
def_Area.ClosedPath.from Area.ClosedPath.fromWE : area.is_west_of, area.is_east_of : Pipe.WE

-- Takes a list of existing closed paths and the current paths state, and moves all closed paths from the paths state to the list of closed paths.
-- This is needed, as there may be 2 solutions. There might for instance be a closed path from North to East, and another one from South to West.
private def Area.Paths.extractSolutions {area : Area} (paths : area.Paths) (solutions : List area.ClosedPath) : (area.Paths × List area.ClosedPath) :=
  let solution :
    (a : Option area.PathsPart)
    → (b : Option area.PathsPart)
    → (Option ((ab : (area.PathsPart) × (area.PathsPart)) ×' (
        a = some ab.fst
        ∧ b = some ab.snd
        ∧ ab.fst.steps.head ab.fst.list_not_empty = ab.snd.steps.head ab.snd.list_not_empty)))
    := λ a b ↦
      match a, b with
      | some aa, some bb =>
        if h: aa.steps.head aa.list_not_empty = bb.steps.head bb.list_not_empty then
          some ⟨(aa,bb),⟨rfl,⟨rfl, h⟩⟩⟩
        else
          none
      | _, _ => none

  -- NE
  if let some ⟨(n,e),ns,es,he₁⟩ := solution paths.north paths.east then
    let s1 := (Area.ClosedPath.fromNE area n (paths.north_valid n ns) e (paths.east_valid e es) he₁)
    if let some ⟨(s,w),ss,ws,he₂⟩ := solution paths.south paths.west then
      (
        { north := none, south := none, east := none, west := none, north_valid := nofun, east_valid := nofun, south_valid := nofun, west_valid := nofun },
        s1 :: Area.ClosedPath.fromSW area s (paths.south_valid s ss) w (paths.west_valid w ws) he₂ :: solutions
      )
    else
      (
        {paths with north := none, east := none, north_valid := nofun, east_valid := nofun},
        s1 :: solutions
      )
  -- NS
  else if let some ⟨(n,s),ns,ss,he₁⟩ := solution paths.north paths.south then
    -- no point in checking WE - paths cannot cross. (todo?: prove)
    (
      {paths with north := none, south := none, north_valid := nofun, south_valid := nofun},
      Area.ClosedPath.fromNS area n (paths.north_valid n ns) s (paths.south_valid s ss) he₁ :: solutions
    )
  -- WN
  else if let some ⟨(w,n),ws,ns,he₁⟩ := solution paths.west paths.north then
    let s1 := (Area.ClosedPath.fromWN area w (paths.west_valid w ws) n (paths.north_valid n ns) he₁)
    if let some ⟨(e,s),es,ss,he₂⟩ := solution paths.east paths.south then
      (
        { north := none, south := none, east := none, west := none, north_valid := nofun, east_valid := nofun, south_valid := nofun, west_valid := nofun },
        s1 :: Area.ClosedPath.fromES area e (paths.east_valid e es) s (paths.south_valid s ss) he₂ :: solutions
      )
    else
      (
        {paths with west := none, north := none, west_valid := nofun, north_valid := nofun},
        s1 :: solutions
      )
  -- ES
  else if let some ⟨(e,s),es,ss,he₁⟩ := solution paths.east paths.south then
    -- no point in checking WN again, has been checked already
    (
      {paths with east := none, south := none, east_valid := nofun, south_valid := nofun},
      Area.ClosedPath.fromES area e (paths.east_valid e es) s (paths.south_valid s ss) he₁ :: solutions
    )
  -- WE
  else if let some ⟨(w,e),ws,es,he₁⟩ := solution paths.west paths.east then
    -- no point in checking NS - paths cannot cross.
    (
      {paths with west := none, east := none, west_valid := nofun, east_valid := nofun},
      Area.ClosedPath.fromWE area w (paths.west_valid w ws) e (paths.east_valid e es) he₁ :: solutions
    )
  -- SW
  else if let some ⟨(s,w),ss,ws,he₁⟩ := solution paths.south paths.west then
    -- NE has been checked already
    (
      {paths with south := none, west := none, south_valid := nofun, west_valid := nofun},
      Area.ClosedPath.fromSW area s (paths.south_valid s ss) w (paths.west_valid w ws) he₁ :: solutions
    )
  else
    (paths, solutions)

private def Area.Paths.unsolvable {area : Area} (paths : area.Paths) : Bool :=
  let count := λ (o : Option area.PathsPart) (i : Nat) ↦ if o.isSome then i + 1 else i
  let c := 0
    |> count paths.north
    |> count paths.east
    |> count paths.south
    |> count paths.west
  c < 2
end

private def coordinateSorter (a b : Coordinate w h) : Bool :=
  a.y < b.y ∨ (a.y = b.y ∧ a.x ≤ b.x)

private theorem coordinateSorter_transitive (w h : Nat) : BinaryHeap.transitive_le (coordinateSorter (w := w) (h := h)) := by
  unfold BinaryHeap.transitive_le
  intros a b c
  unfold coordinateSorter
  simp
  omega

private theorem coordinateSorter_total (w h : Nat) : BinaryHeap.total_le (coordinateSorter (w := w) (h := h)) := by
  unfold BinaryHeap.total_le
  intros a b
  unfold coordinateSorter
  simp
  omega

private structure PipeAtCoordinate (area : Area) where
  coordinate : Coordinate (area.width) (area.height)
  pipe : Pipe

private def PipeAtCoordinate.sortByCoordinate (a b : PipeAtCoordinate area) : Bool :=
  coordinateSorter a.coordinate b.coordinate

private theorem PipeAtCoordinate.sortByCoordinate_trans (area : Area) : BinaryHeap.transitive_le (PipeAtCoordinate.sortByCoordinate (area := area)) :=
  λ a b c ↦ coordinateSorter_transitive area.width area.height a.coordinate b.coordinate c.coordinate

private theorem PipeAtCoordinate.sortByCoordinate_total (area : Area) : BinaryHeap.total_le (PipeAtCoordinate.sortByCoordinate (area := area)) :=
  λ a b ↦ coordinateSorter_total area.width area.height a.coordinate b.coordinate

private def PipeAtCoordinate.totalAndTransitiveLe (area : Area) : BinaryHeap.TotalAndTransitiveLe (PipeAtCoordinate.sortByCoordinate (area := area)) := ⟨sortByCoordinate_trans area, sortByCoordinate_total area⟩

section ListMonad
-- We can do this here without perf issues. The list in question will never have more than 2 elements.
local instance : Monad List where
  pure := List.pure
  bind := List.bind

private inductive WestEastFoldState (area : Area)
| inside : Coordinate area.width area.height → WestEastFoldState area
| outside : WestEastFoldState area

private structure WestEastFold (area : Area) where
  state : WestEastFoldState area
  accumulator : Nat

private def WestEastFold.accumulate (old : WestEastFold area) (element : PipeAtCoordinate area) : WestEastFold area :=
  match old, element with
  | { state := .outside, accumulator}, {pipe := Pipe.NE, coordinate}
  | { state := .outside, accumulator}, {pipe := Pipe.WN, coordinate}
  | { state := .outside, accumulator}, {pipe := Pipe.NS, coordinate} => { state := .inside coordinate, accumulator}
  | { state := .outside, accumulator}, {pipe := Pipe.ES, ..}
  | { state := .outside, accumulator}, {pipe := Pipe.SW, ..}
  | { state := .outside, accumulator}, {pipe := Pipe.WE, ..} => { state := .outside, accumulator}
  | { state := .inside lastWall, accumulator}, {pipe := Pipe.NE, coordinate}
  | { state := .inside lastWall, accumulator}, {pipe := Pipe.WN, coordinate}
  | { state := .inside lastWall, accumulator}, {pipe := Pipe.NS, coordinate} => { state := .outside, accumulator := accumulator + (coordinate.x - lastWall.x - 1)}
  | { state := .inside lastWall, accumulator}, {pipe := Pipe.ES, coordinate}
  | { state := .inside lastWall, accumulator}, {pipe := Pipe.SW, coordinate}
  | { state := .inside lastWall, accumulator}, {pipe := Pipe.WE, coordinate} => { state := .inside coordinate, accumulator := accumulator + (coordinate.x - lastWall.x - 1)}

def part2 (area : Area) : List Nat := do
  let mut paths := Area.Paths.fromPathStarts area.pathStarts
  let mut solutions := []
  while !paths.unsolvable do
    (paths, solutions) := Area.Paths.extractSolutions paths solutions
    paths := paths.step
  let s ← solutions
  let pipesAtCoordinate := closedPathToPipesAtCoordinate s
  -- sort the pipes by coordinate, row-major.
  let h := BinaryHeap.ofList (PipeAtCoordinate.totalAndTransitiveLe area) pipesAtCoordinate
  -- Originally I had thought about doing another transformation of the path before sorting.
  -- The reason was that by folding the path's tiles west-to-east and trackings state if one is on a
  -- ┌┘, └┘, ┌┐ or └┐ wall would need handling of states like └| which are impossible.
  -- Proving that those states are impossible would be a lot of work, so a simpler representation
  -- of the path might have been in order.
  --
  -- Meanwhile I realized something though, that makes tracking the state while folding much simpler:
  -- All state that is needed is "Inside" and "Outside", and there is a very simple condition for
  -- state switches:
  -- If a tile has a connection north, it toggles between the states.
  -- It is unnecessary to track on which kind of wall one currently is, it is enough to look at the current tile.
  -- For instance:
  --
  --   └---┐   |
  --  oTxxxxiiiTo
  --
  --   ┌---┐  |  └--┐
  --  oxxxxxooTiiTxxxo
  --
  --   └---┘  ┌┘   |
  --  oTxxxTooxTiiiTo
  --
  --   |  └---┘   ┌┘
  --  oTiiTxxxTiiixTo
  --
  -- (here x denotes a tile that needs to be ignored, T is a tile that toggles state switch, i is inside, o is outside)
  --
  -- That way, even though there is no guarantee that there is no invalid state while folding over the
  -- sorted tiles, there is no need to handle such invalid state, as the rule "everything that connects north toggles"
  -- only depends on the current tile.
  -- I am happy with this, as it means I don't have to write partial functions, use optionals where they aren't needed,
  -- or return nonsensical values. It's still pretty bad, as the invariant that all lines end outside is not proven,
  -- but hey, I want to finish this at some point...
  -- Also, Area.ClosedPath implicitly gives this guarantee, it's just that I don't want to bother transforming it
  -- along with sorting the tiles...
  let result := h.fold WestEastFold.accumulate {state := .outside, accumulator := 0}
  return result.accumulator
where
  closedPathToPipesAtCoordinate : area.ClosedPath → List (PipeAtCoordinate area) := λcp ↦
    let rec worker : (area.PathsPart) → List (PipeAtCoordinate area) → (List (PipeAtCoordinate area)) := λpp o ↦
      match hs : pp.steps, pp.connected with
      | h :: [], connects_to_start =>
        let t := area[h]
        let ⟨(_ : t ≠ Tile.ground), (_ : t ≠ Tile.start)⟩ := Area.can_connect_to_imp_not_start_not_ground connects_to_start
        match t with
        | Tile.pipe p => ({coordinate := area.start, pipe := cp.start} :: {coordinate := h, pipe := p} :: o).reverse
      | s :: ss :: sss, ⟨s_connects_to_ss, rest_is_connected⟩ =>
        let t := area[s]
        let ⟨(_ : t ≠ Tile.ground), (_ : t ≠ Tile.start)⟩ := Area.can_connect_to_imp_not_start_not_ground s_connects_to_ss.left
        match t with
        | Tile.pipe p =>
          have : (ss :: sss).length < pp.steps.length := hs.substr $ (List.length_cons s (ss :: sss)).substr $ Nat.lt_add_one (ss :: sss).length
          worker { steps := ss :: sss, connected := rest_is_connected } $ {coordinate := s, pipe :=p} :: o
      termination_by x => x.steps.length
    worker cp.toPathsPart []
end ListMonad
------------------------------------------------------------------------------------------------------------
open DayPart
instance : Parse ⟨10, by simp⟩ (ι := Area) where
  parse := Except.mapError toString ∘ Area.parse

instance : Part ⟨10,_⟩ Parts.One (ι := Area) (ρ := NonEmptyList Nat) where
  run := NonEmptyList.ofList? ∘ part1

instance : Part ⟨10,_⟩ Parts.Two (ι := Area) (ρ := NonEmptyList Nat) where
  run := NonEmptyList.ofList? ∘ part2

------------------------------------------------------------------------------------------------------------
section Test

--def testData : String := "7-F7-
--.FJ|7
--SJLL7
--|F--J
--LJ.LJ"

--#eval (Area.parse testData)

-- Make this clearer
--   ┌┐
--  ┌┘|
-- ┌┘ └┐
-- |┌--┘
-- └┘

--#eval
--  let area := (Area.parse testData)
--  match area with
--  | .ok a => part1 a
--  | .error e => []
--
--
--#eval
--  let area := (Area.parse testData)
--  match area with
--  | .ok a => part2 a
--  | .error e => []

end Test
