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
  simp
  rw[List.getElem_append]

private theorem Area.ParseLine_leaves_start_if_some (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) {res : (Nat × Area.Raw)} (h₂ : (Area.parseLine previous pos line h₁) = Except.ok res) (h₃ : previous.start.isSome) : Fin.val <$> res.2.start = Fin.val <$> previous.start := by
  unfold Area.parseLine at h₂
  split at h₂
  case isTrue => simp at h₂; rw[←h₂]
  case isFalse h₄ =>
    split at h₂ ; exact h₂.rec
    case isFalse h₅ =>
      unfold bind Monad.toBind Except.instMonad Except.bind at h₂
      simp at h₂
      split at h₂; simp at h₂
      case h_2 d1 tile _ =>
        clear d1
        split at h₂; exact h₂.rec
        exact Area.ParseLine_leaves_start_if_some  { width := previous.width, height := previous.height, start := previous.start, fields := previous.fields.push tile } (pos + 1) (line.drop 1) h₁ h₂ h₃
termination_by previous.width - pos

private theorem Area.ParseLine_only_adds_to_fields (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) {res : (Nat × Area.Raw)} (h₂ : (Area.parseLine previous pos line h₁) = Except.ok res) (index : Fin (previous.fields.size)) : previous.fields[index.val]! = res.2.fields[index.val]! := by
  unfold Area.parseLine at h₂
  split at h₂
  case isTrue => simp at h₂; rw[←h₂]
  case isFalse h₃ =>
    split at h₂; exact h₂.rec
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
          split at h₂; exact h₂.rec
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
      case isTrue => exact h₄.rec
      case isFalse h₅ =>
        unfold bind Monad.toBind Except.instMonad Except.bind at h₄
        simp at h₄
        split at h₄; contradiction
        case h_2 d3 t ht =>
          clear d3
          split at h₄
          case isTrue h₆ =>
            split at h₄; exact h₄.rec
            case isFalse h₇ =>
              have h₈ : (previous.fields.push t)[previous.width * (previous.height - 1) + pos]! = t := by
                have := Array.get_push_eq previous.fields t
                simp[h₂, Array.getElem!_eq_getElem] at this
                assumption
              have : t = Tile.start := (beq_iff_eq t Tile.start).mp h₆
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

private theorem Area.PathHead.current_not_start_not_ground (pathHead : Area.PathHead area) : area[pathHead.current] ≠ Tile.ground ∧ area[pathHead.current] ≠ Tile.start :=
  have h₁ : area[pathHead.current] ≠ Tile.ground := by
    cases ht : (area[pathHead.current] == Tile.ground) <;> simp at ht
    case false => assumption
    case true =>
      cases pathHead.current_can_connect_to_previous <;> simp_all
  have h₂ : area[pathHead.current] ≠ Tile.start := by
    cases ht : (area[pathHead.current] == Tile.start) <;> simp at ht
    case false => assumption
    case true =>
      cases pathHead.current_can_connect_to_previous <;> simp_all
  And.intro h₁ h₂

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
end

private def Area.pathStarts (area : Area) : List (Area.PathHead area) :=
  [area.start.goNorth, area.start.goEast, area.start.goSouth, area.start.goWest]
  |> .filterMap λ c ↦ c.bind λc ↦
    if h: area.can_connect_to c area.start then
      some {
        current := c
        previous := area.start
        current_can_connect_to_previous := h
      }
    else
      none


def part1 (area : Area) : Option Nat := do
  let mut paths : List (Area.PathHead area) := area.pathStarts

  let mut steps := 1
  -- The condition in the while-loop is not needed. The program always terminates, as the
  -- search space (Coordinate width height) is finite, paths cannot cross, and all closed
  -- paths have an even number of steps. But I'm too lazy to prove this now, so, while-loop.
  -- It's ≤ instead of < here, because there might still be a solution for
  -- steps * 2 = area.width * area.height. Take this simple grid, for instance:
  --
  -- S7    01
  -- LJ    12
  while steps * 2 ≤ area.width * area.height do
    if noSolution paths then
      none
    if pathsMet paths then
      return steps
    steps := steps + 1
    paths := paths.filterMap (Functor.map Area.BidirPathHead.toPathHead ∘ area.nextPathStep)
  none
where
  pathsMet := λ (ps : List $ Area.PathHead area) ↦ match ps with
  | [] => false
  | p :: ps => ps.any λh ↦ h.current = p.current || pathsMet ps
  noSolution := λ (ps : List $ Area.PathHead area) ↦ match ps with
  | [] => true
  | _ :: [] => true
  | _ => false

------------------------------------------------------------------------------------------------------------

private def coordinateSorter (a b : Coordinate w h) : Bool :=
  a.y < b.y ∨ (a.y = b.y ∧ a.x ≤ b.x)

private theorem coordiateSorter_transitive {w h : Nat} : BinaryHeap.transitive_le (coordinateSorter (w := w) (h := h)) := by
  unfold BinaryHeap.transitive_le
  intros a b c
  unfold coordinateSorter
  simp
  omega

private theorem coordinateSorter_total {w h : Nat} : BinaryHeap.total_le (coordinateSorter (w := w) (h := h)) := by
  unfold BinaryHeap.total_le
  intros a b
  unfold coordinateSorter
  simp
  omega

def part2 (area : Area) : Option Nat :=
  sorry


------------------------------------------------------------------------------------------------------------
open DayPart
instance : Parse ⟨10, by simp⟩ (ι := Area) where
  parse := Except.mapError toString ∘ Area.parse

instance : Part ⟨10,_⟩ Parts.One (ι := Area) (ρ := Nat) where
  run := part1

section Test
------------------------------------------------------------------------------------------------------------
def testData : String := "7-F7-
.FJ|7
SJLL7
|F--J
LJ.LJ"

#eval
  let area := (Area.parse testData)
  match area with
  | .ok a => part1 a
  | .error e => none

end Test
