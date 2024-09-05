import «Common»

namespace Day10

structure Coordinate (width : Nat) (height : Nat) where
  x : Fin width
  y : Fin height

def Coordinate.toIndex {w h : Nat} (c : Coordinate w h) : Fin (w*h) :=
  Fin.mk (c.x.val * c.y.val) (Nat.mul_lt_mul_of_lt_of_lt c.x.isLt c.y.isLt)

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

inductive Pipe
| NS : Pipe
| WE : Pipe
| NE : Pipe
| ES : Pipe
| SW : Pipe
| WN : Pipe
deriving BEq

inductive Tile
| pipe : Pipe → Tile
| ground : Tile
| start : Tile
deriving BEq

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

inductive Area.ParseError
| NoInput
| UnexpectedCharacter
| NoStart
| MoreThanOneStart
| NotRectangular

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
    let tile ← Option.toExcept Area.ParseError.UnexpectedCharacter $ parseCharacter line.front
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
where parseCharacter : Char → Option Tile := λ c ↦ match c with
  | '|' => some $ Tile.pipe Pipe.NS
  | '-' => some $ Tile.pipe Pipe.WE
  | 'L' => some $ Tile.pipe Pipe.NE
  | 'J' => some $ Tile.pipe Pipe.WN
  | '7' => some $ Tile.pipe Pipe.SW
  | 'F' => some $ Tile.pipe Pipe.ES
  | 'S' => some Tile.start
  | '.' => some Tile.ground
  | _ => none

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
  let lines := input.splitTrim (· == '\n')
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
      case none => rw[←h₃] at h₂; contradiction
      case some =>
        split at h₃
        case h_1 => rw[←h₃] at h₂; contradiction
        case h_2 d1 h₅ char₂ d2 char h₆ =>
        simp[Except.pure] at h₆
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
      case none => rw[←h₃] at h₂; contradiction
      case some =>
        split at h₃
        case h_1 => rw[←h₃] at h₂; contradiction
        case h_2 d1 h₅ char₂ d2 char h₆ =>
        simp[Except.pure] at h₆
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

private theorem Option.get_unfold {α : Type u} {v : α} : (some v).get (rfl) = v := rfl

private theorem Option.get_unfold' {α : Type u} {o : Option α} {v : α} (h₁ : o = some v) (h₂ : o.isSome) : o.get h₂ = v := by
  simp[h₁]

private theorem Area.ParseLine_leaves_start_if_some (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) {res : (Nat × Area.Raw)} (h₂ : (Area.parseLine previous pos line h₁) = Except.ok res) (h₃ : previous.start.isSome) : Fin.val <$> res.2.start = Fin.val <$> previous.start := by
  sorry

private theorem Area.ParseLine_only_adds_to_fields (previous : Area.Raw) (pos : Nat) (line : Substring) (h₁ : previous.height > 0) {res : (Nat × Area.Raw)} (h₂ : (Area.parseLine previous pos line h₁) = Except.ok res) (index : Fin (previous.fields.size)) : previous.fields[index.val]! = res.2.fields[index.val]! := by
  sorry

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
                sorry
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
        have : 0 < (String.splitTrim (fun x => x == '\n') input).length := by simp at hs; unfold List.isEmpty at hs; split at hs; contradiction; rename_i hx; simp[hx]
        have := Area.ParseLines_start_position { width := (String.splitTrim (fun x => x == '\n') input)[0].length, height := 0, start := none, fields := #[] } (String.splitTrim (fun x => x == '\n') input) (hr.substr h₁)
        simp at this
        subst r
        split at this
        case h_2 hix => exact absurd (Option.isSome_iff_exists.mpr ⟨index,hi⟩) (Option.not_isSome_iff_eq_none.mpr hix)
        case h_1 index₂ hi₂=>
          have := hi.subst (motive :=λx↦x = some index₂) hi₂
          simp at this
          subst index₂
          exact this

private theorem Array.getElem!_eq_getElem {α : Type u} [Inhabited α] {a : Array α} {index : Nat} (h : index < a.size ): a[index] = a[index]! := by
  unfold getElem getElem! instGetElem?OfGetElemOfDecidable Array.instGetElemNatLtSize decidableGetElem?
  simp
  split
  <;> rename_i blah
  <;> simp[h] at blah
  assumption

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
