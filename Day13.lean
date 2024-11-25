import «Common»

namespace Day13

------------------------------------------------------------------------------------

inductive Tile
| Sand : Tile
| Rock : Tile
deriving Repr, BEq

instance : LawfulBEq Tile where
  rfl := λ{a} ↦ by cases a <;> decide
  eq_of_beq := by intros a b; cases a <;> cases b <;> simp <;> decide

instance: ToString Tile where
toString := λ
| Tile.Sand => "."
| Tile.Rock => "#"

structure ParseCharError where
  unexpectedCharacter : Char

instance : ToString ParseCharError where
toString := λc ↦ s!"Unexpected Character '{c.unexpectedCharacter}', expected '.' or '#'."

private def Tile.ofChar? : Char → Except ParseCharError Tile
| '.' => pure Tile.Sand
| '#' => pure Tile.Rock
| c => throw {unexpectedCharacter := c}

abbrev ParsedInput := List $ Parsing.RectangularGrid Tile

abbrev ParseInputError := Parsing.RectangularGrid.ParseError ParseCharError

def parse (input : String) : Except ParseInputError ParsedInput :=
  let blocks := input.toSubstring.splitOn "\n\n"
  if blocks.isEmpty then
    throw Parsing.RectangularGrid.ParseError.NoInput
  else
    blocks.mapM $ Parsing.RectangularGrid.ofSubstring Tile.ofChar?

-- The things I do just to be able to #eval the parse result...
theorem parse_not_empty_list {input : String} :
match parse input with
| Except.ok r => r.length > 0
| Except.error _ => True := by
  unfold parse
  simp only
  cases h₁ : (input.toSubstring.splitOn "\n\n").isEmpty
  <;> simp only [Bool.false_eq_true, ↓reduceIte, gt_iff_lt]
  rw[←List.mapM'_eq_mapM]
  unfold List.mapM'
  have h₂ : (input.toSubstring.splitOn "\n\n") ≠ [] := List.isEmpty_eq_false.mp h₁
  cases h₃ : input.toSubstring.splitOn "\n\n"
  case false.nil => contradiction
  case false.cons b bs =>
    simp only [bind_pure_comp]
    cases Parsing.RectangularGrid.ofSubstring Day13.Tile.ofChar? b
    case error e => exact True.intro
    case ok t =>
      cases List.mapM' (Parsing.RectangularGrid.ofSubstring Day13.Tile.ofChar?) bs
      case error e => exact True.intro
      case ok ts =>
        have h₄ := List.length_cons t ts
        unfold bind Monad.toBind Except.instMonad
        simp only [Except.bind, Except.map, h₄, Nat.zero_lt_succ]

------------------------------------------------------------------------------------

private abbrev Grid := Parsing.RectangularGrid Tile

private inductive LookDirection (grid : Grid)
| Horizontal
| Vertical

private def LookDirection.width : (LookDirection grid) → Nat
| Horizontal => grid.width
| Vertical => grid.height

private def LookDirection.height : (LookDirection grid) → Nat
| Horizontal => grid.height
| Vertical => grid.width

private structure LookDirection.Coordinate (lookDirection : LookDirection grid) where
  x : Fin lookDirection.width
  y : Fin lookDirection.height

private def LookDirection.Coordinate.toGridCoordinate {grid : Grid} {lookDirection : LookDirection grid} (c : lookDirection.Coordinate) : grid.Coordinate :=
  match lookDirection with
  | Horizontal => {x := c.x, y := c.y}
  | Vertical => {y := c.x, x := c.y}

private def LookDirection.get {grid : Grid} {lookDirection : LookDirection grid} (coordinate : LookDirection.Coordinate lookDirection) : Tile :=
  grid[coordinate.toGridCoordinate]

private def getCoordinateOffset {ld : LookDirection grid} (mirror : Fin (ld.width - 1)) (offset : Nat) : Option (Fin ld.width × Fin ld.width) :=
  if h : offset <= mirror ∧ mirror + offset + 1 < ld.width then
    some (
      ⟨mirror - offset, Nat.lt_of_le_of_lt (Nat.sub_le mirror offset) (Nat.lt_of_pred_lt mirror.isLt)⟩,
      ⟨mirror + offset + 1, h.right⟩)
  else
    none

private theorem LookDirection.not_empty (lookDirection : LookDirection grid) : lookDirection.width > 0 ∧ lookDirection.height > 0 := by
  unfold width height
  cases lookDirection <;> simp only[grid.not_empty, and_true]

private def canBeMirror (lookDirection : LookDirection grid) (index : Fin (lookDirection.width - 1)) : Bool :=
  areRowsMirrored ⟨lookDirection.height.pred, Nat.pred_lt $ Nat.ne_zero_iff_zero_lt.mpr lookDirection.not_empty.right⟩
where
  areRowsMirrored : Fin (lookDirection.height) → Bool := λ r ↦
    let isCurrentRowMirrored := isRowMirrored r 0
    match r with
    | ⟨0,_⟩ => isCurrentRowMirrored
    | ⟨rp + 1, h₁⟩ =>
      isCurrentRowMirrored && areRowsMirrored ⟨rp, Nat.lt_of_succ_lt h₁⟩
  isRowMirrored : Fin (lookDirection.height) → Nat → Bool := λr o ↦
    match h : getCoordinateOffset index o with
    | none => true --always consider outside as mirrored.
    | some (i₁, i₂) =>
      let c₁ : lookDirection.Coordinate := {x := i₁, y := r}
      let c₂ : lookDirection.Coordinate := {x := i₂, y := r}
      lookDirection.get c₁ == lookDirection.get c₂ && isRowMirrored r (o+1)
    termination_by _ o => lookDirection.width - (index + o + 1)
    decreasing_by
      unfold getCoordinateOffset at h
      split at h
      case isFalse => contradiction
      case isTrue h₁ => omega

private def findMirrorPlanes (lookDirection : LookDirection grid) : List (Fin lookDirection.width.pred) :=
  match h : lookDirection.width with
  | 0 => absurd h $ Nat.ne_zero_iff_zero_lt.mpr lookDirection.not_empty.left
  | 1 => []
  | wp + 2 =>
    have h : wp+2 = lookDirection.width := h.symm
    have : wp < lookDirection.width.pred := Nat.pred_lt_pred (Nat.add_one_ne_zero _) $ Nat.add_one_le_iff.mp (Nat.le_of_eq h)
    h▸(findMirrorPlanes_aux ⟨wp,this⟩ [])
where
  findMirrorPlanes_aux (r : Fin lookDirection.width.pred) (p : List (Fin lookDirection.width.pred)) : List (Fin lookDirection.width.pred) :=
    let p := if canBeMirror lookDirection r then
      r :: p
    else
      p
    match r with
    | ⟨0,_⟩ => p
    | ⟨rp+1,isLt⟩ => findMirrorPlanes_aux ⟨rp, Nat.lt_of_succ_lt isLt⟩ p

def part1 (input : ParsedInput) : Nat :=
  let horizontalScores := input.foldl (λs g ↦
    (findMirrorPlanes (LookDirection.Horizontal : LookDirection g)).foldl (·+·.val+1) s) 0
  let verticalScores := input.foldl (λs g ↦
    (findMirrorPlanes (LookDirection.Vertical : LookDirection g)).foldl (λa b ↦ a+(b.val+1)*100) s) 0
  horizontalScores + verticalScores


------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨13, by simp⟩ (ι := ParsedInput) where
  parse := Except.mapError toString ∘ parse

instance : Part ⟨13,_⟩ Parts.One (ι := ParsedInput) (ρ := Nat) where
  run := some ∘ part1
------------------------------------------------------------------------------------

private def testInput := "#.##..##.
..#.##.#.
##......#
##......#
..#.##.#.
..##..##.
#.#.##.#.

#...##..#
#....#..#
..##..###
#####.##.
#####.##.
..##..###
#....#..#"

#eval parse testInput

#eval match h : parse testInput with
| Except.error _ => none
| Except.ok l =>
  have h₁ : 0 < l.length := by
    have h₂ := parse_not_empty_list (input := testInput)
    simp only[h] at h₂
    exact h₂
  let t := l[0]
  let LD := (LookDirection t)
  let ld : LD := LookDirection.Horizontal
  let midx := 0
  if h₂ : midx < ld.width - 1 then
    ToString.toString <$> getCoordinateOffset (ld := ld) ⟨midx, h₂⟩ 1
  else
    none

#eval match h : parse testInput with
| Except.error _ => []
| Except.ok l =>
  have h₁ : 0 < l.length := by
    have h₂ := parse_not_empty_list (input := testInput)
    simp only[h] at h₂
    exact h₂
  let t := l[0]
  let LD := (LookDirection t)
  let ld : LD := LookDirection.Horizontal
  ToString.toString <$> findMirrorPlanes ld

#eval match parse testInput with
| Except.error _ => 0
| Except.ok l => part1 l
