import «Common»

namespace Day14

------------------------------------------------------------------------------------

inductive Tile
| Space
| Cube
| Round
deriving Repr, BEq

instance : LawfulBEq Tile where
  rfl := λ{a} ↦ by cases a <;> decide
  eq_of_beq := by intros a b; cases a <;> cases b <;> simp <;> decide

instance: ToString Tile where
toString := λ
| Tile.Space => "."
| Tile.Cube => "#"
| Tile.Round => "O"

structure ParseCharError where
unexpectedCharacter : Char

instance : ToString ParseCharError where
toString := λc ↦ s!"Unexpected Character '{c.unexpectedCharacter}', expected '.', '#', or 'O'."

private def Tile.ofChar? : Char → Except ParseCharError Tile
| '.' => pure Tile.Space
| '#' => pure Tile.Cube
| 'O' => pure Tile.Round
| c => throw {unexpectedCharacter := c}

abbrev ControlPanel := Parsing.RectangularGrid Tile

abbrev ParseInputError := Parsing.RectangularGrid.ParseError ParseCharError

def parse : String → Except ParseInputError ControlPanel :=
  Parsing.RectangularGrid.ofSubstring Tile.ofChar? ∘ String.toSubstring

------------------------------------------------------------------------------------

/-
there's probably a better way, but I'm too lazy, so I'll just move them row-by-row.
pseudocode
for(row)
  for(column)
    if(tile == Round)
      moveTileAsFarNorthAsPossible
-/

/-- Finds the northmost free space reachable from start. Does not look at start. -/
private def findNorthmostFreeTile {controlPanel : ControlPanel} (start : controlPanel.Coordinate) : controlPanel.Coordinate :=
  if start.y > ⟨0,controlPanel.not_empty.right⟩ then
    let northNeighbour := { start with y := ⟨start.y - 1,Nat.lt_imp_pred_lt start.y.isLt⟩ }
    match controlPanel[northNeighbour] with
    | Tile.Space => findNorthmostFreeTile northNeighbour
    | Tile.Round | Tile.Cube => start
  else
    start
termination_by start.y

private def moveTileNorth {controlPanel : ControlPanel} (position : controlPanel.Coordinate) : ControlPanel :=
  match controlPanel[position] with
  | Tile.Space | Tile.Cube => controlPanel
  | Tile.Round =>
    let intermediate := controlPanel.set position Tile.Space
    let positionInIntermediate : intermediate.Coordinate := {x := position.x, y := position.y} -- how? well, I won't complain
    let northMost := findNorthmostFreeTile positionInIntermediate
    intermediate.set northMost Tile.Round

private theorem moveTileNorth_same_size {controlPanel : ControlPanel} (position : controlPanel.Coordinate) : (moveTileNorth position).width = controlPanel.width ∧ (moveTileNorth position).height = controlPanel.height := by
  constructor
  all_goals
    unfold moveTileNorth
    match controlPanel[position] with
    | Tile.Space | Tile.Cube => trivial
    | Tile.Round =>
      simp only[Parsing.RectangularGrid.set_same_size]

/-
-- Old solution, without do-notation. Proven to terminate, but needs a lot more code...

/- had to move this to top level function to be able to prove stuff with it... "Declaration contains metavariables" -/
private def moveAllTilesNorth_handleColumns (cp : ControlPanel) (row : Fin cp.height) (column : Fin cp.width) : ControlPanel :=
    let intermediate := moveTileNorth {x := column, y := row : cp.Coordinate}
    let nextIndex := column.val + 1
    if h : nextIndex < intermediate.width then
      have h₁ : intermediate.height = cp.height := (moveTileNorth_same_size {x := column, y := row : cp.Coordinate}).right
      moveAllTilesNorth_handleColumns intermediate (h₁▸row) ⟨nextIndex,h⟩
    else
      intermediate
  termination_by cp.width - column
  decreasing_by
    have h₂ := (moveTileNorth_same_size { x := column, y := row }).left
    rw[h₂] at h ⊢
    exact Nat.sub_lt_of_gt (Nat.le_of_lt h) (Nat.lt_succ.mpr $ Nat.le_refl _)

private theorem moveAllTilesNorth_handleColumns_same_height (cp : ControlPanel) (row : Fin cp.height) (column : Fin cp.width) : (moveAllTilesNorth_handleColumns cp row column).height = cp.height := by
  unfold moveAllTilesNorth_handleColumns
  simp
  have h₂ := (moveTileNorth_same_size { x := column, y := row }).right
  split
  case isFalse => exact h₂
  case isTrue =>
    have := moveAllTilesNorth_handleColumns_same_height (Day14.moveTileNorth { x := column, y := row }) (h₂ ▸ row) ⟨↑column + 1, by assumption⟩
    simp[h₂] at this
    assumption
  termination_by cp.width - column
  decreasing_by
    have h₂ := (moveTileNorth_same_size { x := column, y := row }).left
    rename_i h
    rw[h₂] at h ⊢
    exact Nat.sub_lt_of_gt (Nat.le_of_lt h) (Nat.lt_succ.mpr $ Nat.le_refl _)

private def moveAllTilesNorth (controlPanel : ControlPanel) : ControlPanel :=
  handleRows (controlPanel) ⟨0,controlPanel.not_empty.right⟩
where
  handleRows (cp : ControlPanel) (row : Fin cp.height) : ControlPanel :=
    let intermediate := moveAllTilesNorth_handleColumns cp row ⟨0,cp.not_empty.left⟩
    let nextIndex := row.val + 1
    if h : nextIndex < intermediate.height then
      handleRows intermediate ⟨nextIndex, h⟩
    else
      intermediate
    termination_by cp.height - row
    decreasing_by
      have h₁ : intermediate.height = cp.height :=
        moveAllTilesNorth_handleColumns_same_height cp row ⟨0,_⟩
      rw[h₁] at h ⊢
      exact Nat.sub_lt_of_gt (Nat.le_of_lt h) (Nat.lt_succ.mpr $ Nat.le_refl _)
-/

private def moveAllTilesNorth (controlPanel : ControlPanel) : ControlPanel := Id.run do
  let mut result : ((c : ControlPanel) ×' (c.width = controlPanel.width ∧ c.height = controlPanel.height)) := ⟨controlPanel, ⟨rfl,rfl⟩⟩
  for hr :row in [:controlPanel.height] do
    for hc : column in [:controlPanel.width] do
      let x : Fin result.fst.width := Fin.cast result.snd.left.symm ⟨column,hc.upper⟩
      let y : Fin result.fst.height := Fin.cast result.snd.right.symm ⟨row,hr.upper⟩
      let coordinate : result.fst.Coordinate := {x, y}
      have : (moveTileNorth coordinate).width = controlPanel.width ∧ (moveTileNorth coordinate).height = controlPanel.height :=
        (moveTileNorth_same_size coordinate).right.substr $ (moveTileNorth_same_size coordinate).left.substr result.snd
      result := ⟨moveTileNorth coordinate, this⟩
  result.fst

private def weightOnNorthSupport (controlPanel : ControlPanel) : Nat := Id.run do
  let mut score := 0
  for hr :row in [:controlPanel.height] do
    for hc : column in [:controlPanel.width] do
      let coordinate := {x := ⟨column,hc.upper⟩, y := ⟨row,hr.upper⟩ : controlPanel.Coordinate}
      if controlPanel[coordinate] == Tile.Round then
        score := score + (controlPanel.height - row)
  score

def part1 : (input : ControlPanel) → Nat := weightOnNorthSupport ∘ moveAllTilesNorth

------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨14, by simp⟩ (ι := ControlPanel) where
  parse := Except.mapError toString ∘ parse

instance : Part ⟨14,_⟩ Parts.One (ι := ControlPanel) (ρ := Nat) where
  run := some ∘ part1

------------------------------------------------------------------------------------

private def testInput := "O....#....
O.OO#....#
.....##...
OO.#O....O
.O.....O#.
O.#..O.#.#
..O..#O..O
.......O..
#....###..
#OO..#...."

#eval parse testInput

#eval (weightOnNorthSupport ∘ moveAllTilesNorth) <$> parse testInput
