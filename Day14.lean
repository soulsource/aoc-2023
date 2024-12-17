import «Common»
import Std.Data.HashMap
import Std.Data.HashSet

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
  unfold moveTileNorth
  constructor <;> split <;> rfl

private def moveAllTilesNorth (controlPanel : ControlPanel) : ControlPanel := Id.run do
  let mut result : ((c : ControlPanel) ×' (c.width = controlPanel.width ∧ c.height = controlPanel.height)) := ⟨controlPanel, ⟨rfl,rfl⟩⟩
  for hr : row in [:controlPanel.height] do
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

/-- Finds the westmost free space reachable from start. Does not look at start. -/
private def findWestmostFreeTile {controlPanel : ControlPanel} (start : controlPanel.Coordinate) : controlPanel.Coordinate :=
  if start.x > ⟨0,controlPanel.not_empty.left⟩ then
    let westNeighbour := { start with x := ⟨start.x - 1,Nat.lt_imp_pred_lt start.x.isLt⟩ }
    match controlPanel[westNeighbour] with
    | Tile.Space => findWestmostFreeTile westNeighbour
    | Tile.Round | Tile.Cube => start
  else
    start
termination_by start.x

/-- Finds the southmost free space reachable from start. Does not look at start. -/
private def findSouthmostFreeTile {controlPanel : ControlPanel} (start : controlPanel.Coordinate) : controlPanel.Coordinate :=
  if h : start.y.val.succ < controlPanel.height then
    let southNeighbour := { start with y := ⟨start.y.val.succ,h⟩ }
    match controlPanel[southNeighbour] with
    | Tile.Space => findSouthmostFreeTile southNeighbour
    | Tile.Round | Tile.Cube => start
  else
    start

/-- Finds the eastmost free space reachable from start. Does not look at start. -/
private def findEastmostFreeTile {controlPanel : ControlPanel} (start : controlPanel.Coordinate) : controlPanel.Coordinate :=
  if h : start.x.val.succ < controlPanel.width then
    let eastNeighbour := { start with x := ⟨start.x.val.succ,h⟩ }
    match controlPanel[eastNeighbour] with
    | Tile.Space => findEastmostFreeTile eastNeighbour
    | Tile.Round | Tile.Cube => start
  else
    start

private def moveTileInDirection (direction : {c : ControlPanel} → c.Coordinate → c.Coordinate) {controlPanel : ControlPanel} (position : controlPanel.Coordinate) : ControlPanel :=
   match controlPanel[position] with
  | Tile.Space | Tile.Cube => controlPanel
  | Tile.Round =>
    let intermediate := controlPanel.set position Tile.Space
    let positionInIntermediate : intermediate.Coordinate := {x := position.x, y := position.y} -- how? well, I won't complain
    let northMost := direction positionInIntermediate
    intermediate.set northMost Tile.Round

private theorem moveTileInDirection_same_size (direction : {c : ControlPanel} → c.Coordinate → c.Coordinate) {controlPanel : ControlPanel} (position : controlPanel.Coordinate) : (moveTileInDirection direction position).width = controlPanel.width ∧ (moveTileInDirection direction position).height = controlPanel.height := by
  unfold moveTileInDirection
  constructor <;> split <;> rfl

private def moveTileWest : {controlPanel : ControlPanel} → controlPanel.Coordinate → ControlPanel :=
  moveTileInDirection findWestmostFreeTile
private def moveTileSouth : {controlPanel : ControlPanel} → controlPanel.Coordinate → ControlPanel :=
  moveTileInDirection findSouthmostFreeTile
private def moveTileEast : {controlPanel : ControlPanel} → controlPanel.Coordinate → ControlPanel :=
  moveTileInDirection findEastmostFreeTile

private theorem moveTileWest_same_size : {controlPanel : ControlPanel} → (position : controlPanel.Coordinate) → (moveTileWest position).width = controlPanel.width ∧ (moveTileWest position).height = controlPanel.height :=
  moveTileInDirection_same_size findWestmostFreeTile
private theorem moveTileEast_same_size : {controlPanel : ControlPanel} → (position : controlPanel.Coordinate) → (moveTileEast position).width = controlPanel.width ∧ (moveTileEast position).height = controlPanel.height :=
  moveTileInDirection_same_size findEastmostFreeTile
private theorem moveTileSouth_same_size : {controlPanel : ControlPanel} → (position : controlPanel.Coordinate) → (moveTileSouth position).width = controlPanel.width ∧ (moveTileSouth position).height = controlPanel.height :=
  moveTileInDirection_same_size findSouthmostFreeTile

private def moveAllTilesWest (controlPanel : ControlPanel) : ControlPanel := Id.run do
  let mut result : ((c : ControlPanel) ×' (c.width = controlPanel.width ∧ c.height = controlPanel.height)) := ⟨controlPanel, ⟨rfl,rfl⟩⟩
  for hr : row in [:controlPanel.height] do
    for hc : column in [:controlPanel.width] do
      let x : Fin result.fst.width := Fin.cast result.snd.left.symm ⟨column,hc.upper⟩
      let y : Fin result.fst.height := Fin.cast result.snd.right.symm ⟨row,hr.upper⟩
      let coordinate : result.fst.Coordinate := {x, y}
      have : (moveTileWest coordinate).width = controlPanel.width ∧ (moveTileWest coordinate).height = controlPanel.height :=
        (moveTileWest_same_size coordinate).right.substr $ (moveTileWest_same_size coordinate).left.substr result.snd
      result := ⟨moveTileWest coordinate, this⟩
  result.fst

private def moveAllTilesSouth (controlPanel : ControlPanel) : ControlPanel := Id.run do
  let mut result : ((c : ControlPanel) ×' (c.width = controlPanel.width ∧ c.height = controlPanel.height)) := ⟨controlPanel, ⟨rfl,rfl⟩⟩
  for row in [:controlPanel.height] do
    for hc : column in [:controlPanel.width] do
      let x : Fin result.fst.width := Fin.cast result.snd.left.symm ⟨column,hc.upper⟩
      have : controlPanel.height - 1 - row < controlPanel.height :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pred_lt (Nat.pos_iff_ne_zero.mp controlPanel.not_empty.right))
      let y : Fin result.fst.height := Fin.cast result.snd.right.symm ⟨controlPanel.height - 1 - row,this⟩
      let coordinate : result.fst.Coordinate := {x, y}
      have : (moveTileSouth coordinate).width = controlPanel.width ∧ (moveTileSouth coordinate).height = controlPanel.height :=
        (moveTileSouth_same_size coordinate).right.substr $ (moveTileSouth_same_size coordinate).left.substr result.snd
      result := ⟨moveTileSouth coordinate, this⟩
  result.fst

private def moveAllTilesEast (controlPanel : ControlPanel) : ControlPanel := Id.run do
  let mut result : ((c : ControlPanel) ×' (c.width = controlPanel.width ∧ c.height = controlPanel.height)) := ⟨controlPanel, ⟨rfl,rfl⟩⟩
  for hr : row in [:controlPanel.height] do
    for column in [:controlPanel.width] do
      have : controlPanel.width - 1 - column < controlPanel.width :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pred_lt (Nat.pos_iff_ne_zero.mp controlPanel.not_empty.left))
      let x : Fin result.fst.width := Fin.cast result.snd.left.symm ⟨controlPanel.width - 1 - column,this⟩
      let y : Fin result.fst.height := Fin.cast result.snd.right.symm ⟨row,hr.upper⟩
      let coordinate : result.fst.Coordinate := {x, y}
      have : (moveTileEast coordinate).width = controlPanel.width ∧ (moveTileEast coordinate).height = controlPanel.height :=
        (moveTileEast_same_size coordinate).right.substr $ (moveTileEast_same_size coordinate).left.substr result.snd
      result := ⟨moveTileEast coordinate, this⟩
  result.fst

private def cycle (controlPanel : ControlPanel) : ControlPanel :=
  let n := moveAllTilesNorth controlPanel
  let w := moveAllTilesWest n
  let s := moveAllTilesSouth w
  moveAllTilesEast s

private def compareControlPanels (a b : ControlPanel) : Bool :=
  if h₁ : a.width = b.width ∧ a.height = b.height then
    Id.run do
    for hr : row in [:a.height] do
      for hc : column in [:a.width] do
        let ca : a.Coordinate := {x := ⟨column, hc.upper⟩, y := ⟨row, hr.upper⟩}
        let cb : b.Coordinate := {x := ⟨column, h₁.left.subst hc.upper⟩, y := ⟨row, h₁.right.subst hr.upper⟩}
        if !(a[ca] == b[cb]) then
          return false
    return true
  else
    false

/-- (Bad) Hash-Function for ControlPanel. It's good enough for this riddle, but that's about it. -/
private def hashControlPanel (p : ControlPanel) : UInt64 := Id.run do
  let mut hash : UInt64 := mixHash ⟨Fin.ofNat' UInt64.size p.width⟩ ⟨Fin.ofNat' UInt64.size p.height⟩
  for hi : index in [:p.elements.size] do
    match p.elements[index] with
    | Tile.Round => hash := mixHash hash ⟨Fin.ofNat' UInt64.size index⟩
    | Tile.Cube => hash := mixHash hash ⟨Fin.ofNat' UInt64.size (index + p.elements.size)⟩
    | Tile.Space => continue
  hash

private instance : BEq ControlPanel where
beq := compareControlPanels

private instance : Hashable ControlPanel where
hash := hashControlPanel

structure Part2Memory where
  seenHashes : Std.HashSet UInt64 -- If this becomes too large, it could be replaced by a Bloom Filter
  recordedPanels : Std.HashMap ControlPanel Nat
deriving Inhabited

/-- Helper for runCycles. No point in keeping a memory once we have found a cycle. -/
private def runCycles_bruteForce (cycleCount : Nat) (controlPanel : ControlPanel) : ControlPanel :=
  match cycleCount with
  | 0 => controlPanel
  | p+1 =>
    let r := cycle controlPanel
    runCycles_bruteForce p r

private def runCycles (cycleCount : Nat) (controlPanel : ControlPanel) : StateM (Part2Memory) ControlPanel :=
  match cycleCount with
  | 0 => pure controlPanel
  | p+1 => do
    let r := cycle controlPanel
    let s ← get
    let (seen, seenHashes) := s.seenHashes.containsThenInsert (hash r)
    set {s with seenHashes}
    if seen then
      let s ← get
      let (maybePreviousCount, recordedPanels) := s.recordedPanels.getThenInsertIfNew? r p
      set {s with recordedPanels}
      if let some previousCount := maybePreviousCount then
        let period := previousCount - p
        let remaining := p % period
        pure $ runCycles_bruteForce remaining r
      else
        runCycles p r
    else
      runCycles p r

def part2 (input : ControlPanel) : Nat :=
  let r := StateT.run' (runCycles 1000000000 input) Inhabited.default
  weightOnNorthSupport r

------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨14, by simp⟩ (ι := ControlPanel) where
  parse := Except.mapError toString ∘ parse

instance : Part ⟨14,_⟩ Parts.One (ι := ControlPanel) (ρ := Nat) where
  run := some ∘ part1

instance : Part ⟨14,_⟩ Parts.Two (ι := ControlPanel) (ρ := Nat) where
  run := some ∘ part2

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

#eval part2 <$> parse testInput
