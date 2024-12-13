import Common

namespace Day16

------------------------------------------------------------------------------------

inductive MirrorDirection
| BottomLeftTopRight
| BottomRightTopLeft

inductive SplitterDirection
| Horizontal
| Vertical

inductive OpticsElement where
| EmptySpace : OpticsElement
| Mirror : MirrorDirection → OpticsElement
| Splitter : SplitterDirection → OpticsElement

inductive ParseCharError
| InvalidCharacter : Char → ParseCharError

instance : ToString ParseCharError where
toString := λ
| ParseCharError.InvalidCharacter c => s!"Cannot parse character {c}, expected '.', '/', '\\', '|', or '-'."

instance : ToString OpticsElement where
toString := λ
| OpticsElement.EmptySpace => "."
| OpticsElement.Mirror MirrorDirection.BottomLeftTopRight => "/"
| OpticsElement.Mirror MirrorDirection.BottomRightTopLeft => "\\"
| OpticsElement.Splitter SplitterDirection.Horizontal => "-"
| OpticsElement.Splitter SplitterDirection.Vertical => "|"

private def parseCharacter : Char → Except ParseCharError OpticsElement
| '.' => Except.ok $ OpticsElement.EmptySpace
| '/' => Except.ok $ OpticsElement.Mirror MirrorDirection.BottomLeftTopRight
| '\\' => Except.ok $ OpticsElement.Mirror MirrorDirection.BottomRightTopLeft
| '-' => Except.ok $ OpticsElement.Splitter SplitterDirection.Horizontal
| '|' => Except.ok $ OpticsElement.Splitter SplitterDirection.Vertical
| c => Except.error $ ParseCharError.InvalidCharacter c

private abbrev OpticsTable := Parsing.RectangularGrid OpticsElement

open Parsing in
def parse : (input : String) → Except (RectangularGrid.ParseError ParseCharError) OpticsTable :=
  RectangularGrid.ofString parseCharacter


------------------------------------------------------------------------------------

private inductive EnterDirection
| FromTop
| FromLeft
| FromRight
| FromBottom

private inductive ExitDirection
| ToTop
| ToLeft
| ToRight
| ToBottom

private def OpticsElement.outputDirections : OpticsElement → EnterDirection → List ExitDirection
| OpticsElement.EmptySpace, EnterDirection.FromTop => [ExitDirection.ToBottom]
| OpticsElement.EmptySpace, EnterDirection.FromLeft => [ExitDirection.ToRight]
| OpticsElement.EmptySpace, EnterDirection.FromBottom => [ExitDirection.ToTop]
| OpticsElement.EmptySpace, EnterDirection.FromRight => [ExitDirection.ToLeft]
| OpticsElement.Mirror MirrorDirection.BottomLeftTopRight, EnterDirection.FromTop => [ExitDirection.ToLeft]
| OpticsElement.Mirror MirrorDirection.BottomLeftTopRight, EnterDirection.FromLeft => [ExitDirection.ToTop]
| OpticsElement.Mirror MirrorDirection.BottomLeftTopRight, EnterDirection.FromBottom => [ExitDirection.ToRight]
| OpticsElement.Mirror MirrorDirection.BottomLeftTopRight, EnterDirection.FromRight => [ExitDirection.ToBottom]
| OpticsElement.Mirror MirrorDirection.BottomRightTopLeft, EnterDirection.FromTop => [ExitDirection.ToRight]
| OpticsElement.Mirror MirrorDirection.BottomRightTopLeft, EnterDirection.FromLeft => [ExitDirection.ToBottom]
| OpticsElement.Mirror MirrorDirection.BottomRightTopLeft, EnterDirection.FromBottom => [ExitDirection.ToLeft]
| OpticsElement.Mirror MirrorDirection.BottomRightTopLeft, EnterDirection.FromRight => [ExitDirection.ToTop]
| OpticsElement.Splitter SplitterDirection.Horizontal, EnterDirection.FromTop => [ExitDirection.ToLeft, ExitDirection.ToRight]
| OpticsElement.Splitter SplitterDirection.Horizontal, EnterDirection.FromLeft => [ExitDirection.ToRight]
| OpticsElement.Splitter SplitterDirection.Horizontal, EnterDirection.FromBottom => [ExitDirection.ToLeft, ExitDirection.ToRight]
| OpticsElement.Splitter SplitterDirection.Horizontal, EnterDirection.FromRight => [ExitDirection.ToLeft]
| OpticsElement.Splitter SplitterDirection.Vertical, EnterDirection.FromTop => [ExitDirection.ToBottom]
| OpticsElement.Splitter SplitterDirection.Vertical, EnterDirection.FromLeft => [ExitDirection.ToTop, ExitDirection.ToBottom]
| OpticsElement.Splitter SplitterDirection.Vertical, EnterDirection.FromBottom => [ExitDirection.ToTop]
| OpticsElement.Splitter SplitterDirection.Vertical, EnterDirection.FromRight => [ExitDirection.ToTop, ExitDirection.ToBottom]

private def OpticsTable.neighbour? {table : OpticsTable} (outDirection : ExitDirection) (coordinate : table.Coordinate) : Option table.Coordinate :=
  match outDirection with
  | ExitDirection.ToBottom =>
    if h : coordinate.y.succ < table.height then
      some {coordinate with y := ⟨coordinate.y.succ, h⟩}
    else
      none
  | ExitDirection.ToLeft =>
    if 0 < coordinate.x.val then
      some {coordinate with x := ⟨coordinate.x.val.pred,Nat.lt_of_le_of_lt (Nat.pred_le _) coordinate.x.isLt⟩}
    else
      none
  | ExitDirection.ToTop =>
    if 0 < coordinate.y.val then
      some {coordinate with y := ⟨coordinate.y.val.pred, Nat.lt_of_le_of_lt (Nat.pred_le _) coordinate.y.isLt⟩}
    else
      none
  | ExitDirection.ToRight =>
    if h : coordinate.x.succ < table.width then
      some {coordinate with x := ⟨coordinate.x.succ, h⟩}
    else
      none

private abbrev SeenExitDirection := BitVec 4

private def SeenExitDirection.top (a : SeenExitDirection) : Bool := a[0]
private def SeenExitDirection.right (a : SeenExitDirection) : Bool := a[1]
private def SeenExitDirection.bottom (a : SeenExitDirection) : Bool := a[2]
private def SeenExitDirection.left (a : SeenExitDirection) : Bool := a[3]

private def SeenExitDirection.setTop : SeenExitDirection → SeenExitDirection := BitVec.setBitTrue 0
private def SeenExitDirection.setRight : SeenExitDirection → SeenExitDirection := BitVec.setBitTrue 1
private def SeenExitDirection.setBottom : SeenExitDirection → SeenExitDirection := BitVec.setBitTrue 2
private def SeenExitDirection.setLeft : SeenExitDirection → SeenExitDirection := BitVec.setBitTrue 3

private def SeenExitDirection.countDirection (a : SeenExitDirection) : Fin 5 :=
  ⟨
    a.top.toNat + a.right.toNat + a.bottom.toNat + a.left.toNat,
    Nat.lt_succ_of_le $ Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Bool.toNat_le _) (Bool.toNat_le _)) (Bool.toNat_le _)) (Bool.toNat_le _)
  ⟩

private structure SeenExitDirections (table : OpticsTable) extends Parsing.RectangularGrid SeenExitDirection where
  sameWidth : width = table.width
  sameHeight : height = table.height

private def SeenExitDirections.empty (table : OpticsTable) : SeenExitDirections table :=
  {
    width := table.width
    height := table.height
    elements := Array.mkArray (table.width * table.height) default
    not_empty := table.not_empty
    size_valid := Array.size_mkArray _ _
    sameHeight := rfl
    sameWidth := rfl
  }

private theorem List.foldl_add_bounded (l : List α) (f : α → Fin n) (h₁ : 0 < n) (init : Nat) : l.foldl (λn e ↦ n + (f e).val) init ≤ n.pred * l.length + init := by
  unfold List.foldl
  split
  case h_1 => exact Nat.le_add_left _ _
  case h_2 v ll =>
    have h₂ := List.foldl_add_bounded ll f h₁ (init + (f v).val)
    rw[List.length_cons, Nat.mul_succ]
    have h₃ : (f v).val ≤ n.pred := (Nat.le_pred_iff_lt h₁).mpr (f v).isLt
    rw[←Nat.add_assoc] at h₂
    have h₄ := Nat.le_of_add_le h₂ h₃
    rw[Nat.add_assoc] at h₄
    rw(config := {occs := .pos [3]})[Nat.add_comm] at h₄
    rw[←Nat.add_assoc] at h₄
    assumption

/-- For termination proof -/
private def SeenExitDirections.countExitDirections {table : OpticsTable} (seenDirections : SeenExitDirections table) : Fin (4 * table.width * table.height + 1) :=
  let c := seenDirections.elements.foldl (λn e ↦ n + e.countDirection.val) 0
  have h₁ : c ≤ 4 * seenDirections.width * seenDirections.height := by
    have : c = seenDirections.elements.foldl (λn e ↦ n + e.countDirection.val) 0 := (rfl : c = seenDirections.elements.foldl (λn e ↦ n + e.countDirection.val) 0)
    rw[this, Array.foldl_eq_foldl_toList]
    have : seenDirections.elements.toList.length = seenDirections.elements.size :=  Array.length_toList
    rw[seenDirections.size_valid] at this
    rw[Nat.mul_assoc,←this]
    apply (List.foldl_add_bounded seenDirections.elements.toList SeenExitDirection.countDirection (Nat.succ_pos _)) 0
  have h₂ : (4 * table.width * table.height + 1) = (4 * seenDirections.width * seenDirections.height + 1) := by
    apply congrArg Nat.succ
    rw[Nat.mul_assoc, Nat.mul_assoc]
    apply congrArg
    rw[seenDirections.sameHeight, seenDirections.sameWidth]
  Fin.cast h₂.symm ⟨c,Nat.lt_succ_of_le h₁⟩

private def OpticsTable.followPath {table : OpticsTable} (seenDirections : SeenExitDirections table) (beams : List (EnterDirection × table.Coordinate)) : SeenExitDirections table :=
  -- step 1: discard all beams from the beginning of the list
  --         that do not yield at least one not-yet-seen exit-direction.
  -- step 2a: if no beams are left, done.
  -- step 2: for the first beam that yields new exit directions,
  --         add those exit directions at the end of the beams list and
  --         mark them as seen.
  -- step 3: recurse
  -- step 4: profit

  sorry

------------------------------------------------------------------------------------


private def testInput := r".|...\....
|.-.\.....
.....|-...
........|.
..........
.........\
..../.\\..
.-.-/..|..
.|....-|.\
..//.|...."

#eval parse testInput
