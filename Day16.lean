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

private def OpticsTable.neighbour? {table : OpticsTable} (outDirection : ExitDirection) (coordinate : table.Coordinate) : Option (EnterDirection × table.Coordinate) :=
  match outDirection with
  | ExitDirection.ToBottom =>
    if h : coordinate.y.succ < table.height then
      some (EnterDirection.FromTop, {coordinate with y := ⟨coordinate.y.succ, h⟩})
    else
      none
  | ExitDirection.ToLeft =>
    if 0 < coordinate.x.val then
      some (EnterDirection.FromRight,{coordinate with x := ⟨coordinate.x.val.pred,Nat.lt_of_le_of_lt (Nat.pred_le _) coordinate.x.isLt⟩})
    else
      none
  | ExitDirection.ToTop =>
    if 0 < coordinate.y.val then
      some (EnterDirection.FromBottom, {coordinate with y := ⟨coordinate.y.val.pred, Nat.lt_of_le_of_lt (Nat.pred_le _) coordinate.y.isLt⟩})
    else
      none
  | ExitDirection.ToRight =>
    if h : coordinate.x.succ < table.width then
      some (EnterDirection.FromLeft, {coordinate with x := ⟨coordinate.x.succ, h⟩})
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

private def SeenExitDirection.contains (d : SeenExitDirection) : ExitDirection → Bool
| ExitDirection.ToTop => d.top
| ExitDirection.ToRight => d.right
| ExitDirection.ToBottom => d.bottom
| ExitDirection.ToLeft => d.left

private def SeenExitDirection.setDirection (d : SeenExitDirection) : ExitDirection → SeenExitDirection
| ExitDirection.ToTop => d.setTop
| ExitDirection.ToRight => d.setRight
| ExitDirection.ToBottom => d.setBottom
| ExitDirection.ToLeft => d.setLeft

instance : ToString SeenExitDirection where
  toString := λc ↦
  match h : c with
  | 0b0000#4 => "."
  | 0b0001#4 => "↑"
  | 0b0010#4 => "→"
  | 0b0011#4 => "└"
  | 0b0100#4 => "↓"
  | 0b0101#4 => "↕"
  | 0b0110#4 => "┌"
  | 0b0111#4 => "├"
  | 0b1000#4 => "←"
  | 0b1001#4 => "┘"
  | 0b1010#4 => "↔"
  | 0b1011#4 => "┴"
  | 0b1100#4 => "┐"
  | 0b1101#4 => "┤"
  | 0b1110#4 => "┬"
  | 0b1111#4 => "┼"
  | ⟨x+16,_⟩ =>
    -- above Fin 15 exhaustive matches are not auto-detected, see https://github.com/leanprover/lean4/issues/5181 and Contradiction.Config.searchFuel
    False.elim (absurd c.isLt (Nat.not_lt_of_ge $ h.substr $ Nat.le_add_left 16 x))

private def SeenExitDirection.countDirection (a : SeenExitDirection) : Fin 5 :=
  ⟨
    a.top.toNat + a.right.toNat + a.bottom.toNat + a.left.toNat,
    Nat.lt_succ_of_le $ Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Bool.toNat_le _) (Bool.toNat_le _)) (Bool.toNat_le _)) (Bool.toNat_le _)
  ⟩

private def SeenExitDirection.isEnergized : SeenExitDirection → Bool
| 0b0000#4 => false
| _ => true

private theorem SeenExitDirection.setDirection_increasesCountDirection (a : SeenExitDirection) (e : ExitDirection) (h₁ : a.contains e = false) : a.countDirection < (a.setDirection e).countDirection := by
  have Fin.val_three : ∀(n : Nat), (3 : Fin (n + 4)).val = 3 := λx↦rfl
  cases e
  all_goals
    unfold contains at h₁
    simp[countDirection, setDirection, setTop, setLeft, setRight, setBottom, left, right, bottom, top] at h₁ ⊢
    simp[h₁, BitVec.setBitTrue, Fin.val_three]
    unfold getElem BitVec.instGetElemNatBoolLt BitVec.getLsb' Nat.testBit
    simp

private structure SeenExitDirections (table : OpticsTable) extends Parsing.RectangularGrid SeenExitDirection where
  sameWidth : width = table.width
  sameHeight : height = table.height

instance {table : OpticsTable} : ToString (SeenExitDirections table) where
  toString := λes ↦ Id.run do
  let mut result := ""
  for hl: line in [:es.height] do
    for hc: column in [:es.width] do
      result := result.append $ ToString.toString (es.toRectangularGrid[{x := ⟨column, hc.upper⟩, y := ⟨line, hl.upper⟩ : es.Coordinate}])
    result := result.append "\n"
  result

instance {table : OpticsTable} : Repr (SeenExitDirections table) where
  reprPrec t _ := ToString.toString t

private def SeenExitDirections.set {table : OpticsTable} {d : SeenExitDirections table} (c : d.Coordinate) (v : SeenExitDirection) : SeenExitDirections table :=
  {
    d with
      toRectangularGrid := d.toRectangularGrid.set c v
  }

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

/-- Factored out to work around that annoying "generalize failed, result is not type correct" errror -/
private theorem SeenExitDirections.countExitDirections_increasesWhenSet_Aux (l : List SeenExitDirection) (i : Nat) (h₁ : i < l.length) (direction : ExitDirection) (h₂ : l[i].contains direction = false) (prev: Nat) : List.foldl (fun n e => n + e.countDirection.val) prev l < List.foldl (fun n e => n + e.countDirection.val) prev (l.set i (l[i].setDirection direction)) := by
  cases i
  case zero =>
    unfold List.set
    split; case h_2 | h_3 => contradiction
    case h_1 r1 r2 r3 d ds r4 =>
      clear r1 r2 r3 r4
      simp at h₂ ⊢
      simp only [←List.foldl_map]
      rewrite[Nat.add_comm]
      rewrite(config:={occs := .pos [2]})[Nat.add_comm]
      simp[List.foldl_assoc]
      -- f-ing finally
      exact SeenExitDirection.setDirection_increasesCountDirection _ _ h₂
  case succ j =>
    match l with
    | a :: as =>
      simp at h₁ h₂ ⊢
      apply countExitDirections_increasesWhenSet_Aux
      assumption

private theorem SeenExitDirections.countExitDirections_increasesWhenSet {table : OpticsTable} (seenDirections : SeenExitDirections table) (index : seenDirections.Coordinate) (direction : ExitDirection) (h₁ : seenDirections.toRectangularGrid[index].contains direction = false) : (seenDirections.countExitDirections) < (seenDirections.set index $ seenDirections.toRectangularGrid[index].setDirection direction).countExitDirections := by
  unfold countExitDirections SeenExitDirections.set Parsing.RectangularGrid.set getElem Parsing.instGetElemRectangularGridCoordinateEq Parsing.RectangularGrid.Get
  unfold getElem Parsing.instGetElemRectangularGridCoordinateEq Parsing.RectangularGrid.Get at h₁
  simp at h₁ ⊢
  unfold Parsing.RectangularGrid.Coordinate.toIndex at h₁ ⊢
  unfold Array.set
  simp[Array.foldl_eq_foldl_toList] at h₁ ⊢
  rw[Array.getElem_eq_getElem_toList] at h₁ ⊢
  apply countExitDirections_increasesWhenSet_Aux
  assumption

private def OpticsTable.findFirstExitDirectionNotSeenInQueue {table : OpticsTable} (seenDirections : SeenExitDirections table) (beams : List (EnterDirection × table.Coordinate)) : Option (table.Coordinate × ExitDirection × List (EnterDirection × table.Coordinate)) :=
  match beams with
  | [] => none
  | b :: bs =>
    let opticsElement := table[b.snd]
    let outputDirections := opticsElement.outputDirections b.fst
    let sdCoordinate : seenDirections.Coordinate := {
      x := Fin.cast seenDirections.sameWidth.symm b.snd.x
      y := Fin.cast seenDirections.sameHeight.symm b.snd.y
    }
    let seenExitDirections := seenDirections.toRectangularGrid[sdCoordinate]
    let notSeenOutputDirections := outputDirections.filter λd ↦ not $ seenExitDirections.contains d
    match notSeenOutputDirections with
    | [] => findFirstExitDirectionNotSeenInQueue seenDirections bs
    | a :: [] => some (b.snd, a, bs)
    | a :: _ => some (b.snd, a, b :: bs)

private theorem OpticsTable.findFirstExitDirectionNotSeenInQueue_notContains {table : OpticsTable} (seenDirections : SeenExitDirections table) (beams : List (EnterDirection × table.Coordinate)) {result : table.Coordinate × ExitDirection × List (EnterDirection × table.Coordinate)} (h₁ : OpticsTable.findFirstExitDirectionNotSeenInQueue seenDirections beams = some result) : seenDirections.toRectangularGrid[{x := Fin.cast seenDirections.sameWidth.symm result.fst.x, y := Fin.cast seenDirections.sameHeight.symm result.fst.y : seenDirections.Coordinate}].contains result.snd.fst = false := by
  unfold findFirstExitDirectionNotSeenInQueue at h₁
  split at h₁
  case h_1 => contradiction
  case h_2 del b bs =>
    clear del
    simp at h₁
    split at h₁
    case h_1 =>
      exact findFirstExitDirectionNotSeenInQueue_notContains seenDirections bs h₁
    case' h_2 ed heq | h_3 ed eds _ heq =>
      have h₂ := Option.some.inj h₁
      subst result
      generalize { x := Fin.cast _ b.snd.x, y := Fin.cast _ b.snd.y : seenDirections.Coordinate } = c at *
      have h₂ : ed ∈ List.filter (fun d => !seenDirections.toRectangularGrid[c].contains d) (OpticsElement.outputDirections table[b.snd] b.fst) := by simp only [heq, List.mem_singleton, List.mem_cons, true_or]
      exact (Bool.not_eq_true' _).mp (List.mem_filter.mp h₂).right

private def OpticsTable.followPath {table : OpticsTable} (seenDirections : SeenExitDirections table) (beams : List (EnterDirection × table.Coordinate)) : SeenExitDirections table :=
  -- step 1: discard all beams from the beginning of the list
  --         that do not yield at least one not-yet-seen exit-direction.
  -- step 2a: if no beams are left, done.
  -- step 2: for the first beam that yields new exit directions,
  --         add those exit directions at the start of the beams list and
  --         mark them as seen.
  -- step 3: recurse
  -- step 4: profit
  match _h₁ : table.findFirstExitDirectionNotSeenInQueue seenDirections beams with
  | none => seenDirections
  | some (coordinate, exitDirection, remainingBeams) =>
    let sdCoordinate : seenDirections.Coordinate := {
      x := Fin.cast seenDirections.sameWidth.symm coordinate.x
      y := Fin.cast seenDirections.sameHeight.symm coordinate.y
    }
    let newSeenDirections := seenDirections.set sdCoordinate
      (seenDirections.toRectangularGrid[sdCoordinate].setDirection exitDirection)
    match table.neighbour? exitDirection coordinate with
    | none =>
      -- no neighbour, but we still need to note down the exit direction as seen
      OpticsTable.followPath newSeenDirections remainingBeams
    | some cd =>
      OpticsTable.followPath newSeenDirections (cd :: remainingBeams)
termination_by 4 * table.width * table.height - seenDirections.countExitDirections
decreasing_by
  all_goals
  apply Nat.sub_lt_of_gt
  case h₁ =>
    exact Nat.le_of_lt_succ $ Fin.isLt _
  case h₂ =>
    apply SeenExitDirections.countExitDirections_increasesWhenSet
    exact OpticsTable.findFirstExitDirectionNotSeenInQueue_notContains seenDirections beams _h₁

private def SeenExitDirections.countEnergizedTiles {table : OpticsTable} (seenDirections : SeenExitDirections table) : Nat :=
  seenDirections.elements.foldl (λc ed ↦ c + ed.isEnergized.toNat) 0

def part1 (table : OpticsTable) : Nat :=
  let seenDirections := table.followPath (SeenExitDirections.empty table) [(EnterDirection.FromLeft, {x := ⟨0,table.not_empty.left⟩, y := ⟨0,table.not_empty.right⟩})]
  seenDirections.countEnergizedTiles


------------------------------------------------------------------------------------
open DayPart
instance : Parse ⟨16, by simp⟩ (ι := OpticsTable) where
  parse := (Except.mapError ToString.toString) ∘ parse

instance : Part ⟨16,_⟩ Parts.One (ι := OpticsTable) (ρ := Nat) where
  run := λc ↦ some (part1 c)

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

#eval match parse testInput with
| Except.error e => s!"Error: {e}".toFormat
| Except.ok ot =>
  Repr.reprPrec (ot.followPath (SeenExitDirections.empty ot) [(EnterDirection.FromLeft, {x := ⟨0,ot.not_empty.left⟩, y := ⟨0,ot.not_empty.right⟩})]) 0

#eval match parse testInput with
| Except.error e => s!"Error: {e}"
| Except.ok ot => ToString.toString $ part1 ot
