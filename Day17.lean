import Common

namespace Day17

------------------------------------------------------------------------------------

abbrev HeatLossMap := Parsing.RectangularGrid Nat

structure CharacterParseError where
  char : Char

instance : ToString CharacterParseError where
  toString := λ ({char}) ↦ s!"Unexpected character '{char}'. Expected a digit between 1 and 9."

open Except in
private def parseCharacter : Char → Except CharacterParseError Nat
| '1' => ok 1
| '2' => ok 2
| '3' => ok 3
| '4' => ok 4
| '5' => ok 5
| '6' => ok 6
| '7' => ok 7
| '8' => ok 8
| '9' => ok 9
| char => error {char}

open Parsing in
def parse : String → Except (RectangularGrid.ParseError CharacterParseError) HeatLossMap := Parsing.RectangularGrid.ofString parseCharacter

------------------------------------------------------------------------------------

section PathNode
variable {heatLossMap : HeatLossMap}

private inductive Direction
| Up
| Right
| Down
| Left
deriving BEq

instance : LawfulBEq Direction where
  rfl := λ{x} ↦ by cases x <;> rfl
  eq_of_beq := λ {a b} ↦ by cases a <;> cases b <;> simp <;> rfl

private inductive StepsInDirection
| One
| Two
| Three

private def StepsInDirection.next (s : StepsInDirection) (h₁ : s ≠ .Three) : StepsInDirection :=
  match s with
  | .One => .Two
  | .Two => .Three

private structure PathNode (heatLossMap : HeatLossMap) where
  coordinate : heatLossMap.Coordinate
  accumulatedCosts : Nat
  currentDirection : Direction
  takenSteps : StepsInDirection

private def PathNode.goUp? (node : PathNode heatLossMap) : Option (PathNode heatLossMap) :=
  match node.coordinate.y, node.currentDirection, node.takenSteps with
  | ⟨0,_⟩, _, _ => none
  | _, Direction.Up, StepsInDirection.Three => none
  | ⟨y,h₂⟩, Direction.Up, steps@h₁:StepsInDirection.One | ⟨y,h₂⟩, Direction.Up, steps@h₁:StepsInDirection.Two =>
    have : steps ≠ .Three := λx ↦ StepsInDirection.noConfusion (x.subst h₁.symm)
    sorry
  | ⟨y,h₂⟩, _, _ => sorry

private def PathNode.getNeighbours (node : PathNode heatLossMap) : List (PathNode heatLossMap) :=
  sorry


end PathNode
