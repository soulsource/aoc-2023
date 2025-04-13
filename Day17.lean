import Common
import Std.Data.HashSet
import BinaryHeap
import LeanAStar

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
deriving BEq, Hashable

instance : LawfulBEq Direction where
  rfl := λ{x} ↦ by cases x <;> rfl
  eq_of_beq := λ {a b} ↦ by cases a <;> cases b <;> simp <;> rfl

instance : Finite Direction where
  cardinality := 4
  enumerate := λ
  | .Up => 0
  | .Right => 1
  | .Down => 2
  | .Left => 3
  nth := λ
  | 0 => .Up
  | 1 => .Right
  | 2 => .Down
  | 3 => .Left
  nth_inverse_enumerate := by funext x; cases x <;> rfl
  enumerate_inverse_nth := by funext x; revert x; decide

private inductive StepsInDirection
| One
| Two
| Three
deriving BEq, Hashable

instance : LawfulBEq StepsInDirection where
  rfl := λ{x} ↦ by cases x <;> rfl
  eq_of_beq := λ {a b} ↦ by cases a <;> cases b <;> simp <;> rfl

instance : Finite StepsInDirection where
  cardinality := 3
  enumerate := λ
  | .One => 0
  | .Two => 1
  | .Three => 2
  nth := λ
  | 0 => .One
  | 1 => .Two
  | 2 => .Three
  nth_inverse_enumerate := by funext x; cases x <;> rfl
  enumerate_inverse_nth := by funext x; revert x; decide

private def StepsInDirection.next (s : StepsInDirection) (h₁ : s ≠ .Three) : StepsInDirection :=
  match s with
  | .One => .Two
  | .Two => .Three

private structure PathNode (heatLossMap : HeatLossMap) where
  coordinate : heatLossMap.Coordinate
  currentDirection : Direction
  takenSteps : StepsInDirection
deriving BEq, Hashable

private def PathNode.goUp? (node : PathNode heatLossMap) : Option (PathNode heatLossMap) :=
  match node.coordinate.y, node.currentDirection, node.takenSteps with
  | ⟨0,_⟩, _, _ => none
  | ⟨_+1,_⟩, .Down, _ => none -- can't go back
  | ⟨_+1,_⟩, .Up, .Three => none
  | ⟨y+1,h₁⟩, .Up, steps@h₂:.One | ⟨y+1,h₁⟩, .Up, steps@h₂:.Two =>
    have : steps ≠ .Three := λh₃ ↦ StepsInDirection.noConfusion (h₃.subst h₂.symm)
    let takenSteps := steps.next this
    let coordinate := {x := node.coordinate.x, y := ⟨y, Nat.lt_of_succ_lt h₁⟩}
    some {
      coordinate,
      currentDirection := .Up,
      takenSteps,
      }
  | ⟨y+1,h₁⟩, .Left, _ | ⟨y+1,h₁⟩, .Right, _ =>
    let coordinate := { x := node.coordinate.x, y := ⟨y, Nat.lt_of_succ_lt h₁⟩}
    some {
      coordinate,
      currentDirection := .Up,
      takenSteps := .One,
    }

--since I made mistakes, rather add verification
private theorem PathNode.goUp_goes_up (node result : PathNode heatLossMap) (h₁ : some result = node.goUp?) : result.currentDirection = .Up := by
  unfold PathNode.goUp? at h₁
  split at h₁ <;> simp_all
private theorem PathNode.goUp_y_pred (node result : PathNode heatLossMap) (h₁ : some result = node.goUp?) : result.coordinate.y.val.succ = node.coordinate.y.val := by
  unfold PathNode.goUp? at h₁
  split at h₁ <;> simp_all

private def PathNode.goLeft? (node : PathNode heatLossMap) : Option (PathNode heatLossMap) :=
  match node.coordinate.x, node.currentDirection, node.takenSteps with
  | ⟨0,_⟩, _, _ => none
  | ⟨_+1,_⟩, .Right, _ => none -- can't go back
  | ⟨_+1,_⟩, .Left, .Three => none
  | ⟨x+1,h₁⟩, .Left, steps@h₂:.One | ⟨x+1,h₁⟩, .Left, steps@h₂:.Two =>
    have : steps ≠ .Three := λh₃ ↦ StepsInDirection.noConfusion (h₃.subst h₂.symm)
    let takenSteps := steps.next this
    let coordinate := { x := ⟨x, Nat.lt_of_succ_lt h₁⟩, y := node.coordinate.y }
    some {
      coordinate,
      currentDirection := .Left
      takenSteps
    }
  | ⟨x+1,h₁⟩, .Up, _ | ⟨x+1,h₁⟩, .Down, _ =>
    let coordinate := { x := ⟨x, Nat.lt_of_succ_lt h₁⟩, y := node.coordinate.y }
    some {
      coordinate,
      currentDirection := .Left
      takenSteps := .One
    }

--since I made mistakes, rather add verification
private theorem PathNode.goLeft_goes_left (node result : PathNode heatLossMap) (h₁ : some result = node.goLeft?) : result.currentDirection = .Left := by
  unfold PathNode.goLeft? at h₁
  split at h₁ <;> simp_all
private theorem PathNode.goLeft_x_pred (node result : PathNode heatLossMap) (h₁ : some result = node.goLeft?) : result.coordinate.x.val.succ = node.coordinate.x.val := by
  unfold PathNode.goLeft? at h₁
  split at h₁ <;> simp_all

private def PathNode.goDown? (node : PathNode heatLossMap) : Option (PathNode heatLossMap) :=
  match node.coordinate.y.rev, node.currentDirection, node.takenSteps with
  | ⟨0,_⟩, _, _ => none
  | ⟨_+1,_⟩, .Up, _ => none -- can't go back
  | ⟨_+1,_⟩, .Down, .Three => none
  | ⟨y+1,h₁⟩, .Down, steps@h₂:.One | ⟨y+1,h₁⟩, .Down, steps@h₂:.Two =>
    have : steps ≠ .Three := λh₃ ↦ StepsInDirection.noConfusion (h₃.subst h₂.symm)
    let takenSteps := steps.next this
    let coordinate := {x := node.coordinate.x, y := Fin.rev ⟨y, Nat.lt_of_succ_lt h₁⟩}
    some {
      coordinate,
      currentDirection := .Down,
      takenSteps,
      }
  | ⟨y+1,h₁⟩, .Left, _ | ⟨y+1,h₁⟩, .Right, _  =>
    let coordinate := { x := node.coordinate.x, y := Fin.rev ⟨y, Nat.lt_of_succ_lt h₁⟩}
    some {
      coordinate,
      currentDirection := .Down,
      takenSteps := .One,
    }

--since I made mistakes, rather add verification
private theorem PathNode.goDown_goes_down (node result : PathNode heatLossMap) (h₁ : some result = node.goDown?) : result.currentDirection = .Down := by
  unfold PathNode.goDown? at h₁
  split at h₁ <;> simp_all
private theorem PathNode.goDown_y_succ (node result : PathNode heatLossMap) (h₁ : some result = node.goDown?) : result.coordinate.y.val = node.coordinate.y.val.succ := by
  unfold PathNode.goDown? at h₁
  split at h₁ <;> simp at h₁
  all_goals
    simp_all[Fin.rev]
    omega

private def PathNode.goRight? (node : PathNode heatLossMap) : Option (PathNode heatLossMap) :=
  match node.coordinate.x.rev, node.currentDirection, node.takenSteps with
  | ⟨0,_⟩, _, _ => none
  | ⟨_+1,_⟩, .Left, _ => none -- can't go back
  | ⟨_+1,_⟩, .Right, .Three => none
  | ⟨x+1,h₁⟩, .Right, steps@h₂:.One | ⟨x+1,h₁⟩, .Right, steps@h₂:.Two =>
    have : steps ≠ .Three := λh₃ ↦ StepsInDirection.noConfusion (h₃.subst h₂.symm)
    let takenSteps := steps.next this
    let coordinate := {x := Fin.rev ⟨x, Nat.lt_of_succ_lt h₁⟩, y := node.coordinate.y}
    some {
      coordinate,
      currentDirection := .Right,
      takenSteps,
      }
  | ⟨x+1,h₁⟩, .Down, _ | ⟨x+1,h₁⟩, .Up, _  =>
    let coordinate := {x := Fin.rev ⟨x, Nat.lt_of_succ_lt h₁⟩, y := node.coordinate.y}
    some {
      coordinate,
      currentDirection := .Right,
      takenSteps := .One,
    }

--since I made mistakes, rather add verification
private theorem PathNode.goRightt_goes_right (node result : PathNode heatLossMap) (h₁ : some result = node.goRight?) : result.currentDirection = .Right := by
  unfold PathNode.goRight? at h₁
  split at h₁ <;> simp_all
private theorem PathNode.goRight_x_succ (node result : PathNode heatLossMap) (h₁ : some result = node.goRight?) : result.coordinate.x.val = node.coordinate.x.val.succ := by
  unfold PathNode.goRight? at h₁
  split at h₁ <;> simp at h₁
  all_goals
    simp_all[Fin.rev]
    omega

private def PathNode.getNeighbours (node : PathNode heatLossMap) : List (PathNode heatLossMap) :=
  [node.goLeft?, node.goUp?, node.goRight?, node.goDown?].filterMap id

private def PathNode.estimateMinimumCostToGoal (node : PathNode heatLossMap) : Nat :=
  --costs cannot be lower than 1, so the minimum is just the Manhattan Distance
  --this is a dumb estimate, only true if there is a perfect diagonal path, but should be good enough.
  --also, it must never overestimate, sooo
  let goal : heatLossMap.Coordinate := {
    x := ⟨heatLossMap.width - 1, Nat.pred_lt_self heatLossMap.not_empty.left⟩,
    y := ⟨heatLossMap.height - 1, Nat.pred_lt_self heatLossMap.not_empty.right⟩,
  }
  (goal.x - node.coordinate.x : Fin _).val + (goal.y - node.coordinate.y : Fin _).val

private def PathNode.isGoal (node : PathNode heatLossMap) : Bool :=
  let goal : heatLossMap.Coordinate := {
    x := ⟨heatLossMap.width - 1, Nat.pred_lt_self heatLossMap.not_empty.left⟩,
    y := ⟨heatLossMap.height - 1, Nat.pred_lt_self heatLossMap.not_empty.right⟩,
  }
  node.coordinate == goal


instance : LawfulBEq (PathNode heatLossMap) where
  rfl := λ {a} ↦
    match a with
    | {coordinate, currentDirection, takenSteps} => by
      unfold BEq.beq instBEqPathNode
      simp! --no clue how to rename an unnamed function in the goal
  eq_of_beq := λ{a b} h₁ ↦ by
    unfold BEq.beq instBEqPathNode at h₁
    cases a
    cases b
    simp! at h₁
    simp[h₁]

private def PathNode.toTuple : (PathNode heatLossMap) → (heatLossMap.Coordinate × Direction × StepsInDirection)
| {coordinate, currentDirection, takenSteps} => (coordinate, currentDirection, takenSteps)

private def PathNode.ofTuple  : (heatLossMap.Coordinate × Direction × StepsInDirection) → (PathNode heatLossMap)
| (coordinate, currentDirection, takenSteps) => {coordinate, currentDirection, takenSteps}

private theorem PathNode.toTuple_inv_ofTuple : (PathNode.toTuple (heatLossMap := heatLossMap)) ∘ PathNode.ofTuple = id := rfl
private theorem PathNode.ofTuple_inv_toTuple : (PathNode.ofTuple (heatLossMap := heatLossMap)) ∘ PathNode.toTuple = id := rfl

instance : Finite (PathNode heatLossMap) where
  cardinality := Finite.cardinality (heatLossMap.Coordinate × Direction × StepsInDirection)
  enumerate := Finite.enumerate ∘ PathNode.toTuple
  nth := PathNode.ofTuple ∘ Finite.nth
  enumerate_inverse_nth := by
    funext x
    rewrite[Function.comp_assoc]
    rewrite (occs := .pos [2]) [←Function.comp_assoc]
    simp only[PathNode.toTuple_inv_ofTuple, Function.id_comp, Finite.enumerate_inverse_nth]
  nth_inverse_enumerate := by
    funext x
    rewrite[Function.comp_assoc]
    rewrite (occs := .pos [2]) [←Function.comp_assoc]
    simp only[Finite.nth_inverse_enumerate, Function.id_comp, PathNode.ofTuple_inv_toTuple]

instance : LeanAStar.AStarNode (PathNode heatLossMap) Nat where
  costsLe := Nat.ble
  costs_order := ⟨BinaryHeap.nat_ble_to_heap_transitive_le, BinaryHeap.nat_ble_to_heap_le_total⟩
  remaining_costs_heuristic := PathNode.estimateMinimumCostToGoal
  isGoal := PathNode.isGoal
  getNeighbours := λn↦
    let ns := n.getNeighbours
    ns.map λn ↦ (n, heatLossMap[n.coordinate])
end PathNode

private def HeatLossMap.start (heatLossMap : HeatLossMap) : List (PathNode heatLossMap) :=
  let a : List (PathNode heatLossMap) := if h : heatLossMap.width > 1 then
    let coordinate := {x := ⟨1,h⟩, y := ⟨0, heatLossMap.not_empty.right⟩ }
    [{
      coordinate,
      currentDirection := .Right,
      takenSteps := .One
    }]
  else
    []
  if h : heatLossMap.height > 1 then
    let coordinate := {x := ⟨0, heatLossMap.not_empty.left⟩, y := ⟨1,h⟩}
    {
      coordinate,
      currentDirection := .Down,
      takenSteps := .One
    } :: a
  else
    a

private def HeatLossMap.startPoints (heatLossMap : HeatLossMap) : List (LeanAStar.StartPoint (PathNode heatLossMap)) :=
  heatLossMap.start.map λx ↦ {start := x, initial_costs := heatLossMap[x.coordinate]}

def part1 (heatLossMap : HeatLossMap) : Option Nat :=
  have : Add Nat := inferInstance
  LeanAStar.findLowestCosts heatLossMap.startPoints

------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨17, by simp⟩ (ι := HeatLossMap) where
  parse := (Except.mapError ToString.toString) ∘ parse

instance : Part ⟨17,_⟩ Parts.One (ι := HeatLossMap) (ρ := Nat) where
  run := part1

------------------------------------------------------------------------------------

private def testData := "2413432311323
3215453535623
3255245654254
3446585845452
4546657867536
1438598798454
4457876987766
3637877979653
4654967986887
4564679986453
1224686865563
2546548887735
4322674655533"

#eval parse testData

#eval match parse testData with
| .error _ => none
| .ok m =>
  have : Add Nat := inferInstance
  let r : Option Nat := LeanAStar.findLowestCosts m.startPoints
  r
