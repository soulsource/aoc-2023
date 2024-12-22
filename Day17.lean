import Common
import Std.Data.HashSet
import BinaryHeap

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
  accumulatedCosts : Nat
  currentDirection : Direction
  takenSteps : StepsInDirection

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
      accumulatedCosts := node.accumulatedCosts + heatLossMap[coordinate],
      currentDirection := .Up,
      takenSteps,
      }
  | ⟨y+1,h₁⟩, .Left, _ | ⟨y+1,h₁⟩, .Right, _ =>
    let coordinate := { x := node.coordinate.x, y := ⟨y, Nat.lt_of_succ_lt h₁⟩}
    some {
      coordinate,
      accumulatedCosts := node.accumulatedCosts + heatLossMap[coordinate],
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
      accumulatedCosts := node.accumulatedCosts + heatLossMap[coordinate],
      currentDirection := .Left
      takenSteps
    }
  | ⟨x+1,h₁⟩, .Up, _ | ⟨x+1,h₁⟩, .Down, _ =>
    let coordinate := { x := ⟨x, Nat.lt_of_succ_lt h₁⟩, y := node.coordinate.y }
    some {
      coordinate,
      accumulatedCosts := node.accumulatedCosts + heatLossMap[coordinate],
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
      accumulatedCosts := node.accumulatedCosts + heatLossMap[coordinate],
      currentDirection := .Down,
      takenSteps,
      }
  | ⟨y+1,h₁⟩, .Left, _ | ⟨y+1,h₁⟩, .Right, _  =>
    let coordinate := { x := node.coordinate.x, y := Fin.rev ⟨y, Nat.lt_of_succ_lt h₁⟩}
    some {
      coordinate,
      accumulatedCosts := node.accumulatedCosts + heatLossMap[coordinate],
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
      accumulatedCosts := node.accumulatedCosts + heatLossMap[coordinate],
      currentDirection := .Right,
      takenSteps,
      }
  | ⟨x+1,h₁⟩, .Down, _ | ⟨x+1,h₁⟩, .Up, _  =>
    let coordinate := {x := Fin.rev ⟨x, Nat.lt_of_succ_lt h₁⟩, y := node.coordinate.y}
    some {
      coordinate,
      accumulatedCosts := node.accumulatedCosts + heatLossMap[coordinate],
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

private def PathNode.heuristics (node : PathNode heatLossMap) : Nat :=
  node.estimateMinimumCostToGoal + node.accumulatedCosts

private def PathNode.heuristicsLe (a b : PathNode heatLossMap) : Bool :=
  Nat.ble a.heuristics b.heuristics

theorem PathNode.heuristicsLe_transitive : BinaryHeap.transitive_le (PathNode.heuristicsLe (heatLossMap := heatLossMap)) :=
  λa b c ↦ BinaryHeap.nat_ble_to_heap_transitive_le a.heuristics b.heuristics c.heuristics

theorem PathNode.heuristicsLe_total : BinaryHeap.total_le (PathNode.heuristicsLe (heatLossMap := heatLossMap)) :=
  λa b ↦ BinaryHeap.nat_ble_to_heap_le_total a.heuristics b.heuristics

private theorem PathNode.heuristicsLe_total_and_transitive : BinaryHeap.TotalAndTransitiveLe (PathNode.heuristicsLe (heatLossMap := heatLossMap)) := ⟨PathNode.heuristicsLe_transitive, PathNode.heuristicsLe_total⟩

private def PathNode.isGoal (node : PathNode heatLossMap) : Bool :=
  let goal : heatLossMap.Coordinate := {
    x := ⟨heatLossMap.width - 1, Nat.pred_lt_self heatLossMap.not_empty.left⟩,
    y := ⟨heatLossMap.height - 1, Nat.pred_lt_self heatLossMap.not_empty.right⟩,
  }
  node.coordinate == goal

end PathNode

abbrev OpenSet (heatLossMap : HeatLossMap) := BinaryHeap (PathNode heatLossMap) PathNode.heuristicsLe

private def HeatLossMap.start (heatLossMap : HeatLossMap) : List (PathNode heatLossMap) :=
  let a : List (PathNode heatLossMap) := if h : heatLossMap.width > 1 then
    let coordinate := {x := ⟨1,h⟩, y := ⟨0, heatLossMap.not_empty.right⟩ }
    [{
      coordinate,
      accumulatedCosts := heatLossMap[coordinate],
      currentDirection := .Right,
      takenSteps := .One
    }]
  else
    []
  if h : heatLossMap.height > 1 then
    let coordinate := {x := ⟨0, heatLossMap.not_empty.left⟩, y := ⟨1,h⟩}
    {
      coordinate,
      accumulatedCosts := heatLossMap[coordinate]
      currentDirection := .Down,
      takenSteps := .One
    } :: a
  else
    a

private def OpenSet.start (heatLossMap : HeatLossMap) : OpenSet heatLossMap (heatLossMap.start.length) :=
  --we cannot add the start tile directly - it's invalid state, as it doesn't have a direction
  BinaryHeap.ofList PathNode.heuristicsLe_total_and_transitive heatLossMap.start

private structure ClosedSetEntry (heatLossMap : HeatLossMap) where
  coordinate : heatLossMap.Coordinate
  direction : Direction
  steps : StepsInDirection
deriving BEq, Hashable

instance {heatLossMap : HeatLossMap} : LawfulBEq (ClosedSetEntry heatLossMap) where
  rfl := λ {a} ↦
    match a with
    | {coordinate, direction, steps} => by
      unfold BEq.beq instBEqClosedSetEntry
      simp! --no clue how to rename an unnamed function in the goal
  eq_of_beq := λ{a b} h₁ ↦ by
    unfold BEq.beq instBEqClosedSetEntry at h₁
    cases a
    cases b
    simp! at h₁
    simp[h₁]

private def ClosedSetEntry.toTuple {heatLossMap : HeatLossMap} : (ClosedSetEntry heatLossMap) → (heatLossMap.Coordinate × Direction × StepsInDirection)
| {coordinate, direction, steps} => (coordinate, direction, steps)

private def ClosedSetEntry.ofTuple {heatLossMap : HeatLossMap} : (heatLossMap.Coordinate × Direction × StepsInDirection) → (ClosedSetEntry heatLossMap)
| (coordinate, direction, steps) => {coordinate, direction, steps}

private theorem ClosedSetEntry.toTuple_inv_ofTuple {heatLossMap : HeatLossMap} : (ClosedSetEntry.toTuple (heatLossMap := heatLossMap)) ∘ ClosedSetEntry.ofTuple = id := rfl
private theorem ClosedSetEntry.ofTuple_inv_toTuple {heatLossMap : HeatLossMap} : (ClosedSetEntry.ofTuple (heatLossMap := heatLossMap)) ∘ ClosedSetEntry.toTuple = id := rfl

instance {heatLossMap : HeatLossMap} : Finite (ClosedSetEntry heatLossMap) where
  cardinality := Finite.cardinality (heatLossMap.Coordinate × Direction × StepsInDirection)
  enumerate := Finite.enumerate ∘ ClosedSetEntry.toTuple
  nth := ClosedSetEntry.ofTuple ∘ Finite.nth
  enumerate_inverse_nth := by
    funext x
    rewrite[Function.comp_assoc]
    rewrite (occs := .pos [2]) [←Function.comp_assoc]
    simp only[ClosedSetEntry.toTuple_inv_ofTuple, Function.id_comp, Finite.enumerate_inverse_nth]
  nth_inverse_enumerate := by
    funext x
    rewrite[Function.comp_assoc]
    rewrite (occs := .pos [2]) [←Function.comp_assoc]
    simp only[Finite.nth_inverse_enumerate, Function.id_comp, ClosedSetEntry.ofTuple_inv_toTuple]

instance {heatLossMap : HeatLossMap} : Coe (PathNode heatLossMap) (ClosedSetEntry heatLossMap) where
  coe := λ{coordinate, currentDirection, takenSteps, ..} ↦ {coordinate, direction := currentDirection, steps := takenSteps}

abbrev ClosedSet (heatLossMap : HeatLossMap) := Std.HashSet (ClosedSetEntry heatLossMap)

private def OpenSet.findFirstNotInClosedSet {heatLossMap : HeatLossMap} {n : Nat} (openSet : OpenSet heatLossMap n) (closedSet : ClosedSet heatLossMap) : Option ((r : Nat) × PathNode heatLossMap × OpenSet heatLossMap r) :=
  match n, openSet with
  | 0, _ => none
  | m+1, openSet =>
    let (node, openSet) := openSet.pop
    if closedSet.contains node then
      findFirstNotInClosedSet openSet closedSet
    else
      some ⟨m, node, openSet⟩

private theorem OpenSet.findFirstNotInClosedSet_not_in_closed_set {heatLossMap : HeatLossMap} {n : Nat} (openSet : OpenSet heatLossMap n) (closedSet : ClosedSet heatLossMap) {result : (r : Nat) × PathNode heatLossMap × OpenSet heatLossMap r} (h₁ : openSet.findFirstNotInClosedSet closedSet = some result) : ¬closedSet.contains result.snd.fst := by
  simp
  unfold findFirstNotInClosedSet at h₁
  split at h₁; contradiction
  simp at h₁
  split at h₁
  case h_2.isTrue =>
    have h₃ := findFirstNotInClosedSet_not_in_closed_set _ closedSet h₁
    simp at h₃
    assumption
  case h_2.isFalse h₂ =>
    simp at h₂ h₁
    subst result
    assumption

private def HeatLossMap.findPath {heatLossMap : HeatLossMap} {n : Nat} (openSet : OpenSet heatLossMap n) (closedSet : ClosedSet heatLossMap) : Option Nat :=
  match h₁ : openSet.findFirstNotInClosedSet closedSet with
  | none => none
  | some ⟨_,(node, openSet)⟩ =>
    if node.isGoal then
      some node.accumulatedCosts
    else
      let neighbours := node.getNeighbours.filter (not ∘ closedSet.contains ∘ Coe.coe)
      let newClosedSet := closedSet.insert node
      let openSet := openSet.pushList neighbours
      findPath openSet newClosedSet
termination_by (Finite.cardinality (ClosedSetEntry heatLossMap)) - closedSet.size
decreasing_by
  have h₃ := Std.HashSet.size_insert (m := closedSet) (k := { coordinate := node.coordinate, direction := node.currentDirection, steps := node.takenSteps })
  split at h₃
  case isTrue =>
    have := OpenSet.findFirstNotInClosedSet_not_in_closed_set _ _ h₁
    contradiction
  case isFalse h₂ =>
    rw[h₃]
    have : closedSet.size < (Finite.cardinality (ClosedSetEntry heatLossMap)) := Std.HashSet.size_lt_finite_cardinality_of_not_mem closedSet ⟨_,h₂⟩
    omega



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
| .ok m => HeatLossMap.findPath (OpenSet.start m) Std.HashSet.empty
