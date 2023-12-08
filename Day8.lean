import «Common»
import Lean.Data.HashMap
import Lean.Data.HashSet

namespace Day8

inductive Instruction
  | left
  | right
  deriving Repr

abbrev WaypointId := String

structure Waypoint where
  id : WaypointId
  left : WaypointId
  right : WaypointId
  deriving Repr

-- Okay, the need for different representations in both parts has burnt me once too often.
-- This time it's going to be really dumb.

private def parseInstructions (input : String) : Except String $ List Instruction := do
  let mut result := []
  for character in input.toList do
    match character with
    | 'L' => result := Instruction.left :: result
    | 'R' => result := Instruction.right :: result
    | _ => throw s!"Invalid instruction {character}. Only 'L' and 'R' are valid instructions."
  pure result.reverse

private def parseWaypoint (input : String) : Except String Waypoint :=
  if let [id, targets] := input.splitOn " = " |> List.map String.trim then
    if targets.startsWith "(" && targets.endsWith ")" then
      let withoutBraces := targets.drop 1 |> flip String.dropRight 1
      match withoutBraces.splitOn "," |> List.map String.trim with
      | [a,b] => pure {id := id, left := a, right := b : Waypoint}
      | _ => throw s!"Targets need to have 2 entries, separated by ',', but were {targets}"
    else
      throw s!"Targets for waypoint need to be enclosed in (), but were {targets}"
  else
    throw s!"Waypoint could not be split in ID and targets: {input}"

private def parseWaypoints (input : List String) : Except String $ List Waypoint :=
  input.mapM parseWaypoint

open Lean in
private def validateWaypointLinks (waypoints : List Waypoint) : Bool :=
  let validLinks := HashSet.insertMany HashSet.empty $ waypoints.map Waypoint.id
  waypoints.all λw ↦ validLinks.contains w.left && validLinks.contains w.right

def target : WaypointId := "ZZZ"
def start : WaypointId := "AAA"

def parse (input : String) : Except String $ List Instruction × List Waypoint := do
  let lines := input.splitOn "\n" |> List.map String.trim |> List.filter String.notEmpty
  match lines with
  | instructions :: waypoints =>
    let instructions ← parseInstructions instructions
    let waypoints ← parseWaypoints waypoints
    if let none := waypoints.find? λx ↦ x.id == start then
      throw s!"Input must contain the waypoint \"{start}\"."
    if let none := waypoints.find? λx ↦ x.id == target then
      throw s!"Input must contain the waypoint \"{target}\""
    if not $ validateWaypointLinks waypoints then
      throw "Input contained a waypoint that is not properly linked."
    return (instructions, waypoints)
  | [] => throw "Input was empty (or only contained whitespace)."

--------------------------------------------------------------------------------------------------------
-- One of my goals for this Advent of Code is to show that the code terminates whenever that's
-- possible. In this case, it's not directly possible from the riddle input, but it's possible
-- by adding circle detection. So, instead of making the instructions just an infinite list
-- I'll treat the case that we run out of instruction in a special way, such that we detect
-- if we are lost in the desert.

private structure ConnectedWaypoints where
  left : WaypointId
  right : WaypointId

private def ConnectedWaypoints.get : ConnectedWaypoints →  Instruction → WaypointId
| {left, right := _}, Instruction.left => left
| {left := _, right}, Instruction.right => right

-- does a single pass over all instructions. Returns err if no result has been found and another pass is needed.
-- error is optional - if none, then there is an inconsistency in the input and we are stuck.
private def pass (waypoints : Lean.HashMap WaypointId ConnectedWaypoints) (alreadyDoneSteps : Nat) (currentPosition : WaypointId) (instructions : List Instruction) : Except (Option (Nat × WaypointId)) Nat := do
  if currentPosition == "ZZZ" then
    return alreadyDoneSteps
  match instructions with
  | [] => throw $ some (alreadyDoneSteps, currentPosition)
  | a :: as =>
    let currentWaypoint := waypoints.find? currentPosition
    match currentWaypoint with
    | none => throw none -- should not happen
    | some currentWaypoint => pass waypoints (alreadyDoneSteps + 1) (currentWaypoint.get a) as

private def part1_impl (waypoints : Lean.HashMap WaypointId ConnectedWaypoints) (instructions : List Instruction) (possibleStarts : List WaypointId) (alreadyDoneSteps : Nat) (currentPosition : WaypointId) : Option Nat :=
  let remainingStarts := possibleStarts.filter λs ↦ s != currentPosition
  if remainingStarts.length < possibleStarts.length then -- written this way to make termination_by easy
    let passResult := pass waypoints alreadyDoneSteps currentPosition instructions
    match passResult with
    | Except.ok n => some n
    | Except.error none => none -- dead end on map. Should not be possible.
    | Except.error $ some n => part1_impl waypoints instructions remainingStarts n.fst n.snd
  else
    none -- walking in circles
  termination_by part1_impl a b c d e => c.length

open Lean in
def part1 (input : List Instruction × List Waypoint) : Option Nat :=
  let possibleStarts := input.snd.map Waypoint.id
  let waypoints : HashMap WaypointId ConnectedWaypoints := HashMap.ofList $ input.snd.map λw ↦ (w.id, {left := w.left, right := w.right : ConnectedWaypoints})
  let instructions := input.fst
  part1_impl waypoints instructions possibleStarts 0 start

--------------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨8, by simp⟩ (ι := List Instruction × List Waypoint) where
  parse := parse

instance : Part ⟨8,_⟩ Parts.One (ι := List Instruction × List Waypoint) (ρ := Nat) where
  run := part1

--------------------------------------------------------------------------------------------------------

private def testInput := "LLR

AAA = (BBB, BBB)
BBB = (AAA, ZZZ)
ZZZ = (ZZZ, ZZZ)
"

private def testInput2 := "RL

AAA = (BBB, CCC)
BBB = (DDD, EEE)
CCC = (ZZZ, GGG)
DDD = (DDD, DDD)
EEE = (EEE, EEE)
GGG = (GGG, GGG)
ZZZ = (ZZZ, ZZZ)
"

#eval parse testInput >>= (Option.toExcept "Blah" ∘ part1)
#eval parse testInput2 >>= (Option.toExcept "Blah" ∘ part1)
