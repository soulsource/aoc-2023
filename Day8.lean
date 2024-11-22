import «Common»
import Lean.Data.HashMap
import Lean.Data.HashSet

namespace Day8

inductive Instruction
  | left
  | right

instance : ToString Instruction where
  toString a := match a with
  | Instruction.left => "Left"
  | Instruction.right => "Right"

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

open Std in
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
private def pass (waypoints : Std.HashMap WaypointId ConnectedWaypoints) (alreadyDoneSteps : Nat) (currentPosition : WaypointId) (instructions : List Instruction) : Except (Option (Nat × WaypointId)) Nat := do
  if currentPosition == "ZZZ" then
    return alreadyDoneSteps
  match instructions with
  | [] => throw $ some (alreadyDoneSteps, currentPosition)
  | a :: as =>
    let currentWaypoint := waypoints.get? currentPosition
    match currentWaypoint with
    | none => throw none -- should not happen
    | some currentWaypoint => pass waypoints (alreadyDoneSteps + 1) (currentWaypoint.get a) as

private def part1_impl (waypoints : Std.HashMap WaypointId ConnectedWaypoints) (instructions : List Instruction) (possibleStarts : List WaypointId) (alreadyDoneSteps : Nat) (currentPosition : WaypointId) : Option Nat :=
  let remainingStarts := possibleStarts.filter λs ↦ s != currentPosition
  if remainingStarts.length < possibleStarts.length then -- written this way to make termination_by easy
    let passResult := pass waypoints alreadyDoneSteps currentPosition instructions
    match passResult with
    | Except.ok n => some n
    | Except.error none => none -- dead end on map. Should not be possible.
    | Except.error $ some n => part1_impl waypoints instructions remainingStarts n.fst n.snd
  else
    none -- walking in circles
  termination_by possibleStarts.length

open Std in
def part1 (input : List Instruction × List Waypoint) : Option Nat :=
  let possibleStarts := input.snd.map Waypoint.id
  let waypoints : HashMap WaypointId ConnectedWaypoints := HashMap.ofList $ input.snd.map λw ↦ (w.id, {left := w.left, right := w.right : ConnectedWaypoints})
  let instructions := input.fst
  part1_impl waypoints instructions possibleStarts 0 start

--------------------------------------------------------------------------------------------------------
-- okay, part 2 is nasty.
-- what do we know?
-- o) All paths we follow simultaneously have the same path length, as they have common instructions.
--   x) This means that once we walk in circles on all of them, we are lost.
--      -> That's the way to convince the compiler this program terminates.
-- o) We could use the cycle detection to rule out short, cycled paths.
--   x) Once a path is in a cycle, the targets repeat at cycle-lenght interval.
--   x) I doubt that this would be much faster than brute-force though.

-- let's try brute force first.

private def parallelPass (waypoints : Std.HashMap WaypointId ConnectedWaypoints) (alreadyDoneSteps : Nat) (currentPositions : List WaypointId) (instructions : List Instruction) : Except (Option (Nat × (List WaypointId))) Nat := do
  if currentPositions.all λw ↦ w.endsWith "Z" then
    return alreadyDoneSteps
  match instructions with
  | [] => throw $ some (alreadyDoneSteps, currentPositions)
  | a :: as =>
    let currentWaypoint := currentPositions.mapM waypoints.get?
    match currentWaypoint with
    | none => throw none -- should not happen
    | some currentWaypoints =>
      let nextWaypoints := currentWaypoints.map $ flip ConnectedWaypoints.get a
      parallelPass waypoints (alreadyDoneSteps + 1) nextWaypoints as


private def totalRemainingStarts (s : List (List WaypointId)) : Nat :=
  s.foldl (·+·.length) 0

private def part2_impl (waypoints : Std.HashMap WaypointId ConnectedWaypoints) (instructions : List Instruction) (alreadyDoneSteps : Nat) (possibleStarts : List (List WaypointId)) (currentPositions : List WaypointId) : Option Nat :=
  let remainingStarts := (possibleStarts.zip currentPositions).map λs ↦ s.fst.filter λt ↦ t != s.snd
  -- I _really_ don't want to prove stuff by hand... Luckily this works.
  if totalRemainingStarts remainingStarts < totalRemainingStarts possibleStarts then
    let passResult := parallelPass waypoints alreadyDoneSteps currentPositions instructions
    match passResult with
    | Except.ok n => some n
    | Except.error none => none -- dead end on map. Should not be possible.
    | Except.error $ some n => part2_impl waypoints instructions n.fst remainingStarts n.snd
  else
    none -- walking in circles
  termination_by totalRemainingStarts possibleStarts

-- Okay, tried Brute Force, it did NOT work. Or rather, it might work, but I won't be able to prove
-- termination for it. Not that it wouldn't be possible to prove, just I won't manage to.
-- The problem is that the termination condition in part2_impl is too soon.
-- You can actually see this in the example (for which part2_impl works, but by chance).
-- While the goals in each part repeat, they repeat at different rates.
-- Soo, we would need to continue even after each part has started walking in circles.
-- However, just doing that runs for a very long time without finding a result.
-- Sooo, let's be smarter.
--
-- Every path consist of 2 segments. The part that leads up to a cycle, and the cycle.
-- Both parts can contain goals, but once the cycle starts, the goals repeat with cycle-length.
-- A cycle is at least one pass, but can (and does...) consist of multiple passes too.

-- We can use part2_impl still - to verify that we do not reach the goals before all our paths start
-- cycling. That allows us to only care about cycling paths in the second part of the solution, which
-- we only reach if part2_impl does not yield a result (we know it doesn't, but that would be cheating).

-- Soo, how can the second part look like?

-- For simplicity let's not do this in parallel. Rather, let's find the goals for each start individually
-- So, let's just consider a single path (like the one from part1)
-- We need to write down the number of steps at which we reach a goal.
-- Whenever we remove a remaining start from the possible starts list, we need to note it down, and
--   how many steps it took us to get there.
-- Once we detect a circle, we can look up
--   how many steps we took in total till we startec cycling
--   and how many steps it took us to reach the cycle start for the first time
--   that's the period of each goal in the cycle.
-- For each goal that was found between cycle-start and cycle-end, we can write down an equation:
-- x = steps_from_start + cycle_length * n
-- n is a Natural number here, not an integer. x is the number of steps at which we pass this goal

-- Once we have that information for all goals of all starts, we can combine it:
-- That's a set of Diophantine equations.
--
-- Or, rather, several sets of Diophantine equations...
-- For each combination of goals that are reached in the cycles of the participating paths, we need to
-- solve the following system:
--
-- We can write each goal for each run in the form x = g0 + n * cg
-- Where x is the solution we are looking for, g0 is the number of steps from the start until
-- we hit the goal for the first time **in the cycle**, and cg is the cycle length
--
-- Once we have those equations, we can combine them pairwise: https://de.wikipedia.org/wiki/Lineare_diophantische_Gleichung
-- This allows us to reduce all paths to a single one, which has multiple equations that
-- describe when a goal is reached.
-- For each of those equations we need to find the first solution that is larger than
-- the point where all paths started to cycle. The smallest of those is the result.

-- a recurring goal, that starts at "start" and afterwards appears at every "interval".
private structure CyclingGoal where
  start : Nat
  interval : Nat
  deriving BEq

instance : ToString CyclingGoal where
  toString g := s!"`g = {g.start} + n * {g.interval}`"

private def CyclingGoal.nTh (goal : CyclingGoal) (n : Nat) : Nat :=
  goal.start + n * goal.interval

-- Combine two cycling goals into a new cycling goal. This might fail, if they never meet.
-- This can for instance happen if they have the same frequency, but different starts.
private def CyclingGoal.combine (a b : CyclingGoal) : Option CyclingGoal :=
  -- a.start + n * a.interval = b.start + m * b.interval
  -- n * a.interval - m * b.interval = b.start - a.start
  -- we want to do as much as possible in Nat, such that we can easily reason about which numbers are
  -- positive. Soo
  let (a, b) := if a.start > b.start then (b,a) else (a,b)
  let (g, u, _) := Euclid.xgcd a.interval b.interval
  -- there is no solution if b.start - a.start is not divisible by g
  let c := (b.start - a.start)
  let s := c / g
  if s * g != c then
    none
  else
    let deltaN := b.interval / g
    let n0 := s * u -- we can use u directly - v would need its sign swapped, but we don't use v.
    -- a.start + (n0 + t * deltaN)*a.interval
    -- a.start + n0*a.interval + t * deltaN * a.interval
    -- we need the first value of t that yields a result >= max(a.start, b.start)
    -- because that's where our cycles start.
    let x := ((max a.start b.start : Int) - a.interval * n0 - a.start)
    let interval := a.interval * deltaN
    let t0 := x / interval
    let t0 := if t0 * interval == x || x < 0 then t0 else t0 + 1 -- int division rounds towards zero, so for x < 0 it's already ceil.
    let start :=  a.start + n0 * a.interval + t0 * deltaN * a.interval
    assert! (start ≥ max a.start b.start)
    let start := start.toNat
    some {start, interval }

private def findCyclingGoalsInPathPass (waypoints : Std.HashMap WaypointId ConnectedWaypoints) (alreadyDoneSteps : Nat) (currentPosition : WaypointId) (instructions : List Instruction) (visitedGoals : List Nat) : Option (Nat × WaypointId × (List Nat)) := do
  let visitedGoals := if currentPosition.endsWith "Z" then
    alreadyDoneSteps :: visitedGoals
  else
    visitedGoals
  match instructions with
  | [] => some (alreadyDoneSteps, currentPosition, visitedGoals)
  | a :: as =>
    let currentWaypoint := waypoints.get? currentPosition
    match currentWaypoint with
    | none => none -- should not happen
    | some currentWaypoint => findCyclingGoalsInPathPass waypoints (alreadyDoneSteps + 1) (currentWaypoint.get a) as visitedGoals

private def findCyclingGoalsInPath_impl (waypoints : Std.HashMap WaypointId ConnectedWaypoints) (instructions : List Instruction) (possibleStarts : List WaypointId) (visitedGoals : List Nat) (visitedStarts : List (WaypointId × Nat)) (currentPosition : WaypointId) (currentSteps : Nat) : List CyclingGoal :=
  let remainingStarts := possibleStarts.filter λs ↦ s != currentPosition
  if remainingStarts.length < possibleStarts.length then -- written this way to make termination_by easy
    let visitedStarts := (currentPosition, currentSteps) :: visitedStarts
    let passResult := findCyclingGoalsInPathPass waypoints currentSteps currentPosition instructions visitedGoals
    match passResult with
      | none =>  [] -- should not happen. Only possible if there's a dead end
      | some (currentSteps, currentPosition, visitedGoals) => findCyclingGoalsInPath_impl waypoints instructions remainingStarts visitedGoals visitedStarts currentPosition currentSteps
  else
    let beenHereWhen := visitedStarts.find? λs ↦ s.fst == currentPosition
    let beenHereWhen := beenHereWhen.get!.snd --cannot possibly fail
    let cycleLength := currentSteps - beenHereWhen
    visitedGoals.filterMap λ n ↦ if n ≥ beenHereWhen then
      some {start := n, interval := cycleLength : CyclingGoal}
    else
      none -- goal was reached before we started to walk in cycles, ignore.
  termination_by possibleStarts.length

private def findCyclingGoalsInPath (waypoints : Std.HashMap WaypointId ConnectedWaypoints) (instructions : List Instruction) (possibleStarts : List WaypointId) (startPosition : WaypointId) : List CyclingGoal :=
  findCyclingGoalsInPath_impl waypoints instructions possibleStarts [] [] startPosition 0

-- returns the number of steps needed until the first _commmon_ goal that cycles is found.
private def findFirstCommonCyclingGoal (waypoints : Std.HashMap WaypointId ConnectedWaypoints) (instructions : List Instruction) (possibleStarts : List WaypointId) (startPositions : List WaypointId) : Option Nat :=
  let cyclingGoals := startPositions.map $ findCyclingGoalsInPath waypoints instructions possibleStarts
  let combinedGoals : List CyclingGoal := match cyclingGoals with
    | [] => []
    | g :: gs => flip gs.foldl g λc n ↦ c.bind λ cc ↦ n.filterMap λ nn ↦ nn.combine cc
  let cyclingGoalStarts := combinedGoals.map CyclingGoal.start
  cyclingGoalStarts.min?

open Std in
def part2 (input : List Instruction × List Waypoint) : Option Nat :=
  let possibleStarts := input.snd.map Waypoint.id
  let waypoints : HashMap WaypointId ConnectedWaypoints := HashMap.ofList $ input.snd.map λw ↦ (w.id, {left := w.left, right := w.right : ConnectedWaypoints})
  let instructions := input.fst
  let positions : List WaypointId := (input.snd.filter λ(w : Waypoint) ↦ w.id.endsWith "A").map Waypoint.id
  part2_impl waypoints instructions 0 (positions.map λ_ ↦ possibleStarts) positions
  <|> -- if part2_impl fails (it does), we need to dig deeper.
  findFirstCommonCyclingGoal waypoints instructions possibleStarts positions

--------------------------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨8, by simp⟩ (ι := List Instruction × List Waypoint) where
  parse := parse

instance : Part ⟨8,_⟩ Parts.One (ι := List Instruction × List Waypoint) (ρ := Nat) where
  run := part1

instance : Part ⟨8,_⟩ Parts.Two (ι := List Instruction × List Waypoint) (ρ := Nat) where
  run := part2

--------------------------------------------------------------------------------------------------------
