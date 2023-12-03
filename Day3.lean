import «Common»
import Lean.Data.HashSet
import Lean.Data.HashMap

namespace Day3
structure Coordinate : Type 0 where
  x : Nat
  y : Nat
  deriving Repr, BEq, Ord, Hashable

def Coordinate.default : Coordinate := {x := 0, y := 0}

/--Returns the adjacent fields, row-major order (this is important)-/
def Coordinate.adjacents : Coordinate → List Coordinate
| { x := 0, y := 0} => [
                     ⟨1,0⟩,
    ⟨0,1⟩,           ⟨1,1⟩
  ]
| { x := 0, y := y} => [
    ⟨0,y.pred⟩,      ⟨1,y.pred⟩,
                     ⟨1,y⟩,
    ⟨0,y.succ⟩,      ⟨1,y.succ⟩
  ]
| { x := x, y := 0} => [
    ⟨x.pred,0⟩,                  ⟨x.succ,0⟩,
    ⟨x.pred,1⟩,      ⟨x,1⟩,      ⟨x.succ,1⟩
  ]
| { x := x, y := y} => [
    ⟨x.pred,y.pred⟩, ⟨x,y.pred⟩, ⟨x.succ,y.pred⟩,
    ⟨x.pred,y⟩,                  ⟨x.succ,y⟩,
    ⟨x.pred,y.succ⟩, ⟨x,y.succ⟩, ⟨x.succ,y.succ⟩
  ]

structure Part : Type 0 where
  symbol : Char
  position : Coordinate
  deriving Repr

structure PartNumber : Type 0 where
  value : Nat
  positions : List Coordinate
  deriving Repr, BEq

-- Schematic is just using lists, because at this point it's not clear what kind of lookup
-- is needed in part 2... Probably some kind of HashMap Coordinate Whatever, but that's
-- guesswork for now...
-- Parts can refine the data further, anyhow.
structure Schematic : Type 0 where
  parts : List Part
  numbers : List PartNumber
  deriving Repr

/-- nextByChar gives the coordinate of the **next** character. -/
private def Coordinate.nextByChar : Coordinate → Char → Coordinate
| {x := _, y := oldY}, '\n' => { x := 0, y := oldY + 1 }
| {x := oldX, y := oldY}, _ => { x := oldX + 1, y := oldY }

private def extractParts : List (Coordinate × Char) → List Part :=
  (List.map (uncurry $ flip Part.mk)) ∘ (List.filter $ not ∘ λ (sc : Coordinate × Char) ↦ sc.snd.isWhitespace || sc.snd.isDigit || sc.snd == '.')

private def extractPartNumbers (input : List (Coordinate × Char)) : List PartNumber :=
  let rec helper := λ
  | [], none => []
  | [], some acc => [acc] -- if we are still accumulating a number at the end, commit
  | a :: as, none =>
    if p: a.snd.isDigit then
      --start accumulating a PartNumber
      helper as $ some {value := a.snd.asDigit p, positions := [a.fst]}
    else
      --not accumulating, not a digit, not of interest.
      helper as none
  | a :: as, some acc =>
    if p: a.snd.isDigit then
      --keep accumulating
      helper as $ some {value := acc.value * 10 + a.snd.asDigit p, positions := a.fst :: acc.positions }
    else
      -- we were accumulating, aren't on a number any more -> commit
      acc :: helper as none
  helper input none

def parse (schematic : String) : Option Schematic := do
  -- I think this one is easier if we don't split the input in lines. Because:
  let charsWithCoordinates ← match schematic.toList with
    | [] => none
    | c :: cs => pure $ cs.scan (λ s c ↦ (uncurry Coordinate.nextByChar s, c)) (Coordinate.default, c)
  -- Whitespaces are **intentionally** left in. This makes extracting the numbers easier.
  pure $ {
    parts := extractParts charsWithCoordinates
    numbers := extractPartNumbers charsWithCoordinates
  }

def part1 (schematic : Schematic) : Nat :=
  -- fast lookup: We need to know if a part is at a given coordinate
  open Lean(HashSet) in
  let partCoordinates := HashSet.insertMany HashSet.empty $ schematic.parts.map Part.position
  let partNumbers := schematic.numbers.filter λnumber ↦
    number.positions.any λposition ↦
      position.adjacents.any partCoordinates.contains
  partNumbers.foldl (· + PartNumber.value ·) 0

def part2 (schematic : Schematic) : Nat :=
  -- and now it is obvious that keeping the parsed input free of opinions was a good idea.
  -- because here we need quick lookup for the numbers, not the parts.
  open Lean(HashMap) in
  let numberCoordinates : HashMap Coordinate PartNumber :=
    Lean.HashMap.ofList $ schematic.numbers.bind $ λ pn ↦ pn.positions.map (·, pn)
  let gearSymbols := schematic.parts.filter (Part.symbol · == '*')
  -- but the symbols aren't enough, they need to be adjacent to **exactly** 2 numbers
  let numbersNextGearSymbols := List.dedup <$> gearSymbols.map λgs ↦
    gs.position.adjacents.filterMap numberCoordinates.find?
  let gearSymbols := numbersNextGearSymbols.filter (List.length · == 2)
  let gearRatios := gearSymbols.map $ List.foldl (· * PartNumber.value ·) 1
  gearRatios.foldl (· + ·) 0

open DayPart

instance : Parse ⟨3, by simp⟩ (ι := Schematic) where
  parse := parse

instance : DayPart.Part ⟨3,_⟩ Parts.One (ι := Schematic) (ρ := Nat) where
  run := some ∘ part1

instance : DayPart.Part ⟨3,_⟩ Parts.Two (ι := Schematic) (ρ := Nat) where
  run := some ∘ part2
