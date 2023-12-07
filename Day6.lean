import Common.Option
import Common.Helpers
import Common.DayPart

structure Race where
  timeLimit : Nat
  recordDistance : Nat
  deriving Repr

private def parseLine (header : String) (input : String) : Except String (List Nat) := do
  if not $ input.startsWith header then
    throw s!"Unexpected line header: {header}, {input}"
  let input := input.drop header.length |> String.trim
  let numbers := input.split Char.isWhitespace
    |> List.map String.trim
    |> List.filter (not ∘ String.isEmpty)
  numbers.mapM $ Option.toExcept s!"Failed to parse input line: Not a number {input}" ∘  String.toNat?

def parse (input : String) : Except String (List Race) := do
  let lines := input.splitOn "\n"
    |> List.map String.trim
    |> List.filter (not ∘ String.isEmpty)
  let (times, distances) ← match lines with
    | [times, distances] =>
      let times ← parseLine "Time:" times
      let distances ← parseLine "Distance:" distances
      pure (times, distances)
    | _ => throw "Failed to parse: there should be exactly 2 lines of input"
  if times.length != distances.length then
    throw "Input lines need to have the same number of, well, numbers."
  let pairs := times.zip distances
  if pairs = [] then
    throw "Input does not have at least one race."
  return pairs.map $ uncurry Race.mk

-- okay, part 1 is a quadratic equation. Simple as can be
-- s = v * tMoving
-- s = tPressed * (tLimit - tPressed)
-- (tPressed - tLimit) * tPressed + s = 0
-- tPressed² - tPressed * tLimit + s = 0
-- tPressed := tLimit / 2 ± √(tLimit² / 4 - s)
-- beware: We need to _beat_ the record, so s here is the record + 1

-- Inclusive! This is the smallest number that can win, and the largest number that can win
private def Race.timeRangeToWin (input : Race) : (Nat × Nat) :=
  let tLimit  := input.timeLimit.toFloat
  let sRecord := input.recordDistance.toFloat
  let tlimitHalf := 0.5 * tLimit
  let theRoot := (tlimitHalf^2 - sRecord - 1.0).sqrt
  let lowerBound := tlimitHalf - theRoot
  let upperBound := tlimitHalf + theRoot
  let lowerBound := lowerBound.ceil.toUInt64.toNat
  let upperBound := upperBound.floor.toUInt64.toNat
  (lowerBound,upperBound)

def part1 (input : List Race) : Nat :=
  let limits := input.map Race.timeRangeToWin
  let counts := limits.map $ λ p ↦ p.snd - p.fst + 1 -- inclusive range
  counts.foldl (· * ·) 1

-- part2 is the same thing, but here we need to be careful.
-- namely, careful about the precision of Float. Which luckily is enough, as confirmed by pen&paper
-- but _barely_ enough.
-- If Lean's Float were an actual C float and not a C double, this would not work.

-- we need to concatenate the numbers again (because I don't want to make a separate parse for part2)
private def combineNumbers (left : Nat) (right : Nat) : Nat :=
  let rec countDigits := λ (s : Nat) (n : Nat) ↦
    if p : n > 0 then
      have : n > n / 10 := by simp[p, Nat.div_lt_self]
      countDigits (s+1) (n/10)
    else
      s
  let d := if right = 0 then 1 else countDigits 0 right
  left * (10^d) + right

def part2 (input : List Race) : Nat :=
  let timeLimits := input.map Race.timeLimit
  let timeLimit := timeLimits.foldl combineNumbers 0
  let records := input.map Race.recordDistance
  let record := records.foldl combineNumbers 0
  let limits := Race.timeRangeToWin $ {timeLimit := timeLimit, recordDistance := record}
  limits.snd - limits.fst + 1 -- inclusive range

open DayPart
instance : Parse ⟨6, by simp⟩ (ι := List Race) where
  parse := parse

instance : Part ⟨6, _⟩ Parts.One (ι := List Race) (ρ := Nat) where
  run := some ∘ part1

instance : Part ⟨6, _⟩ Parts.Two (ι := List Race) (ρ := Nat) where
  run := some ∘ part2
