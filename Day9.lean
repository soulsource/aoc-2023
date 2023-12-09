import «Common»

namespace Day9

private def parseLine (line : String) : Except String $ List Int :=
  line.split Char.isWhitespace
  |> List.map String.trim
  |> List.filter String.notEmpty
  |> List.mapM String.toInt?
  |> Option.toExcept s!"Failed to parse numbers in line \"{line}\""

def parse (input : String) : Except String $ List $ List Int :=
  let lines := input.splitOn "\n" |> List.map String.trim |> List.filter String.notEmpty
  lines.mapM parseLine

-------------------------------------------------------------------------------------------

private def differences : List Int → List Int
| [] => []
| _ :: [] => []
| a :: b :: as => (a - b) :: differences (b::as)

private theorem differences_length_independent_arg (a b : Int) (bs : List Int) : (differences (a :: bs)).length = (differences (b :: bs)).length := by
  induction bs <;> simp[differences]

-- BEWARE: Extrapolate needs the input reversed.
private def extrapolate : List Int → Int
| [] => 0
| a :: as =>
  if a == 0 && as.all (· == 0) then
    0
  else
    have : (differences (a :: as)).length < as.length + 1 := by
      simp_arith[differences]
      induction (as) <;> simp_arith[differences]
      case cons b bs hb => rw[←differences_length_independent_arg]
                           assumption
    a + extrapolate (differences (a :: as))
termination_by extrapolate a => a.length

def part1 : List (List Int) → Int :=
  List.foldl Int.add 0 ∘ List.map (extrapolate ∘ List.reverse)

-------------------------------------------------------------------------------------------

def part2 : List (List Int) → Int :=
  List.foldl Int.add 0 ∘ List.map extrapolate

-------------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨9, by simp⟩ (ι := List (List Int)) where
  parse := parse

instance : Part ⟨9,_⟩ Parts.One (ι := List (List Int)) (ρ := Int) where
  run := some ∘ part1

instance : Part ⟨9,_⟩ Parts.Two (ι := List (List Int)) (ρ := Int) where
  run := some ∘ part2

-------------------------------------------------------------------------------------------
