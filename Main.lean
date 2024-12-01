import «Common»
import «Day1»
import «Day2»
import «Day3»
import «Day4»
import «Day5»
import «Day6»
import «Day7»
import «Day8»
import «Day9»
import «Day10»
import «Day11»
import «Day12»
import «Day13»
import «Day14»
import «Day15»

open DayPart

private def try_run_day_part_impl : {ι ρ: Type} →  (d : Days) → (p : Parts) → String → [Parse d (ι := ι)] → [ToString ρ]  → [Part d p (ι := ι) (ρ := ρ)] → IO String := λ day part data ↦ do
    let instructions ← IO.ofExcept $ Parse.parse day data
    if let some result := (Part.run day part instructions).map ToString.toString then
      pure result
    else
      throw $ IO.userError "Failed to find a solution."

def try_run_day_part (day : Days) (part : Parts) (data : String) : IO String :=
  match day, part with
  |  ⟨1,_⟩, Parts.One => try_run_day_part_impl  ⟨1,_⟩ Parts.One data
  |  ⟨1,_⟩, Parts.Two => try_run_day_part_impl  ⟨1,_⟩ Parts.Two data
  |  ⟨2,_⟩, Parts.One => try_run_day_part_impl  ⟨2,_⟩ Parts.One data
  |  ⟨2,_⟩, Parts.Two => try_run_day_part_impl  ⟨2,_⟩ Parts.Two data
  |  ⟨3,_⟩, Parts.One => try_run_day_part_impl  ⟨3,_⟩ Parts.One data
  |  ⟨3,_⟩, Parts.Two => try_run_day_part_impl  ⟨3,_⟩ Parts.Two data
  |  ⟨4,_⟩, Parts.One => try_run_day_part_impl  ⟨4,_⟩ Parts.One data
  |  ⟨4,_⟩, Parts.Two => try_run_day_part_impl  ⟨4,_⟩ Parts.Two data
  |  ⟨5,_⟩, Parts.One => try_run_day_part_impl  ⟨5,_⟩ Parts.One data
  |  ⟨5,_⟩, Parts.Two => try_run_day_part_impl  ⟨5,_⟩ Parts.Two data
  |  ⟨6,_⟩, Parts.One => try_run_day_part_impl  ⟨6,_⟩ Parts.One data
  |  ⟨6,_⟩, Parts.Two => try_run_day_part_impl  ⟨6,_⟩ Parts.Two data
  |  ⟨7,_⟩, Parts.One => try_run_day_part_impl  ⟨7,_⟩ Parts.One data
  |  ⟨7,_⟩, Parts.Two => try_run_day_part_impl  ⟨7,_⟩ Parts.Two data
  |  ⟨8,_⟩, Parts.One => try_run_day_part_impl  ⟨8,_⟩ Parts.One data
  |  ⟨8,_⟩, Parts.Two => try_run_day_part_impl  ⟨8,_⟩ Parts.Two data
  |  ⟨9,_⟩, Parts.One => try_run_day_part_impl  ⟨9,_⟩ Parts.One data
  |  ⟨9,_⟩, Parts.Two => try_run_day_part_impl  ⟨9,_⟩ Parts.Two data
  | ⟨10,_⟩, Parts.One => try_run_day_part_impl ⟨10,_⟩ Parts.One data
  | ⟨10,_⟩, Parts.Two => try_run_day_part_impl ⟨10,_⟩ Parts.Two data
  | ⟨11,_⟩, Parts.One => try_run_day_part_impl ⟨11,_⟩ Parts.One data
  | ⟨11,_⟩, Parts.Two => try_run_day_part_impl ⟨11,_⟩ Parts.Two data
  | ⟨12,_⟩, Parts.One => try_run_day_part_impl ⟨12,_⟩ Parts.One data
  | ⟨12,_⟩, Parts.Two => try_run_day_part_impl ⟨12,_⟩ Parts.Two data
  | ⟨13,_⟩, Parts.One => try_run_day_part_impl ⟨13,_⟩ Parts.One data
  | ⟨13,_⟩, Parts.Two => try_run_day_part_impl ⟨13,_⟩ Parts.Two data
  | ⟨14,_⟩, Parts.One => try_run_day_part_impl ⟨14,_⟩ Parts.One data
  | ⟨14,_⟩, Parts.Two => try_run_day_part_impl ⟨14,_⟩ Parts.Two data
  | ⟨15,_⟩, Parts.One => try_run_day_part_impl ⟨15,_⟩ Parts.One data
  | _, _ => throw $ IO.userError "The requested combination of day/part has not been implemented yet."

def main (parameters : List String): IO Unit := do
  try
    let (day, part, file) ← match parameters with
    | [day, part, file] => pure (day, part, file)
    | _ => throw $ IO.userError "This program needs to be invoked with 3 parameters: Day (1-25), Part (1-2) and a filename."
    let invalid_day := IO.userError "The first parameter has to be a day, namely a value between 1 and 25."
    let day ← if let some day := day.toNat? then pure day else throw invalid_day
    let (day : Days) ←
      if p : day > 0 ∧ day <= 25 then
        pure ⟨day, p⟩
      else
        throw invalid_day
    let invalid_part := IO.userError "The second parameter must be a part, namely 1 or 2."
    let part ← if let some part := part.toNat? then pure part else throw invalid_part
    let part ← match part with
      | 1 => pure Parts.One
      | 2 => pure Parts.Two
      | _ => throw invalid_part
    let file ← IO.FS.readFile file

    let result ← try_run_day_part day part file
    IO.println s!"Result: {result}"

  catch e =>
    IO.eprintln e
