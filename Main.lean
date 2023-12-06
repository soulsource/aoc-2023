import «Common»
import «Day1»
import «Day2»
import «Day3»
import «Day4»
import «Day5»

open DayPart

def try_run_day_part (day : Days) (part : Parts) (data : String) : IO String :=
  let impl : {ι : Type} →  (d : Days) → (p : Parts) → String → [Parse d (ι := ι)] → [Part d p (ι := ι)] → IO String := λ day part data ↦ do
    let instructions ← if let some instructions := Parse.parse day data then
      pure instructions
    else
      throw $ IO.userError "Failed to parse input file."
    if let some result := (Part.run day part instructions).map ToString.toString then
      pure result
    else
      throw $ IO.userError "Failed to find a solution."

  match day, part with
  | ⟨1,_⟩, Parts.One => impl ⟨1,_⟩ Parts.One data
  | ⟨1,_⟩, Parts.Two => impl ⟨1,_⟩ Parts.Two data
  | ⟨2,_⟩, Parts.One => impl ⟨2,_⟩ Parts.One data
  | ⟨2,_⟩, Parts.Two => impl ⟨2,_⟩ Parts.Two data
  | ⟨3,_⟩, Parts.One => impl ⟨3,_⟩ Parts.One data
  | ⟨3,_⟩, Parts.Two => impl ⟨3,_⟩ Parts.Two data
  | ⟨4,_⟩, Parts.One => impl ⟨4,_⟩ Parts.One data
  | ⟨4,_⟩, Parts.Two => impl ⟨4,_⟩ Parts.Two data
  | ⟨5,_⟩, Parts.One => impl ⟨5,_⟩ Parts.One data
  | ⟨5,_⟩, Parts.Two => impl ⟨5,_⟩ Parts.Two data
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
