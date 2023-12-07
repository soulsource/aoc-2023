namespace DayPart

abbrev Days := {d : Nat // d > 0 ∧ d <= 25}
inductive Parts
| One
| Two

class Parse (day : Days) {ι : outParam Type} where
  parse : String → Except String ι

class Part (day : Days) (part : Parts) {ι ρ : outParam Type} [Parse day (ι := ι)] [ToString ρ] where
  run : ι → Option ρ -- can fail, because it deals with user input...
