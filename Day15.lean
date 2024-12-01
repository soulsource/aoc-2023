import Common

namespace Day15
------------------------------------------------------------------------------------

inductive InvalidInput
| MissingSeparator
| InvalidFocalLength
| DeleteWithExtraData

instance : ToString InvalidInput where
  toString := λ
  | InvalidInput.MissingSeparator => "Each input step needs to contain either '-' xor '=' exactly once."
  | InvalidInput.InvalidFocalLength => "Focal Length has to be an integer in the range [0-9]."
  | InvalidInput.DeleteWithExtraData => "The Delete instruction must be at the end of the command."

private inductive Instruction (α β : Type)
| Remove (label : α) : Instruction α β
| Insert (label : α) (value : β) : Instruction α β

structure Command where
  raw : Substring
  instruction : Instruction Substring (Fin 10)

private def parseCommand (input : Substring) : Except InvalidInput Command :=
  if let [l,v] := input.splitOn "=" then
    if let some v := v.toNat? then
      if h : v < 10 then
        Except.ok $ {raw := input, instruction := Instruction.Insert l ⟨v,h⟩}
      else
        Except.error InvalidInput.InvalidFocalLength
    else
      Except.error InvalidInput.InvalidFocalLength
  else if let [l,v] := input.splitOn "-" then
    if v.isEmpty then
      Except.ok $ {raw := input, instruction := Instruction.Remove l}
    else
      Except.error InvalidInput.DeleteWithExtraData
  else
    Except.error InvalidInput.MissingSeparator

/- Adjusted after part one. For part one this was just the first line and retunred List Substring-/
def parse (input : String) : Except InvalidInput (List Command) :=
  let substrings := input.toSubstring.trim.splitOn ","
  substrings.mapM parseCommand

------------------------------------------------------------------------------------

private def holidayAsciiStringHelper (currentValue : UInt8) (input : Substring) : UInt8 :=
  input.foldl (λ(v : UInt8) (c : Char) ↦ 17*(c.toUInt8 + v)) currentValue

def part1 (input : List Command) : Nat :=
  input.foldl (λc v ↦ c + (holidayAsciiStringHelper 0 v.raw).toNat) 0

------------------------------------------------------------------------------------

/- Feels a bit weird to implement a HashMap myself now, given that I've used one on previous days... -/

private class HolidayAsciiStringHelperAble (α : Type) where
  holidayAsciiStringHelper : α → UInt8

private structure HolidayAsciiStringHelperManualArrangementProcedure (α β : Type) where
  boxes : Array (List (α × β))
  valid : boxes.size = UInt8.size

private def HolidayAsciiStringHelperManualArrangementProcedure.empty (α β : Type) : HolidayAsciiStringHelperManualArrangementProcedure α β :=
  {
    boxes := Array.mkArray UInt8.size [],
    valid := Array.size_mkArray _ _
  }

private def HolidayAsciiStringHelperManualArrangementProcedure.insert {α β : Type} [HolidayAsciiStringHelperAble α] [BEq α] (label : α) (data : β) (old : HolidayAsciiStringHelperManualArrangementProcedure α β) : HolidayAsciiStringHelperManualArrangementProcedure α β :=
  let h := HolidayAsciiStringHelperAble.holidayAsciiStringHelper label
  let index := Fin.cast old.valid.symm h.val
  let box := old.boxes[index]
  let box := updateOrAppend box []
  {
    boxes := old.boxes.set index box
    valid := (Array.size_set old.boxes index box).substr old.valid
  }
where
  updateOrAppend (box : List (α × β)) (accumulator : List (α × β)) : List (α × β) :=
    match box with
    | [] => ((label, data) :: accumulator).reverse
    | b :: bs =>
      if b.fst == label then
        accumulator.reverse ++ (label, data) :: bs
      else
        updateOrAppend bs (b::accumulator)

private def HolidayAsciiStringHelperManualArrangementProcedure.remove {α β : Type} [HolidayAsciiStringHelperAble α] [BEq α] (label : α) (old : HolidayAsciiStringHelperManualArrangementProcedure α β) : HolidayAsciiStringHelperManualArrangementProcedure α β :=
  let h := HolidayAsciiStringHelperAble.holidayAsciiStringHelper label
  let index := Fin.cast old.valid.symm h.val
  let box := old.boxes[index]
  let box := tryRemove box []
  {
    boxes := old.boxes.set index box
    valid := (Array.size_set old.boxes index box).substr old.valid
  }
where
  tryRemove (box : List (α × β)) (accumulator : List (α × β)) : List (α × β) :=
    match box with
    | [] => accumulator.reverse
    | b :: bs =>
      if b.fst == label then
        tryRemove bs accumulator
      else
        tryRemove bs (b :: accumulator)

/- Funny, by the way, that the riddle only needs insert/remove, but not find... -/

private def focussingPower (hashMap : HolidayAsciiStringHelperManualArrangementProcedure Substring (Fin 10)) : Nat :=
  Prod.fst $
  hashMap.boxes.foldl (
    λ(totalPower, boxIndex) box ↦
      let totalPower := Prod.fst $ box.foldl
        (λ(totalPower, lensIndex) lens ↦ (totalPower + boxIndex * lensIndex * lens.snd.val, lensIndex + 1))
        (totalPower, 1)
      (totalPower, boxIndex + 1)
      )
    (0,1)

private instance : HolidayAsciiStringHelperAble Substring where
  holidayAsciiStringHelper := holidayAsciiStringHelper 0

def part2 (input : List Command) : Nat := Id.run do
  let mut map := HolidayAsciiStringHelperManualArrangementProcedure.empty Substring (Fin 10)
  for command in input do
    map := match command.instruction with
    | Instruction.Insert label value => map.insert label value
    | Instruction.Remove label => map.remove label
  focussingPower map


------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨15, by simp⟩ (ι := List Command) where
  parse := (Except.mapError ToString.toString) ∘ parse

instance : Part ⟨15,_⟩ Parts.One (ι := List Command) (ρ := Nat) where
  run := λc ↦ some (part1 c)

instance : Part ⟨15,_⟩ Parts.Two (ι := List Command) (ρ := Nat) where
  run := λc ↦ some (part2 c)

------------------------------------------------------------------------------------

private def testInput := "rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7"

#eval part2 <$> parse testInput
