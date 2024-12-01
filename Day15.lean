import Common

namespace Day15
------------------------------------------------------------------------------------

def parse (input : String) : List Substring := input.toSubstring.trim.splitOn ","

------------------------------------------------------------------------------------

private def holidayAsciiStringHelper (currentValue : UInt8) (input : Substring) : UInt8 :=
  input.foldl (λ(v : UInt8) (c : Char) ↦ 17*(c.toUInt8 + v)) currentValue

def part1 (input : List Substring) : Nat :=
  input.foldl (λc v ↦ c + (holidayAsciiStringHelper 0 v).toNat) 0

------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨15, by simp⟩ (ι := List Substring) where
  parse := Except.ok ∘ parse

instance : Part ⟨15,_⟩ Parts.One (ι := List Substring) (ρ := Nat) where
  run := some ∘ part1

------------------------------------------------------------------------------------

private def testInput := "rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7"

#eval parse testInput |> part1
