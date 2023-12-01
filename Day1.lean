import Common.Helpers
import Common.Option
import Common.DayPart

namespace Day1

def parse (input : String) : Option $ List String :=
  some $ input.split Char.isWhitespace |> List.filter (not ∘ String.isEmpty)

-- Both parts could still be improved by doing two searches, one from the left, one from the right

def part1 (instructions : List String) : Option Nat :=
  let firstLast := λ (o : Option Nat × Option Nat) (c : Char) ↦
    let digit := match c with
    | '0' => some 0
    | '1' => some 1
    | '2' => some 2
    | '3' => some 3
    | '4' => some 4
    | '5' => some 5
    | '6' => some 6
    | '7' => some 7
    | '8' => some 8
    | '9' => some 9
    | _ => none
    if let some digit := digit then
      match o.fst with
      | none => (some digit, some digit)
      | some _ => (o.fst, some digit)
    else
      o
  let scanLine := λ (l : String) ↦ l.foldl firstLast (none, none)
  let numbers := instructions.mapM ((uncurry Option.zip) ∘ scanLine)
  let numbers := numbers.map λ l ↦ l.map λ (a, b) ↦ 10*a + b
  numbers.map (List.foldl (.+.) 0)

def part2 (instructions : List String) : Option Nat :=
  -- once I know how to prove stuff propery, I'm going to improve this. Maybe.
  let instructions := instructions.map String.toList
  let updateState := λ (o : Option Nat × Option Nat) (n : Nat) ↦ match o.fst with
    | none => (some n, some n)
    | some _ => (o.fst, some n)
  let extract_digit := λ (o : Option Nat × Option Nat) (l : List Char) ↦
    match l with
    | '0' :: _ | 'z' :: 'e' :: 'r' :: 'o' :: _ => (updateState o 0)
    | '1' :: _ | 'o' :: 'n' :: 'e' :: _ => (updateState o 1)
    | '2' :: _ | 't' :: 'w' :: 'o' :: _ => (updateState o 2)
    | '3' :: _ | 't' :: 'h' :: 'r' :: 'e' :: 'e' :: _ => (updateState o 3)
    | '4' :: _ | 'f' :: 'o' :: 'u' :: 'r' :: _ => (updateState o 4)
    | '5' :: _ | 'f' :: 'i' :: 'v' :: 'e' :: _ => (updateState o 5)
    | '6' :: _ | 's' :: 'i' :: 'x' :: _ => (updateState o 6)
    | '7' :: _ | 's' :: 'e' :: 'v' :: 'e' :: 'n' :: _ => (updateState o 7)
    | '8' :: _ | 'e' :: 'i' :: 'g' :: 'h' :: 't' :: _ => (updateState o 8)
    | '9' :: _ | 'n' :: 'i' :: 'n' :: 'e' :: _ => (updateState o 9)
    | _ => o
  let rec firstLast := λ (o : Option Nat × Option Nat) (l : List Char) ↦
    match l with
    | [] => o
    | _ :: cs => firstLast (extract_digit o l) cs
  let scanLine := λ (l : List Char) ↦ firstLast (none, none) l
  let numbers := instructions.mapM ((uncurry Option.zip) ∘ scanLine)
  let numbers := numbers.map λ l ↦ l.map λ (a, b) ↦ 10*a + b
  numbers.map (List.foldl (.+.) 0)

open DayPart
instance : Parse ⟨1, by simp⟩ (ι := List String) where
  parse := parse

instance : Part ⟨1, _⟩ Parts.One (ι := List String) (ρ := Nat) where
  run := part1

instance : Part ⟨1, _⟩ Parts.Two (ι := List String) (ρ := Nat) where
  run := part2
