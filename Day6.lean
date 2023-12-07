import Common.Option
import Common.Helpers

structure Race where
  timeLimit : Nat
  recordDistance : Nat

private def parseLine (header : String) (input : String) : Option (List Nat) := do
  if not $ input.startsWith header then
    failure
  let input := input.drop header.length |> String.trim
  let numbers := input.split Char.isWhitespace
    |> List.map String.trim
    |> List.filter String.isEmpty
  numbers.mapM String.toNat?

def parse (input : String) : Option (List Race) := do
  let lines := input.splitOn "\n"
    |> List.map String.trim
    |> List.filter String.isEmpty
  let (times, distances) ← match lines with
    | [times, distances] => Option.zip (parseLine "Time:" times) (parseLine "Distance:" distances)
    | _ => none
  if times.length != distances.length then
    failure
  let pairs := times.zip distances
  return pairs.map $ uncurry Race.mk
