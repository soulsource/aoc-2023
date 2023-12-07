import Common.DayPart

namespace Day4

structure Card where
  id : Nat
  winningNumbers : List Nat
  haveNumbers : List Nat
  deriving Repr

private def Card.matches (c : Card) : Nat :=
  flip c.haveNumbers.foldl 0 λo n ↦
    if c.winningNumbers.contains n then o + 1 else o

private def Card.score : Card → Nat :=
  (· / 2) ∘ (2^·) ∘ Card.matches

abbrev Deck := List Card

private def Deck.score : Deck → Nat :=
  List.foldl (· + ·.score) 0

def parse (input : String) : Except String Deck := do
  let mut cards : Deck := []
  for line in input.splitOn "\n" do
    if line.isEmpty then
      continue
    let cs := line.splitOn ":"
    if p : cs.length = 2 then
      let f := String.trim $ cs[0]'(by simp[p])
      let g := String.trim $ cs[1]'(by simp[p])
      if not $ f.startsWith "Card " then
        throw "All cards need to start with the term \"Card \""
      let f := f.drop 5 |> String.trim
      let f ← if let some f := f.toNat? then pure f else throw "Card numbers need to be numbers."
      let g := g.splitOn "|"
      if q : g.length = 2 then
        let winners := String.trim $ g[0]'(by simp[q])
        let draws := String.trim $ g[1]'(by simp[q])
        let toNumbers := λ(s : String) ↦
          s.split (·.isWhitespace)
          |> List.filter (not ∘ String.isEmpty)
          |> List.mapM String.toNat?
        let winners ← if let some winners := toNumbers winners then pure winners else throw "Failed to parse winning numbers."
        let draws ← if let some draws := toNumbers draws then pure draws else throw "Failed to parse draws"
        cards := {id := f, winningNumbers := winners, haveNumbers := draws : Card} :: cards
      else
        throw "Failed to split input line between winners and draws"
    else
      throw "Failed to split between card number and winners/draws"
  return cards -- cards is **reversed**, that's intentional. It doesn't affect part 1, but makes part 2 easier.

def part2 (input : Deck) : Nat :=
  -- Okay, doing this brute-force is dumb.
  -- Instead let's compute how many cards each original card is worth, and sum that up.
  -- This relies on parse outputting the cards in **reverse** order.
  let multipliers := input.map Card.matches
  let sumNextN : Nat → List Nat → Nat := λn l ↦ (l.take n).foldl (· + ·) 0
  let rec helper : List Nat → List Nat → List Nat := λ input output ↦ match input with
    | [] => output
    | a :: as => helper as $ (1 + (sumNextN a output)) :: output
  let worths := helper multipliers []
  worths.foldl (· + ·) 0

open DayPart

instance : Parse ⟨4, by simp⟩ (ι := Deck) where
  parse := parse

instance : Part ⟨4,_⟩ Parts.One (ι := Deck) (ρ := Nat) where
  run := some ∘ Deck.score

instance : Part ⟨4,_⟩ Parts.Two (ι := Deck) (ρ := Nat) where
  run := some ∘ part2
