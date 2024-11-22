import Common

namespace Day2
structure Draw (α : Type) where
  red : α
  green : α
  blue : α
  deriving Repr

structure Game where
  id : Nat
  draw : List $ Draw Nat
  deriving Repr

def parse (input : String) : Option $ List Game :=
  let lines := input.splitTrim (. == '\n')
  let lines := lines.filter (not ∘ String.isEmpty)
  let parse_single_line : (String → Option Game):= λ (l : String) ↦ do
    let parse_id := λ (s : String) ↦ do
      let rest ← if s.startsWith "Game " then some (s.drop 5) else none
      rest.toNat?
    let parse_draw := λ (s : String) ↦ do
      let s := s.splitTrim (· == ',')
      let findAndRemoveTail := λ (s : String) (t : String) ↦
        if s.endsWith t then
          some $ String.dropRight s (t.length)
        else
          none
      let update_draw_parse := λ (pd : Option (Draw (Option String))) (c : String) ↦ do
        let old ← pd
        let red := findAndRemoveTail c " red"
        let green := findAndRemoveTail c " green"
        let blue := findAndRemoveTail c " blue"
        match red, green, blue with
        | some red, none, none => match old.red with
          | none => some $ {old with red := some red}
          | some _ => none
        | none, some green, none => match old.green with
          | none => some $ {old with green := some green}
          | some _ => none
        | none, none, some blue => match old.blue with
          | none => some $ {old with blue := some blue}
          | some _ => none
        | _, _, _  => none
      let parsed_draw ← s.foldl update_draw_parse (some $ Draw.mk none none none)
      let parsed_draw := {
        red := String.toNat? <$> parsed_draw.red,
        green := String.toNat? <$> parsed_draw.green,
        blue := String.toNat? <$> parsed_draw.blue : Draw _}
      let extractOrFail := λ (s : Option $ Option Nat) ↦ match s with
        | none => some 0
        | some none => none
        | some $ some x => some x
      let red ← extractOrFail parsed_draw.red
      let green ← extractOrFail parsed_draw.green
      let blue ← extractOrFail parsed_draw.blue
      pure { red := red, blue := blue, green := green : Draw _}
    let parse_draws := λ s ↦ List.mapM parse_draw $ s.splitTrim (· == ';')
    let (id, draw) ← match l.splitTrim (· == ':') with
    | [l, r] => Option.zip (parse_id l) (parse_draws r)
    | _ => none
    pure { id := id, draw := draw}
  lines.mapM parse_single_line

def part1 (games : List Game) : Nat :=
  let draw_possible := λ g ↦ g.red ≤ 12 && g.green ≤ 13 && g.blue ≤ 14
  let possible := flip List.all draw_possible
  let possible_games := games.filter (possible ∘ Game.draw)
  possible_games.map Game.id |> List.foldl Nat.add 0

def part2 (games : List Game) : Nat :=
  let powerOfGame := λ (g : Game) ↦
    let minReq := λ (c : Draw Nat → Nat) ↦
      g.draw.map c |> List.max? |> flip Option.getD 0
    minReq Draw.red * minReq Draw.green * minReq Draw.blue
  let powers := games.map powerOfGame
  powers.foldl Nat.add 0

open DayPart
instance : Parse ⟨2, by simp⟩ (ι := List Game) where
  parse := (λ o ↦ match o with | some a => pure a | none => throw "Failed to parse input") ∘ parse

instance : Part ⟨2,_⟩ Parts.One (ι := List Game) (ρ := Nat) where
  run := some ∘ part1

instance : Part ⟨2,_⟩ Parts.Two (ι := List Game) (ρ := Nat) where
  run := some ∘ part2

def testInput : String :=
"Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green"

 -- #eval part1 <$> parse testInput

 -- #eval part2 <$> parse testInput
