import Common.DayPart
import Common.List

namespace Day5

structure Seed where
  id : Nat
  deriving BEq, Ord, Repr

structure Soil where
  id : Nat
  deriving BEq, Ord, Repr

structure Fertilizer where
  id : Nat
  deriving BEq, Ord, Repr

structure Water where
  id : Nat
  deriving BEq, Ord, Repr

structure Light where
  id : Nat
  deriving BEq, Ord, Repr

structure Temperature where
  id : Nat
  deriving BEq, Ord, Repr

structure Humidity where
  id : Nat
  deriving BEq, Ord, Repr

structure Location where
  id : Nat
  deriving BEq, Ord, Repr

private class NatId (α : Type) where
  fromNat : Nat → α
  toNat : α → Nat

private instance : NatId Seed where
  fromNat := Seed.mk
  toNat := Seed.id

private instance : NatId Soil where
  fromNat := Soil.mk
  toNat := Soil.id

private instance : NatId Fertilizer where
  fromNat := Fertilizer.mk
  toNat := Fertilizer.id

private instance : NatId Water where
  fromNat := Water.mk
  toNat := Water.id

private instance : NatId Light where
  fromNat := Light.mk
  toNat := Light.id

private instance : NatId Temperature where
  fromNat := Temperature.mk
  toNat := Temperature.id

private instance : NatId Humidity where
  fromNat := Humidity.mk
  toNat := Humidity.id

private instance : NatId Location where
  fromNat := Location.mk
  toNat := Location.id

private instance : Min Location where
  min a b := if Ord.compare a b == Ordering.lt then a else b

structure Mapping (α β : Type) where
  inputStart : α
  outputStart : β
  length : Nat
  deriving Repr

structure Mappings (α β : Type) where
  mappings : List $ Mapping α β
  deriving Repr

private def Mapping.apply? {α β : Type} [NatId α] [NatId β] (mapping : Mapping α β) (input : α) : Option β :=
  let input := NatId.toNat input
  let fromStart := NatId.toNat mapping.inputStart
  let toStart := NatId.toNat mapping.outputStart
  if input ≥ fromStart ∧ input < fromStart + mapping.length then
    some $ NatId.fromNat $ toStart + input - fromStart
  else
    none

private def Mappings.apply {α β : Type} [NatId α] [NatId β] (mappings : Mappings α β) (input : α) : β :=
  let applied := mappings.mappings.findSome? $ flip Mapping.apply? input
  applied.getD $ NatId.fromNat $ NatId.toNat input

structure Almanach where
  seedsToSoil : Mappings Seed Soil
  soilToFertilizer : Mappings Soil Fertilizer
  fertilizerToWater : Mappings Fertilizer Water
  waterToLight : Mappings Water Light
  lightToTemperature : Mappings Light Temperature
  temperatureToHumidity : Mappings Temperature Humidity
  humidityToLocation : Mappings Humidity Location
  deriving Repr

private def parseSeeds (input : String) : Option (List Seed) :=
  if input.startsWith "seeds: " then
    let input := input.drop 7
    let input := String.trim <$> input.split Char.isWhitespace
    let numbers := input.mapM String.toNat?
    List.map NatId.fromNat <$> numbers
  else
    none

private def parseMapping {α β : Type} [NatId α] [NatId β] (input : String) : Option $ Mapping α β := do
  let input := String.trim <$> input.split Char.isWhitespace
  let nums ← input.mapM String.toNat?
  match nums with
  | [a,b,c] => some $ {inputStart := NatId.fromNat b, outputStart := NatId.fromNat a, length := c}
  | _ => none

private def parseMappings (α β : Type) [NatId α] [NatId β] (input : String) (header : String) : Option $ Mappings α β :=
  if input.startsWith header then
    let lines := String.trim <$> input.splitOn "\n" |> List.drop 1 |> List.filter (not ∘ String.isEmpty)
    let mappings := lines.mapM parseMapping
    Mappings.mk <$> mappings
  else
   none

def parse (input : String) : Option ((List Seed) × Almanach) := do
  let blocks := input.splitOn "\n\n" |> List.filter (not ∘ String.isEmpty)
  let blocks := String.trim <$> blocks
  if let [seeds, seedToSoil, soilToFertilizer, fertilizerToWater, waterToLight, lightToTemperature, temperatureToHumidity, humidityToLocation] := blocks then
    let seeds ← parseSeeds seeds
    let seedToSoil ← parseMappings Seed Soil seedToSoil "seed-to-soil map:"
    let soilToFertilizer ← parseMappings Soil Fertilizer soilToFertilizer "soil-to-fertilizer map:"
    let fertilizerToWater ← parseMappings Fertilizer Water fertilizerToWater "fertilizer-to-water map:"
    let waterToLight ← parseMappings Water Light waterToLight "water-to-light map:"
    let lightToTemperature ← parseMappings Light Temperature lightToTemperature "light-to-temperature map:"
    let temperatureToHumidity ← parseMappings Temperature Humidity temperatureToHumidity "temperature-to-humidity map:"
    let humidityToLocation ← parseMappings Humidity Location humidityToLocation "humidity-to-location map:"
    (seeds, {
      seedsToSoil := seedToSoil
      soilToFertilizer := soilToFertilizer
      fertilizerToWater := fertilizerToWater
      waterToLight := waterToLight
      lightToTemperature := lightToTemperature
      temperatureToHumidity := temperatureToHumidity
      humidityToLocation := humidityToLocation
    : Almanach})
  else
    none

def part1 (input : ((List Seed) × Almanach)) : Option Nat :=
  let a := input.snd
  let seedToLocation  := a.humidityToLocation.apply
                      ∘ a.temperatureToHumidity.apply
                      ∘ a.lightToTemperature.apply
                      ∘ a.waterToLight.apply
                      ∘ a.fertilizerToWater.apply
                      ∘ a.soilToFertilizer.apply
                      ∘ a.seedsToSoil.apply
  let locations := input.fst.map seedToLocation
  NatId.toNat <$> locations.minimum?


-- Part 2 seems unmanageable by brute force.
-- So, let's rather combine the mappings in a smart way, and then invert them.
-- Then we can do binary search if any seed is in the domain of the combined mapping.
-- if not, the answer is just the smallest seed.

private def Mappings.combine {α β γ : Type} [NatId α] [NatId β] [NatId γ] (a : Mappings α β) (b : Mappings β γ) : Mappings α γ :=
  -- the combined mapping contains all ranges in b that aren't "shielded" by ranges of a.
  -- then it contains all ranges of a, but their codomain needs to be checked if it overlaps with
  --    any ranges in b, and if yes, those ranges need to be split accordingly.
  let domain := λ {δ ε : Type} [NatId δ] [NatId ε] (e :Mapping δ ε) ↦ (NatId.toNat e.inputStart, NatId.toNat e.inputStart + e.length)
  let codomain := λ {δ ε : Type} [NatId δ] [NatId ε] (e :Mapping δ ε) ↦ (NatId.toNat e.outputStart, NatId.toNat e.outputStart + e.length)
  let unshieldedB : List (Mapping α γ) := b.mappings.bind λ bm ↦
    let bmd := domain bm
    let bmcd := codomain bm
    let shielded := a.mappings.filterMap λ am ↦
      let amd := domain am
      let s := Nat.max amd.fst bmd.fst
      let e := Nat.min amd.snd bmd.snd
      if e > s then some (s,e) else none
    -- add a range before and after to shielded, then we can take those between
    -- we anyhow need to sort shielded, sooo
    let shielded := (bmd.fst, bmd.fst) :: (bmd.snd, bmd.snd) :: shielded
    let shielded := shielded.quicksortBy (·.fst < ·.fst)
    let rs := shielded.zip (shielded.drop 1)
    let rs : List (Nat × Nat):= rs.map λ x ↦ (x.fst.snd, x.snd.fst)
    let rs := rs.filter λ l ↦ l.snd > l.fst -- skip emtpy, they are just noise
    rs.map λ (x : Nat × Nat) ↦
      let is : α := NatId.fromNat x.fst
      let os : γ := NatId.fromNat $ bmcd.fst + x.fst - bmd.fst
      let l : Nat := (x.snd - x.fst)
      { inputStart := is, outputStart := os, length := l}
  --TODO: Unify the onlyAffectedByA and affectedByBoth computations.
  let onlyAffectedByA : List (Mapping α γ) := a.mappings.bind λ am ↦
    let amd := domain am
    let amcd := codomain am
    let overlapping := b.mappings.filterMap λ bm ↦
      let bmd := domain bm
      let s := Nat.max amcd.fst bmd.fst
      let e := Nat.min amcd.snd bmd.snd
      if e > s then some (s,e) else none
    -- overlapping is in the **codomain** of a. Transform to domain:
    let overlapping := overlapping.map λ p ↦ (p.fst + amd.fst - amcd.fst, p.snd + amd.fst - amcd.fst)
    let overlapping := (amd.fst, amd.fst) :: (amd.snd, amd.snd) :: overlapping
    let overlapping := overlapping.quicksortBy (·.fst < ·.fst)
    let rs := overlapping.zip (overlapping.drop 1)
    let rs : List (Nat × Nat):= rs.map λ x ↦ (x.fst.snd, x.snd.fst)
    let rs := rs.filter λ l ↦ l.snd > l.fst
    rs.map λ (x : Nat × Nat) ↦
      let is : α := NatId.fromNat x.fst
      let os : γ := NatId.fromNat $ amcd.fst + x.fst - amd.fst
      let l : Nat := (x.snd - x.fst)
      { inputStart := is, outputStart := os, length := l}
  let affectedByBoth : List (Mapping α γ) := sorry
  sorry


open DayPart
instance : Parse ⟨5, by simp⟩ (ι := (List Seed) × Almanach) where
  parse := parse

instance : Part ⟨5, _⟩ Parts.One (ι := (List Seed) × Almanach) (ρ := Nat) where
  run := part1


private def TestInput := "seeds: 79 14 55 13

seed-to-soil map:
50 98 2
52 50 48

soil-to-fertilizer map:
0 15 37
37 52 2
39 0 15

fertilizer-to-water map:
49 53 8
0 11 42
42 0 7
57 7 4

water-to-light map:
88 18 7
18 25 70

light-to-temperature map:
45 77 23
81 45 19
68 64 13

temperature-to-humidity map:
0 69 1
1 0 69

humidity-to-location map:
60 56 37
56 93 4
"

#eval parse TestInput
#eval parse TestInput >>= part1
