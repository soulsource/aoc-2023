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

private def Mapping.overlap {α β : Type} [NatId α] [NatId β] (a : Mapping α β) (b : Mapping α β) : Bool :=
  let aStart := NatId.toNat $ a.inputStart
  let aEnd := aStart + a.length
  let bStart := NatId.toNat $ b.inputStart
  let bEnd := bStart + b.length
  (bStart ≥ aStart && bStart < aEnd)
   || (bEnd ≥ aStart && bEnd < aEnd)
   || (aStart ≥ bStart && aStart < bEnd)
   || (aEnd ≥ bStart && aEnd < bEnd)

private def parseMappings (α β : Type) [NatId α] [NatId β] (input : String) (header : String) : Option $ Mappings α β :=
  if input.startsWith header then
    let lines := String.trim <$> input.splitOn "\n" |> List.drop 1 |> List.filter (not ∘ String.isEmpty)
    let mappings := lines.mapM parseMapping
    let rec overlapHelper := λ (a : List $ Mapping α β) ↦ match a with
      | [] => false
      | a :: as => as.any (λ b ↦ a.overlap b) || overlapHelper as
    let mappings := mappings.filter overlapHelper --make sure no ranges overlap. That would be faulty
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
-- So, let's rather combine the mappings in a smart way, such that we don't need to brute-force
-- anything (okay, nearly)

private structure Mapping2 (α β : Type) where
  start : α --okay, next time I do this, I'll encode end and offset, not start and offset...
  offset : Int
  deriving Repr

private structure Mappings2 (α β : Type) where
  mappings : List $ Mapping2 α β
  deriving Repr

private def Mappings2.fromMappings {α β : Type} [NatId α] [NatId β] [Ord α] (input : Mappings α β) : Mappings2 α β :=
  let input := input.mappings.quicksortBy λ a b ↦ (Ord.compare a.inputStart b.inputStart == Ordering.lt)
  let rec helper := λ
    | [] => []
    | a :: [] => [{ start:= a.inputStart, offset := (NatId.toNat a.outputStart) - (NatId.toNat a.inputStart)},
                 {start:= NatId.fromNat (NatId.toNat a.inputStart + a.length), offset := 0}]
    | a :: b :: as => if (NatId.toNat b.inputStart) != (NatId.toNat a.inputStart + a.length) then
                        { start:= a.inputStart, offset := (NatId.toNat a.outputStart) - (NatId.toNat a.inputStart)}
                        :: { start:= NatId.fromNat (NatId.toNat a.inputStart + a.length), offset := 0}
                        :: helper (b :: as)
                      else
                        { start:= a.inputStart, offset := (NatId.toNat a.outputStart) - (NatId.toNat a.inputStart)}
                        :: helper (b :: as)
  let result := match input with
    | [] => []
    | a :: _ =>  if NatId.toNat a.inputStart != 0 then
                    { start:= NatId.fromNat 0, offset := 0 : Mapping2 α β} :: helper input
                  else
                    helper input
  Mappings2.mk result

private def Mappings2.apply (α β : Type) [NatId α] [NatId β] [Ord α] (mapping : Mappings2 α β) (value : α) : β :=
  let rec findOffsetHelper := λ
    | [] => 0
    | a :: [] => a.offset
    | a :: b :: as => if (Ord.compare value b.start == Ordering.lt) then a.offset else findOffsetHelper (b :: as)
  let offset : Int := findOffsetHelper mapping.mappings
  let result : Int := (NatId.toNat value + offset)
  NatId.fromNat result.toNat

private def Mappings2.combine {α β γ : Type} [NatId α] [NatId β] [NatId γ] (a : Mappings2 α β) (b : Mappings2 β γ) : Mappings2 α γ :=
  -- at this point, let's just go integer
  let a : List (Int × Int) := a.mappings.map λ m ↦ (NatId.toNat m.start, m.offset)
  let b : List (Int × Int):= b.mappings.map λ m ↦ (NatId.toNat m.start, m.offset)
  let rec findOffsetHelper := λ (list : List (Int × Int)) (value : Int) ↦ match list with
    | [] => 0
    | a :: [] => a.snd
    | a :: b :: as => if (value < b.fst) then a.snd else findOffsetHelper (b :: as) value

  let rec helper := λ
    | [] => b
    | a :: [] =>
      let bOffsetAtA := findOffsetHelper b (a.fst + a.snd)
      let bRemainder := b.dropWhile (λ (bb : Int × Int) ↦ a.fst + a.snd > bb.fst)
      match bRemainder with
        | [] => [(a.fst, a.snd + bOffsetAtA)]
        | b :: _ =>  if b.fst - a.snd == a.fst then
                        bRemainder.map λ (b : Int × Int) ↦ (b.fst - a.snd, a.snd + b.snd)
                      else
                        (a.fst, a.snd + bOffsetAtA) :: bRemainder.map λ (b : Int × Int) ↦ (b.fst - a.snd, a.snd + b.snd)
    | a :: aa :: as =>
      let bOffsetAtA := findOffsetHelper b (a.fst + a.snd)
      let relevantBs := b.filter (λ (bb : Int × Int) ↦ a.fst + a.snd ≤ bb.fst && aa.fst + a.snd > bb.fst)
      match relevantBs with
        | [] => (a.fst, a.snd + bOffsetAtA) :: (helper (aa :: as))
        | b :: _ =>  if b.fst - a.snd == a.fst then
                        (relevantBs.map λ (b : Int × Int) ↦ (b.fst - a.snd, a.snd + b.snd))
                        ++ helper (aa :: as)
                      else
                        (a.fst, a.snd + bOffsetAtA) :: (relevantBs.map λ (b : Int × Int) ↦ (b.fst - a.snd, a.snd + b.snd))
                        ++ helper (aa :: as)
  let result := helper a
  Mappings2.mk $ result.map λ p ↦ { start := NatId.fromNat p.fst.toNat, offset := p.snd : Mapping2 α γ}

-- Unused, left here for reference
private def part1_2 (input : ((List Seed) × Almanach)) : Option Nat :=
  let a := input.snd
  let seedsToFertilizer := (Mappings2.fromMappings a.seedsToSoil).combine (Mappings2.fromMappings a.soilToFertilizer)
  let seedsToWater := seedsToFertilizer.combine  (Mappings2.fromMappings a.fertilizerToWater)
  let seedsToLight := seedsToWater.combine (Mappings2.fromMappings a.waterToLight)
  let seedsToTemperature := seedsToLight.combine (Mappings2.fromMappings a.lightToTemperature)
  let seedsToHumidity := seedsToTemperature.combine (Mappings2.fromMappings a.temperatureToHumidity)
  let seedsToLocation := seedsToHumidity.combine (Mappings2.fromMappings a.humidityToLocation)
  let seedToLocation  := seedsToLocation.apply
  let locations := input.fst.map seedToLocation
  NatId.toNat <$> locations.minimum?

private structure SeedRange where
  start : Seed
  ending : Seed
  deriving Repr

private def SeedRange.fromList (input : List Seed) : List SeedRange :=
  let rec helper : List Seed → List SeedRange := λ
    | [] => []
    | _ :: [] => []
    | a :: b :: as => { start := a, ending := Seed.mk $ b.id + a.id} :: SeedRange.fromList as
  (helper input).quicksortBy λ a b ↦ a.start.id < b.start.id

private def SeedRange.findSmallestSeedAbove (seedRanges : List SeedRange) (value : Seed) : Option Seed :=
  -- two options: If the value is inside a seedRange, the value itself is the result
  --              If not, the start of the first seedRange above the value is the result
  let rangeContains := λ r ↦ (Ord.compare r.start value != Ordering.gt) && (Ord.compare r.ending value == Ordering.gt)
  let rec helper := λ
  | [] => none
  | r :: rs =>  if rangeContains r then
                  some value
                else
                  if Ord.compare r.start value == Ordering.gt then
                    r.start
                  else
                    helper rs
  helper seedRanges

def part2 (input : ((List Seed) × Almanach)) : Option Nat :=
  let a := input.snd
  let seedToLocation := Mappings2.fromMappings a.seedsToSoil
    |> flip Mappings2.combine (Mappings2.fromMappings a.soilToFertilizer)
    |> flip Mappings2.combine (Mappings2.fromMappings a.fertilizerToWater)
    |> flip Mappings2.combine (Mappings2.fromMappings a.waterToLight)
    |> flip Mappings2.combine (Mappings2.fromMappings a.lightToTemperature)
    |> flip Mappings2.combine (Mappings2.fromMappings a.temperatureToHumidity)
    |> flip Mappings2.combine (Mappings2.fromMappings a.humidityToLocation)

  let seedRanges := SeedRange.fromList input.fst

  let potentialSeeds := seedToLocation.mappings.filterMap λ m ↦
    (SeedRange.findSmallestSeedAbove seedRanges m.start) -- could filter by range end, but who cares?
  let locations := potentialSeeds.map seedToLocation.apply
  NatId.toNat <$> locations.minimum?

open DayPart
instance : Parse ⟨5, by simp⟩ (ι := (List Seed) × Almanach) where
  parse := parse

instance : Part ⟨5, _⟩ Parts.One (ι := (List Seed) × Almanach) (ρ := Nat) where
  run := part1

instance : Part ⟨5, _⟩ Parts.Two (ι := (List Seed) × Almanach) (ρ := Nat) where
  run := part2


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

-- #eval parse TestInput
-- #eval parse TestInput >>= λ a ↦ some $ SeedRange.fromList a.fst
-- #eval (parse TestInput) >>= λ a ↦ some $ Mappings2.fromMappings a.snd.soilToFertilizer
-- #eval parse TestInput >>= part1
-- #eval parse TestInput >>= part1_2
-- #eval parse TestInput >>= part2
