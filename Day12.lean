import «Common»
import Lean.Data.HashMap

namespace Day12

------------------------------------------------------------------------------------

inductive SpringState
| operational
| damaged
| unknown
deriving Repr, BEq, Hashable

instance : ToString (List SpringState) where
  toString := λl ↦
    let rec w := λ
    | .operational :: as => "." ++ (w as)
    | .damaged :: as => "#" ++ (w as)
    | .unknown :: as => "?" ++ (w as)
    | [] => ""
  w l


structure SpringArrangement where
  mask : List SpringState
  damagedGroups : List Nat

instance : ToString SpringArrangement where
  toString := λ
  | {mask, damagedGroups} => (inferInstance : ToString (List SpringState)).toString mask ++ " " ++ damagedGroups.toString

inductive ParsingError
| unknownSymbolInLeftBlock : Char → ParsingError
| nonNumericSymbolInRightBlock : Substring → ParsingError
| invalidNumberOfBlockSeparators : Nat → ParsingError
| noInput : ParsingError
| missingLeftBlock : ParsingError
| missingRightBlock : ParsingError

instance : ToString ParsingError where
  toString := λ
  | .unknownSymbolInLeftBlock c => s!"Unkown character in left part of input: '{c}'. Expected '#', '.' or '?'."
  | .nonNumericSymbolInRightBlock s => s!"The right block contained an unknown symbol. Expected ',' or numeric digits. Found {s}"
  | .invalidNumberOfBlockSeparators n => s!"An input line has an unexpected number of whitespace characters. Expected 1, found {n}."
  | .noInput => "The input file is empty."
  | .missingLeftBlock => "The left block, which should contain a map of operational ('.') or damaged ('#') springs, or the question mark ('?') is empty."
  | .missingRightBlock => "The right block, which should contain a comma-separted list of numbers, is empty."



def parse (input : String) : Except ParsingError (List SpringArrangement) :=
  let input := input.toSubstring.trim
  let lines := input.splitOn "\n"
  let lines := lines.filterMap λx ↦
    let r : Substring := x.trim
    (Function.const Unit r) <$> Option.ofBool !r.isEmpty
  if lines.isEmpty then
    Except.error ParsingError.noInput
  else
    lines.mapM λl ↦
      match l.splitOn " " with
      | l :: r :: [] => parseLeftBlock l [] >>= λmask↦ parseRightBlock r <&> λdamagedGroups ↦ {mask, damagedGroups}
      | _ :: [] => .error $ ParsingError.invalidNumberOfBlockSeparators 0
      | l => .error $ ParsingError.invalidNumberOfBlockSeparators (l.length - 1)
where
  parseLeftBlock : Substring → List SpringState → Except ParsingError (List SpringState) := λs p ↦
    if s.isEmpty then
      Except.ok p.reverse
    else
      match parseMaskChar s.front with
      | .error e => .error e
      | .ok v => parseLeftBlock (s.drop 1) $ v :: p
  termination_by s => s.bsize
  decreasing_by
    simp_wf
    rename_i h₁
    apply Substring.drop_bsize_dec _ _ h₁ Nat.one_ne_zero
  parseMaskChar : Char → Except ParsingError SpringState := λ
  | '#' => .ok .damaged
  | '?' => .ok .unknown
  | '.' => .ok .operational
  | c => Except.error $ .unknownSymbolInLeftBlock c
  parseRightBlock : Substring → Except ParsingError (List Nat) := λs ↦
    s.splitOn ","
    |> List.mapM λs ↦ (Substring.toNat? s).toExcept (ParsingError.nonNumericSymbolInRightBlock s)


----------------------------------------------------------------------------------------------------

-- There is probably some nice closed form, but I don't have the brain for that right now.
-- Brute force, it is.

inductive DefiniteSpringState
| operational
| damaged

def canFirstNBeDamaged (states : List SpringState) (n : Nat) : Bool :=
  match n, states with
  | 0, _ => true
  | (_ + 1), [] => false
  | (_ + 1), .operational :: _ => false
  | (nn + 1), _ :: ss => canFirstNBeDamaged ss nn

def canFirstBeOperational : (states : List SpringState) → Bool
| .operational :: _ => true
| .unknown :: _ => true
| _ => false

def mustFirstBeDamaged : (states : List SpringState) → Bool
| .damaged :: _ => true
| _ => false

abbrev PossiblePositionsMemo := Std.HashMap (List SpringState × List Nat) Nat

def countPossiblePositionsWithDamagedMemoized (memo : PossiblePositionsMemo) (remainingSpace : List SpringState) (remainingDamagedGroups : List Nat) (h₁ : remainingDamagedGroups ≠ []) : (PossiblePositionsMemo × Nat) :=
  if h₂ : remainingSpace.isEmpty then
    (memo,0)
  else
    match remainingDamagedGroups with
    | g :: gs =>
      let (memo, fromCurrentPosition) :=
        if canFirstNBeDamaged remainingSpace g then
          if h₃ : gs.isEmpty then
            if (remainingSpace.drop g).any (· == .damaged) then
              (memo, 0)
            else
              (memo, 1)
          else
            let d := (remainingSpace.drop g)
            if canFirstBeOperational d then
              let d := (d.drop 1)
              if let some r := memo.get? (d, gs) then
                (memo,r)
              else
                let (memo, r) :=countPossiblePositionsWithDamagedMemoized memo d gs (List.ne_nil_of_not_empty.mp $ (Bool.not_eq_true _).mp h₃)
                (memo.insert (d, gs) r, r)
            else
              (memo, 0)
        else
          (memo, 0)
      have  : remainingSpace.length > 0 := List.not_empty_iff_size_gt_zero.mp $ (Bool.not_eq_true _).mp h₂
      let (memo, fromOtherPositions) :=
        if mustFirstBeDamaged remainingSpace then
          (memo, 0)
        else
          let remainingSpace := (remainingSpace.drop 1)
          if let some r := memo.get? (remainingSpace, g :: gs) then
            (memo,r)
          else
            let (memo, r) := countPossiblePositionsWithDamagedMemoized memo remainingSpace (g :: gs) h₁
            (memo.insert (remainingSpace, g :: gs) r, r)
      (memo, fromCurrentPosition + fromOtherPositions)
termination_by remainingSpace.length + remainingDamagedGroups.length

def countPossiblePositions (remainingSpace : List SpringState) (remainingDamagedGroups : List Nat) : Nat :=
  if h : remainingDamagedGroups.isEmpty then
    let canAllBeOperational := remainingSpace.all λ
    | .operational | .unknown => true
    | _ => false
    if canAllBeOperational then
      1
    else
      0
  else
    Prod.snd $ countPossiblePositionsWithDamagedMemoized Std.HashMap.empty remainingSpace remainingDamagedGroups (List.ne_nil_of_not_empty.mp $ (Bool.not_eq_true _).mp h)


def part1 (springs : List SpringArrangement) : Nat :=
  let possiblePositions := springs.map λ{mask, damagedGroups} ↦ Task.spawn λ_ ↦ countPossiblePositions mask damagedGroups
  let possiblePositions := possiblePositions.map Task.get
  possiblePositions.foldl (· + ·) 0

----------------------------------------------------------------------------------------------------

def convertInputToDay2 (l : List SpringArrangement) : List SpringArrangement :=
  l.map λ{mask, damagedGroups} ↦ {
    mask := mask ++ [.unknown] ++ mask ++ [.unknown] ++ mask ++ [.unknown] ++ mask ++ [.unknown] ++ mask
    damagedGroups := damagedGroups ++ damagedGroups ++ damagedGroups ++ damagedGroups ++ damagedGroups
  }

def part2 : (springs : List SpringArrangement) → Nat := part1 ∘ convertInputToDay2

----------------------------------------------------------------------------------------------------

open DayPart
instance : Parse ⟨12, by simp⟩ (ι := List SpringArrangement) where
  parse := Except.mapError toString ∘ parse

instance : Part ⟨12,_⟩ Parts.One (ι := List SpringArrangement) (ρ := Nat) where
  run := some ∘ part1

instance : Part ⟨12,_⟩ Parts.Two (ι := List SpringArrangement) (ρ := Nat) where
  run := some ∘ part2

----------------------------------------------------------------------------------------------------

def testData := "???.### 1,1,3
.??..??...?##. 1,1,3
?#?#?#?#?#?#?#? 1,3,1,6
????.#...#... 4,1,1
????.######..#####. 1,6,5
?###???????? 3,2,1"

#eval parse testData <&> part2

def testData2 := "?##?.##???????#??#.. 2,10,1"

#eval parse testData2 <&> part1
