import «Common»

namespace Day12

------------------------------------------------------------------------------------

inductive SpringState
| operational
| damaged
| unknown

structure SpringArrangement where
  Mask : List SpringState
  DamagedGroups : List Nat

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



def parse (input : String) : Except ParsingError SpringArrangement :=
  let input := input.toSubstring.trim
  let lines := input.splitOn "\n"
  let lines := lines.filterMap λx ↦
    let r : Substring := x.trim
    (Function.const Unit r) <$> Option.ofBool !r.isEmpty
  if lines.isEmpty then
    Except.error ParsingError.noInput
  else
    let splitLines := lines.map (·.splitOn " ")
    let invalidLines := splitLines.map List.length |> List.filter (· ≠ 2)
    if h : !invalidLines.isEmpty then
      Except.error $ ParsingError.invalidNumberOfBlockSeparators $ invalidLines.head (List.not_empty_iff_size_gt_zero.mp ((Bool.not_eq_true' _).mp h) |> List.ne_nil_of_length_pos)
    else
      --splitLines.mapM
      sorry
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
