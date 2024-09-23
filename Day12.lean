import «Common»

namespace Day12

------------------------------------------------------------------------------------

inductive SpringMask
| operational
| damaged
| unknown

structure SpringArrangement where
  Mask : List SpringMask
  DamagedGroups : List Nat

inductive ParsingError
| unknownSymbolInLeftBlock : Char → ParsingError
| unknownSymbolInRightBlock : Char → ParsingError
| missingBlockSeparator : ParsingError
| noInput : ParsingError
| missingLeftBlock : ParsingError
| missingRightBlock : ParsingError

instance : ToString ParsingError where
  toString := λ
  | .unknownSymbolInLeftBlock c => s!"Unkown character in left part of input: '{c}'. Expected '#', '.' or '?'."
  | .unknownSymbolInRightBlock c => s!"Unknown character in right part of input. '{c}'. Expected either a numeric digit, or ','."
  | .missingBlockSeparator => "An input line is missing a block separator (whitespace)."
  | .noInput => "The input file is empty."
  | .missingLeftBlock => "The left block, which should contain a map of operational ('.') or damaged ('#') springs, or the question mark ('?') is empty."
  | .missingRightBlock => "The right block, which should contain a comma-separted list of numbers, is empty."



def parse (input : String) : Except ParsingError SpringArrangement :=
  sorry
