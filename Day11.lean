import «Common»

namespace Day11

inductive Pixel
| void
| galaxy

instance : ToString Pixel where
  toString := λ
  | .void => "."
  | .galaxy => "#"

structure ParseCharError where
  foundChar : Char

instance : ToString ParseCharError where
  toString := λx ↦ s!"Invalid character. Expected '#' or '.', but found {x.foundChar}"

def parseCharacter : Char → Except ParseCharError Pixel
| '.' => Except.ok Pixel.void
| '#' => Except.ok Pixel.galaxy
| foundChar => Except.error {foundChar}

------------------------------------------------------------------------------------------

private def testData := "...#......
.......#..
#.........
..........
......#...
.#........
.........#
..........
.......#..
#...#.....
"

#eval Parsing.RectangularGrid.ofString parseCharacter testData
