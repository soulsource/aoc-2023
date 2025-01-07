import Lake
open Lake DSL

package «aoc-2023» where

lean_lib «Day1» where
lean_lib «Day2» where
lean_lib «Day3» where
lean_lib «Day4» where
lean_lib «Day5» where
lean_lib «Day6» where
lean_lib «Day7» where
lean_lib «Day8» where
lean_lib «Day9» where
lean_lib «Day10» where
lean_lib «Day11» where
lean_lib «Day12» where
lean_lib «Day13» where
lean_lib «Day14» where
lean_lib «Day15» where
lean_lib «Day16» where
lean_lib «Day17» where

lean_lib «Common» where

@[default_target]
lean_exe «aoc-2023» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require BinaryHeap from git
  "https://github.com/soulsource/BinaryHeap"@"fe30e1dc0a0070452edce74331aa3df21a6b8f7c"

require «lean-astar» from git
  "https://github.com/soulsource/lean-astar"@"4cc7ae8a6653402e091d246ed746a0ed45b099dc"
