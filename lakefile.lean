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

lean_lib «Common» where

@[default_target]
lean_exe «aoc-2023» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
