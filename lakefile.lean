import Lake
open Lake DSL

package «aoc-2023» where
  -- add package configuration options here

lean_lib «Day1» where
  -- add library configuration options here

lean_lib «Day2» where

lean_lib «Common» where

@[default_target]
lean_exe «aoc-2023» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
