import Lake
open Lake DSL

package «LeanearTemporalLogic» where
  -- add package configuration options here

lean_lib «LeanearTemporalLogic» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.18.0-rc1"

@[default_target]
lean_exe «leaneartemporallogic» where
  root := `Main
