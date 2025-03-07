import Lake
open Lake DSL

package «LeanearTemporalLogic» where
  -- add package configuration options here

lean_lib «LeanearTemporalLogic» where
  -- add library configuration options here

@[default_target]
lean_exe «leaneartemporallogic» where
  root := `Main
