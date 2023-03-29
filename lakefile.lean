import Lake
open Lake DSL

package «smt2_interface» {
  srcDir := "src"
  -- add package configuration options here
}

@[default_target]
lean_lib «Smt2» {
  -- roots := #[`Smt2]
  -- add library configuration options here
}
