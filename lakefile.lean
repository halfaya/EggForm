import Lake
open Lake DSL

package «eggForm» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «EggForm» {
  -- add any library configuration options here
}
