import Lake
open Lake DSL

package vcsp {
  moreServerArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «VCSP» {
  globs := #[.submodules `VCSP] 
  moreLeanArgs := #["-DautoImplicit=false"]
}
