import Lake
open Lake DSL

package vcsp {
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib VCSP {
  globs := #[.submodules `VCSP]
  moreLeanArgs := #["-DautoImplicit=false"]
}
