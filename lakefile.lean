import Lake
open Lake DSL

package vcsp {
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require "madvorak" / "duality" @ git "main"

@[default_target]
lean_lib VCSP {
  globs := #[.submodules `VCSP]
}
