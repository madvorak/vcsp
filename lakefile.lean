import Lake
open Lake DSL

package vcsp {
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require "madvorak" / "duality" @ git "v3.0.0"

@[default_target]
lean_lib VCSP {
  globs := #[.submodules `VCSP]
}
