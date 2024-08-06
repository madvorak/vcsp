import Lake
open Lake DSL

package vcsp {
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require duality from git
  "https://github.com/madvorak/duality.git"

@[default_target]
lean_lib VCSP {
  globs := #[.submodules `VCSP]
  moreLeanArgs := #["-DautoImplicit=false"]
}
