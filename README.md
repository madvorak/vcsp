# General-Valued Constraint Satisfaction Problems

This is a playground for experiments preceding my contribution to Mathlib.

[Permalink](https://github.com/leanprover-community/mathlib4/blob/3e51ad145c59d7e879943907172a6c5a89d6420c/Mathlib/Combinatorics/Optimization/ValuedCSP.lean#L39) to the main definition of VCSP.

My long-term goal is to formalize the dichotomy for fixed-template finite-valued constraint satisfaction problems [Thapper, Živný, Kolmogorov] while exploring potential generalizations (infinite domains, partially ordered codomains, and more).

## Results (please see the definitions in [ValuedCSP.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/Optimization/ValuedCSP.lean) first)

* [If a VCSP template over LinearOrderedCancelAddCommMonoid can express MaxCut, it cannot have any commutative fractional polymorphism.](https://github.com/madvorak/vcsp/blob/0c56fa679366db730fa428b82acedd041cb82df9/VCSP/Hardness.lean#L151)
* [Basic LP relaxation for VCSP over LinearOrderedField is valid.](https://github.com/madvorak/vcsp/blob/0c56fa679366db730fa428b82acedd041cb82df9/VCSP/LinearRelaxation.lean#L273)
* [If a VCSP template over ℚ has symmetric fractional polymorphisms of all arities, then Basic LP relaxation is tight.](https://github.com/madvorak/vcsp/blob/0c56fa679366db730fa428b82acedd041cb82df9/VCSP/LinearRelaxationAndSFP.lean#L392)
* [Farkas-Bartl theorem](https://github.com/madvorak/vcsp/blob/3da0844a11e4128d9011adcd5b4c4867a5528ae2/VCSP/FarkasBartl.lean#L16) implies the [standard](https://github.com/madvorak/vcsp/blob/3da0844a11e4128d9011adcd5b4c4867a5528ae2/VCSP/FarkasBartl.lean#L40) Farkas [versions](https://github.com/madvorak/vcsp/blob/3da0844a11e4128d9011adcd5b4c4867a5528ae2/VCSP/FarkasBartl.lean#L72) and also implies our original [extended Farkas version](https://github.com/madvorak/vcsp/blob/3da0844a11e4128d9011adcd5b4c4867a5528ae2/VCSP/FarkasSpecial.lean#L281) (currently, these Farkas variants are only relative results).

## Mathlib contributions

### Pull requests (these PRs are compatible with each other)

* https://github.com/leanprover-community/mathlib4/pull/7404
* https://github.com/leanprover-community/mathlib4/pull/7893
* https://github.com/leanprover-community/mathlib4/pull/7894
* https://github.com/leanprover-community/mathlib4/pull/8707
* https://github.com/leanprover-community/mathlib4/pull/9072
* https://github.com/leanprover-community/mathlib4/pull/9307
* https://github.com/leanprover-community/mathlib4/pull/9652
* https://github.com/leanprover-community/mathlib4/pull/9838
* https://github.com/leanprover-community/mathlib4/pull/10297
* https://github.com/leanprover-community/mathlib4/pull/10379
* https://github.com/leanprover-community/mathlib4/pull/11689
* https://github.com/leanprover-community/mathlib4/pull/12806
* https://github.com/leanprover-community/mathlib4/pull/12901
* https://github.com/leanprover-community/mathlib4/pull/12903
* https://github.com/leanprover-community/mathlib4/pull/12911

### Proposals for Linear Programming (these PRs are incompatible with each other)

* https://github.com/leanprover-community/mathlib4/pull/7386
* https://github.com/leanprover-community/mathlib4/pull/9693
* https://github.com/leanprover-community/mathlib4/pull/10026
* https://github.com/leanprover-community/mathlib4/pull/10159
