# General-Valued Constraint Satisfaction Problems

This is a playground for experiments preceding our contribution to the [Lean 4](https://github.com/leanprover/lean4) version of [Mathlib](https://github.com/leanprover-community/mathlib4).

[Permalink to the definition of VCSP in Mathlib](https://github.com/leanprover-community/mathlib4/blob/3e51ad145c59d7e879943907172a6c5a89d6420c/Mathlib/Combinatorics/Optimization/ValuedCSP.lean#L39)

Our long-term goal is to formalize the dichotomy for fixed-template finite-valued constraint satisfaction problems [Thapper, Živný, Kolmogorov] while exploring potential generalizations (infinite domains, partially ordered codomains, and more).

## Results

### Main results (please see the definitions in [ValuedCSP.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/Optimization/ValuedCSP.lean) first)

* [If a VCSP template over LinearOrderedCancelAddCommMonoid can express MaxCut, it cannot have any commutative fractional polymorphism.](https://github.com/madvorak/vcsp/blob/3488402c0494233c2498b6914d14e54b02a20909/VCSP/Hardness.lean#L70)
* [Basic LP relaxation for VCSP over any OrderedRing of CharZero is valid.](https://github.com/madvorak/vcsp/blob/3488402c0494233c2498b6914d14e54b02a20909/VCSP/LinearRelaxation.lean#L268)
* [If a VCSP template over ℚ has symmetric fractional polymorphisms of all arities, then Basic LP relaxation is tight.](https://github.com/madvorak/vcsp/blob/3488402c0494233c2498b6914d14e54b02a20909/VCSP/LinearRelaxationAndSFP.lean#L398)

### Farkas-like theorems (can be use independently of the VCSP)

* [David Bartl's version](https://github.com/madvorak/vcsp/blob/3b9c0fe55ebebf2155536b3363666ac0baffeca5/VCSP/FarkasBartl.lean#L197)
* [Our most general version](https://github.com/madvorak/vcsp/blob/3b9c0fe55ebebf2155536b3363666ac0baffeca5/VCSP/FarkasBartl.lean#L220)
* [Equality version](https://github.com/madvorak/vcsp/blob/3b9c0fe55ebebf2155536b3363666ac0baffeca5/VCSP/FarkasBasic.lean#L94)
* [Inequality version](https://github.com/madvorak/vcsp/blob/3b9c0fe55ebebf2155536b3363666ac0baffeca5/VCSP/FarkasBasic.lean#L99)
* [Special version for extended rationals](https://github.com/madvorak/vcsp/blob/3b9c0fe55ebebf2155536b3363666ac0baffeca5/VCSP/FarkasSpecial.lean#L252)
* [Strong LP duality for matrices over LinearOrderedField](https://github.com/madvorak/vcsp/blob/3b9c0fe55ebebf2155536b3363666ac0baffeca5/VCSP/LinearProgramming.lean#L133)
* [Strong LP duality for matrices over extended rationals](https://github.com/madvorak/vcsp/blob/3b9c0fe55ebebf2155536b3363666ac0baffeca5/VCSP/LinearProgrammingE.lean#L1009)

## Mathlib contributions that stem from this project

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
* https://github.com/leanprover-community/mathlib4/pull/13167

### Proposals for Linear Programming (these PRs are incompatible with each other)

* https://github.com/leanprover-community/mathlib4/pull/7386
* https://github.com/leanprover-community/mathlib4/pull/9693
* https://github.com/leanprover-community/mathlib4/pull/10026
* https://github.com/leanprover-community/mathlib4/pull/10159
