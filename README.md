# General-Valued Constraint Satisfaction Problems

This is a playground for experiments preceding our contribution to the [Lean 4](https://github.com/leanprover/lean4) version of [Mathlib](https://github.com/leanprover-community/mathlib4).

[Permalink to the definition of VCSP in Mathlib](https://github.com/leanprover-community/mathlib4/blob/3e51ad145c59d7e879943907172a6c5a89d6420c/Mathlib/Combinatorics/Optimization/ValuedCSP.lean#L39)

Our long-term goal is to formalize the dichotomy for fixed-template finite-valued constraint satisfaction problems [Thapper, Živný, Kolmogorov] while exploring potential generalizations (infinite domains, partially ordered codomains, and more).

## Results

### Main results (please see the definitions in [ValuedCSP.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/Optimization/ValuedCSP.lean) first)

* [If a VCSP template over LinearOrderedCancelAddCommMonoid can express MaxCut, it cannot have any commutative fractional polymorphism.](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/Hardness.lean#L70)
* [Basic LP relaxation for VCSP over any OrderedRing of CharZero is valid.](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/LinearRelaxation.lean#L268)
* [If a VCSP template over ℚ has symmetric fractional polymorphisms of all arities, then Basic LP relaxation is tight.](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/LinearRelaxationAndSFP.lean#L398)

### Farkas-like theorems (can be use independently of the VCSP)

* [David Bartl's version](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/FarkasBartl.lean#L192)
* [The most general version](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/FarkasBartl.lean#L252)
* [Equality version](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/FarkasBasic.lean#L102)
* [Inequality version](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/FarkasBasic.lean#L107)
* [Special version for extended rationals](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/FarkasSpecial.lean#L282)
* [Strong LP duality](https://github.com/madvorak/vcsp/blob/a96896872daccd490913d37e159a093a6dde50cb/VCSP/LinearProgramming.lean#L122) (only the most basic version)

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
