# General-Valued Constraint Satisfaction Problems

This is a playground for experiments preceding my contribution to Mathlib.

My long-term goal is to formalize the dichotomy for fixed-template finite-valued constraint satisfaction problems [Thapper, Živný, Kolmogorov] while exploring potential generalizations (infinite domains, partially ordered codomains, and more).

## Results

* [If a VCSP template can express MaxCut, it cannot have any commutative fractional polymorphism.](https://github.com/madvorak/vcsp/blob/0c56fa679366db730fa428b82acedd041cb82df9/VCSP/Hardness.lean#L151)
* [Basic LP relaxation for VCSP is valid.](https://github.com/madvorak/vcsp/blob/0c56fa679366db730fa428b82acedd041cb82df9/VCSP/LinearRelaxation.lean#L273)
* [If a VCSP template over rationals has symmetric fractional polymorphisms of all arities, then Basic LP relaxation is tight.](https://github.com/madvorak/vcsp/blob/0c56fa679366db730fa428b82acedd041cb82df9/VCSP/LinearRelaxationAndSFP.lean#L392)

## Mathlib contributions

[ValuedCSP.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/Optimization/ValuedCSP.lean)

### VCSP PRs
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

### Proposals for Linear Programming
* https://github.com/leanprover-community/mathlib4/pull/7386
* https://github.com/leanprover-community/mathlib4/pull/9693
* https://github.com/leanprover-community/mathlib4/pull/10026
* https://github.com/leanprover-community/mathlib4/pull/10159
