import Mathlib.Algebra.Order.Pi
import VCSP.Basic


/-- Linear program in the canonical form. Variables are of type `J`. Conditions are indexed by type `I`. -/
structure CanonicalLP (I J R : Type*) where
  /-- The left-hand-side matrix -/
  A : Matrix I J R
  /-- The right-hand-side vector -/
  b : I → R
  /-- The objective function coefficients -/
  c : J → R

open scoped Matrix
variable {I J R : Type*} [Fintype J] [OrderedSemiring R]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and
    multiplication by matrix `A` from the left yields the vector `b`. -/
def CanonicalLP.IsSolution (P : CanonicalLP I J R) (x : J → R) : Prop :=
  P.A *ᵥ x = P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`. -/
def CanonicalLP.IsFeasible (P : CanonicalLP I J R) : Prop :=
  ∃ x : J → R, P.IsSolution x

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the coefficients `c` and summed up,
    the result is the value `r`. -/
def CanonicalLP.Reaches (P : CanonicalLP I J R) (r : R) : Prop :=
  ∃ x : J → R, P.IsSolution x ∧ P.c ⬝ᵥ x = r
