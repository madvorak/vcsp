import Duality.LinearProgramming


/-- Linear program over an extended linearly ordered field in the canonical form.
    Variables are of type `J`. Conditions are indexed by type `I`. -/
structure CanonicalELP (I J F : Type*) [LinearOrderedField F] where
  /-- The left-hand-side matrix -/
  A : Matrix I J F∞
  /-- The right-hand-side vector -/
  b : I → F∞
  /-- The objective function coefficients -/
  c : J → F∞

open scoped Matrix
variable {I J F : Type*} [Fintype J] [LinearOrderedField F]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and
    multiplication by matrix `A` from the left yields the vector `b`. -/
def CanonicalELP.IsSolution (P : CanonicalELP I J F) (x : J → F≥0) : Prop :=
  P.A ₘ* x = P.b

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`. -/
def CanonicalELP.IsFeasible (P : CanonicalELP I J F) : Prop :=
  ∃ x : J → F≥0, P.IsSolution x

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the coefficients `c` and summed up,
    the result is the value `r`. -/
def CanonicalELP.Reaches (P : CanonicalELP I J F) (r : F∞) : Prop :=
  ∃ x : J → F≥0, P.IsSolution x ∧ P.c ᵥ⬝ x = r
