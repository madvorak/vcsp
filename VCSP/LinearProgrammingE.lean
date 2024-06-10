import Mathlib.Algebra.Order.Pi
import VCSP.FarkasSpecial


/-- Linear program in the standard form. Variables are of type `J`. Conditions are indexed by type `I`. -/
structure ExtendedLP (I J : Type*) where
  /-- The left-hand-side matrix -/
  A : Matrix I J ℚ∞
  /-- The right-hand-side vector -/
  b : I → ℚ∞
  /-- The objective function coefficients -/
  c : J → ℚ∞

open scoped Matrix
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution (P : ExtendedLP I J) (x : J → ℚ) : Prop :=
  P.A ₘ* x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `v`. -/
def ExtendedLP.Reaches (P : ExtendedLP I J) (v : ℚ∞) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x ∧ P.c ᵥ⬝ x = v

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x -- Does it even mean anything? What if `P.c ᵥ⬝ x = ⊥` here?

/-- Linear program `P` is bounded by `r` iff all values reached by `P` are less or equal to `r`. -/
def ExtendedLP.IsBoundedBy (P : ExtendedLP I J) (r : ℚ∞) : Prop :=
  ∀ p : ℚ∞, P.Reaches p → p ≤ r

/-- Linear program `P` is bounded iff there exists a finite upper bound on values reached by `P`. -/
def ExtendedLP.IsBounded (P : ExtendedLP I J) : Prop :=
  ∃ r : ℚ, P.IsBoundedBy r.toERat

/-- Note that `ExtendedLP.dualize` is significantly different from `StandardLP.dualize`;
    here we keep maximizing but the sign is flipped. -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨-P.Aᵀ, -P.c, -P.b⟩

lemma ExtendedLP.dualize_dualize (P : ExtendedLP I J) : P.dualize.dualize = P := by
  obtain ⟨A, b, c⟩ := P
  simp [ExtendedLP.dualize, ←Matrix.ext_iff]

open Classical

noncomputable def ExtendedLP.optimum (P : ExtendedLP I J) : Option ℚ∞ :=
  if P.IsFeasible then
    if P.IsBounded then
      if hr : ∃ r : ℚ, P.Reaches r.toERat ∧ P.IsBoundedBy r.toERat then
        hr.choose -- the "maximum"
      else
        none -- invalid "finite" value
    else
      some ⊤
  else
    some ⊥
