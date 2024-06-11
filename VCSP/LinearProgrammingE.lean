import Mathlib.Algebra.Order.Pi
import VCSP.FarkasSpecial


/-- Linear program over `ℚ∞` in the standard form (system of linear inequalities with nonnegative `ℚ` variables).
    Variables are of type `J`. Conditions are indexed by type `I`. -/
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
  P.A ₘ* x ≤ P.b ∧ 0 ≤ x -- Do not refactor `x` to `J → ℚ≥0` even tho it would look nicer here!

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`.
    Linear program `P` is considered feasible even if all solutions yield `⊥` as the objective. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. -/
def ExtendedLP.Reaches (P : ExtendedLP I J) (r : ℚ∞) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x ∧ P.c ᵥ⬝ x = r

/-- Linear program `P` is bounded by `r` iff all values reached by `P` are less or equal to `r`.
    Linear program `P` is always bounded by `⊤` which is allowed by this definition. -/
def ExtendedLP.IsBoundedBy (P : ExtendedLP I J) (r : ℚ∞) : Prop :=
  ∀ p : ℚ∞, P.Reaches p → p ≤ r

open scoped Classical in
/-- Extended notion of "maximum" of LP (covers literally everything). -/
noncomputable def ExtendedLP.optimum (P : ExtendedLP I J) : Option ℚ∞ :=
  if P.IsFeasible then
    if hr : ∃ r : ℚ∞, P.Reaches r ∧ P.IsBoundedBy r then
      hr.choose -- the "maximum" or `some ⊤` (the latter happens iff `P.Reaches ⊤`)
    else
      none -- invalid finite value (if supremum was not reached; later, we prove it cannot happen)
  else
    some ⊥ -- note that `some ⊥` is the maximum of both (all) infeasible LPs and (some) feasible LPs

/-- Note that `ExtendedLP.dualize` is significantly different from `StandardLP.dualize`;
    here we keep maximizing in the dual problem but the sign is flipped;
    as a result, `ExtendedLP.dualize` is involution (good),
    but the strong LP duality can no longer be written as equality (bad). -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨-P.Aᵀ, -P.c, -P.b⟩

lemma ExtendedLP.dualize_dualize (P : ExtendedLP I J) : P.dualize.dualize = P := by
  obtain ⟨A, b, c⟩ := P
  simp [ExtendedLP.dualize, ←Matrix.ext_iff]
