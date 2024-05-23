import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Archimedean -- TODO delete after generalizing `StandardLP.strongDuality`
import VCSP.FarkasBartl

open scoped Matrix


section inequalities_only

/-!

# Linear programming

We define linear programs over an `OrderedSemiring R` in the standard matrix form.

## Main definitions
 * `StandardLP` defines a linear program in the standard form
    (maximize `cᵀx` such that `A x ≤ b` and `x ≥ 0`).
 * `StandardLP.IsSolution` tells if given vector is a solution satisfying given standard LP.
 * `StandardLP.IsFeasible` tells if given standard LP has any solution.
 * `StandardLP.Reaches` tells if given value can be obtained as a cost of any solution of given
    standard LP.
 * `StandardLP.dual` defines a dual problem to given standard LP.

## Main results

* `StandardLP.weakDuality`: The weak duality theorem (`cᵀx` such that `A x ≤ b` and `x ≥ 0` is
   always less or equal to `bᵀy` such that `Aᵀ y ≥ c` and `y ≥ 0`).
* `StandardLP.strongDuality`: TODO!

-/

/-- Linear program in the standard form. Variables are of type `n`. Conditions are indexed by type `m`. -/
structure StandardLP (n m R : Type*) [Fintype n] [Fintype m] [OrderedSemiring R] where
  /-- Matrix of coefficients -/
  A : Matrix m n R
  /-- Right-hand side -/
  b : m → R
  /-- Objective function coefficients -/
  c : n → R

variable {n m R : Type*} [Fintype n] [Fintype m]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
multiplication by matrix `A` from the left yields a vector whose all entries are less or equal to
corresponding entries of the vector `b`. -/
def StandardLP.IsSolution [OrderedSemiring R] (P : StandardLP n m R) (x : n → R) : Prop :=
  P.A *ᵥ x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there is a vector `x` that is a solution to `P`. -/
def StandardLP.IsFeasible [OrderedSemiring R] (P : StandardLP n m R) : Prop :=
  ∃ x : n → R, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
when its entries are elementwise multiplied by the costs (given by the vector `c`) and summed up,
the result is the value `v`. -/
def StandardLP.Reaches [OrderedSemiring R] (P : StandardLP n m R) (v : R) : Prop :=
  ∃ x : n → R, P.IsSolution x ∧ P.c ⬝ᵥ x = v

/-- Dual linear program to given linear program `P` in the standard form.
The matrix gets transposed and its values flip signs.
The original cost function gets flipped signs as well and becomes the new righ-hand side vector.
The original righ-hand side vector becomes the new vector of objective function coefficients. -/
def StandardLP.dual [OrderedRing R] (P : StandardLP m n R) : StandardLP n m R :=
  ⟨-P.Aᵀ, -P.c, P.b⟩

/-- Objective values reached by linear program `P` are all less or equal to all objective values
reached by the dual of `P`. -/
theorem StandardLP.weakDuality [OrderedCommRing R] {P : StandardLP n m R}
    {p : R} (hP : P.Reaches p) {q : R} (hD : P.dual.Reaches q) :
    p ≤ q := by
  obtain ⟨x, ⟨hxb, h0x⟩, rfl⟩ := hP
  obtain ⟨y, ⟨hyc, h0y⟩, rfl⟩ := hD
  dsimp only [StandardLP.dual] at hyc ⊢
  have hy : P.A *ᵥ x ⬝ᵥ y ≤ P.b ⬝ᵥ y
  · exact Matrix.dotProduct_le_dotProduct_of_nonneg_right hxb h0y
  have hx : P.c ⬝ᵥ x ≤ P.Aᵀ *ᵥ y ⬝ᵥ x
  · rw [←neg_le_neg_iff, ←Matrix.neg_dotProduct, ←Matrix.neg_dotProduct, ←Matrix.neg_mulVec]
    exact Matrix.dotProduct_le_dotProduct_of_nonneg_right hyc h0x
  rw [Matrix.dotProduct_comm (P.Aᵀ *ᵥ y), Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at hx
  exact hx.trans hy

theorem StandardLP.strongDuality [DecidableEq m] --[LinearOrderedField R] [InfSet R] {P : StandardLP m n R}
    {P : StandardLP m n ℝ}
    (hP : P.IsFeasible) (hD : P.dual.IsFeasible) :
  --∃ r : R, P.Reaches r ∧ P.dual.Reaches r := by
    ∃ r : ℝ, P.Reaches r ∧ P.dual.Reaches r := by
  let r : ℝ := sInf P.Reaches
  use r
  have hPr : P.Reaches r
  · show sInf P.Reaches ∈ setOf P.Reaches
    sorry
    -- We probably have to explicitly provide that `P.Reaches` is an image of a continuous function on a compact set.
    -- Whether we want to use `IsCompact.sInf_mem` or `IsCompact.exists_isMinOn` some nontrivial steps are missing.
  constructor
  · exact hPr
  have farkas := inequalityFarkas (Matrix.fromRows (-P.Aᵀ) (fun _ : Unit => P.b)) (Sum.elim (-P.c) (fun _ : Unit => r))
  have impossibility : ¬(∃ y : m ⊕ Unit → ℝ, 0 ≤ y ∧
      -(Matrix.fromRows (-P.Aᵀ) (fun _ : Unit => P.b))ᵀ *ᵥ y ≤ 0 ∧ Sum.elim (-P.c) (fun _ : Unit => r) ⬝ᵥ y < 0)
  · push_neg
    intro y hy hAby
    have hAby' : (Matrix.fromRows P.Aᵀ (fun _ : Unit => P.b))ᵀ *ᵥ y ≤ 0
    · convert hAby
      sorry -- trivial
    simp [StandardLP.Reaches] at hPr
    obtain ⟨z, ⟨hAbz, hz⟩, hcz⟩ := hPr
    rw [←hcz]
    show 0 ≤ Sum.elim (-P.c) (fun _ : Unit => P.c ⬝ᵥ z) ⬝ᵥ y
    have y₁ : m → ℝ := sorry
    have y₀ : Unit → ℝ := sorry
    suffices : P.c ⬝ᵥ y₁ ≤ (fun _ : Unit => P.c ⬝ᵥ z) ⬝ᵥ y₀
    · sorry -- easy after defining `y₁` and `y₀`
    have y₀₀ : ℝ := sorry
    suffices : P.c ⬝ᵥ y₁ ≤ (P.c ⬝ᵥ z) * y₀₀
    · sorry -- easy after defining `y₀₀`
    have hyz : y₁ = y₀₀ • z
    · sorry -- Does it hold? Something seems to be missing!
    rw [hyz, Matrix.dotProduct_smul, smul_eq_mul, mul_comm]
  simp [impossibility] at farkas
  obtain ⟨x, hx, hAbx⟩ := farkas
  have dual_le : P.dual.A *ᵥ x ≤ P.dual.b
  · intro i
    simpa using hAbx (Sum.inl i)
  refine ⟨x, ⟨dual_le, hx⟩, ?_⟩
  · apply eq_of_le_of_le
    · simpa using hAbx (Sum.inr ())
    · exact StandardLP.weakDuality hPr ⟨x, ⟨dual_le, hx⟩, rfl⟩

end inequalities_only


section equalities_only

/-- Linear program in the canonical form. Variables are of type `n`. Conditions are indexed by type `m`. -/
structure CanonicalLP (n m R : Type*) [Fintype n] [Fintype m] [OrderedSemiring R] where
  /-- Matrix of coefficients -/
  A : Matrix m n R
  /-- Right-hand side -/
  b : m → R
  /-- Objective function coefficients -/
  c : n → R

variable {n m R : Type*} [Fintype n] [Fintype m]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and
its multiplication by matrix `A` from the left yields the vector `b`. -/
def CanonicalLP.IsSolution [OrderedSemiring R] (P : CanonicalLP n m R) (x : n → R) : Prop :=
  P.A *ᵥ x = P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there is a vector `x` that is a solution to `P`. -/
def CanonicalLP.IsFeasible [OrderedSemiring R] (P : CanonicalLP n m R) : Prop :=
  ∃ x : n → R, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
when its entries are elementwise multiplied by the costs (given by the vector `c`) and summed up,
the result is the value `v`. -/
def CanonicalLP.Reaches [OrderedSemiring R] (P : CanonicalLP n m R) (v : R) : Prop :=
  ∃ x : n → R, P.IsSolution x ∧ P.c ⬝ᵥ x = v

def CanonicalLP.toStandardLP [OrderedRing R] (P : CanonicalLP n m R) : StandardLP n (m ⊕ m) R :=
  StandardLP.mk
    (Matrix.fromRows P.A (-P.A))
    (Sum.elim P.b (-P.b))
    P.c

lemma CanonicalLP.toStandardLP_isSolution_iff [OrderedRing R] (P : CanonicalLP n m R) (x : n → R) :
    P.toStandardLP.IsSolution x ↔ P.IsSolution x := by
  constructor
  · intro hyp
    simp only [StandardLP.IsSolution, CanonicalLP.toStandardLP, Matrix.fromRows_mulVec] at hyp
    rw [sumElim_le_sumElim_iff] at hyp
    obtain ⟨⟨ineqPos, ineqNeg⟩, nonneg⟩ := hyp
    constructor
    · apply eq_of_le_of_le ineqPos
      intro i
      have almost : -((P.A *ᵥ x) i) ≤ -(P.b i)
      · specialize ineqNeg i
        rwa [Matrix.neg_mulVec] at ineqNeg
      rwa [neg_le_neg_iff] at almost
    · exact nonneg
  · intro hyp
    unfold CanonicalLP.toStandardLP
    unfold StandardLP.IsSolution
    obtain ⟨equ, nonneg⟩ := hyp
    constructor
    · rw [Matrix.fromRows_mulVec, sumElim_le_sumElim_iff]
      constructor
      · exact equ.le
      rw [Matrix.neg_mulVec]
      intro i
      show -((P.A *ᵥ x) i) ≤ -(P.b i)
      rw [neg_le_neg_iff]
      exact equ.symm.le i
    · exact nonneg

lemma CanonicalLP.toStandardLP_isFeasible_iff [OrderedRing R] (P : CanonicalLP n m R) :
    P.toStandardLP.IsFeasible ↔ P.IsFeasible := by
  constructor <;> intro ⟨x, hx⟩ <;> use x
  · rwa [CanonicalLP.toStandardLP_isSolution_iff] at hx
  · rwa [CanonicalLP.toStandardLP_isSolution_iff]

lemma CanonicalLP.toStandardLP_reaches_iff [OrderedRing R] (P : CanonicalLP n m R) (v : R) :
    P.toStandardLP.Reaches v ↔ P.Reaches v := by
  constructor <;> intro ⟨x, hx⟩ <;> use x
  · rwa [CanonicalLP.toStandardLP_isSolution_iff] at hx
  · rwa [CanonicalLP.toStandardLP_isSolution_iff]

end equalities_only
