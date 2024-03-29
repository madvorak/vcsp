import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Have

lemma sumElim_le_sumElim_iff {α β γ : Type*} [LE γ] (u u' : α → γ) (v v' : β → γ) :
    Sum.elim u v ≤ Sum.elim u' v' ↔ u ≤ u' ∧ v ≤ v' := by
  constructor <;> intro hyp
  · constructor
    · intro a
      have hypa := hyp (Sum.inl a)
      rwa [Sum.elim_inl, Sum.elim_inl] at hypa
    · intro b
      have hypb := hyp (Sum.inr b)
      rwa [Sum.elim_inr, Sum.elim_inr] at hypb
  · intro i
    cases i with
    | inl a =>
      rw [Sum.elim_inl, Sum.elim_inl]
      exact hyp.left a
    | inr b =>
      rw [Sum.elim_inr, Sum.elim_inr]
      exact hyp.right b


/-!

# Linear programming

We define linear programs over a `LinearOrderedField K` in the standard matrix form.

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

-/

open scoped Matrix


section inequalities_only

/-- Linear program in the standard form. Variables are of type `n`. Conditions are indexed by type `m`. -/
structure StandardLP (n m K : Type*) [Fintype n] [Fintype m] [LinearOrderedField K] where
  /-- Matrix of coefficients -/
  A : Matrix m n K
  /-- Right-hand side -/
  b : m → K
  /-- Objective function coefficients -/
  c : n → K

variable {n m K : Type*} [Fintype n] [Fintype m] [LinearOrderedField K]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
multiplication by matrix `A` from the left yields a vector whose all entries are less or equal to
corresponding entries of the vector `b`. -/
def StandardLP.IsSolution (P : StandardLP n m K) (x : n → K) : Prop :=
  P.A *ᵥ x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there is a vector `x` that is a solution to `P`. -/
def StandardLP.IsFeasible (P : StandardLP n m K) : Prop :=
  ∃ x : n → K, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
when its entries are elementwise multiplied by the costs (given by the vector `c`) and summed up,
the result is the value `v`. -/
def StandardLP.Reaches (P : StandardLP n m K) (v : K) : Prop :=
  ∃ x : n → K, P.IsSolution x ∧ P.c ⬝ᵥ x = v

/-- Dual linear program to given linear program `P` in the standard form.
The matrix gets transposed and its values flip signs.
The original cost function gets flipped signs as well and becomes the new righ-hand side vector.
The original righ-hand side vector becomes the new vector of objective function coefficients. -/
def StandardLP.dual (P : StandardLP m n K) : StandardLP n m K :=
  ⟨-P.Aᵀ, -P.c, P.b⟩

/-- Objective values reached by linear program `P` are all less or equal to all objective values
reached by the dual of `P`. -/
theorem StandardLP.weakDuality {P : StandardLP n m K}
    {v : K} (hP : P.Reaches v) {w : K} (hD : P.dual.Reaches w) :
    v ≤ w := by
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

end inequalities_only


section equalities_only

/-- Linear program in the canonical form. Variables are of type `n`. Conditions are indexed by type `m`. -/
structure CanonicalLP (n m K : Type*) [Fintype n] [Fintype m] [LinearOrderedField K] where
  /-- Matrix of coefficients -/
  A : Matrix m n K
  /-- Right-hand side -/
  b : m → K
  /-- Objective function coefficients -/
  c : n → K

variable {n m K : Type*} [Fintype n] [Fintype m] [LinearOrderedField K]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and
its multiplication by matrix `A` from the left yields the vector `b`. -/
def CanonicalLP.IsSolution (P : CanonicalLP n m K) (x : n → K) : Prop :=
  P.A *ᵥ x = P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there is a vector `x` that is a solution to `P`. -/
def CanonicalLP.IsFeasible (P : CanonicalLP n m K) : Prop :=
  ∃ x : n → K, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
when its entries are elementwise multiplied by the costs (given by the vector `c`) and summed up,
the result is the value `v`. -/
def CanonicalLP.Reaches (P : CanonicalLP n m K) (v : K) : Prop :=
  ∃ x : n → K, P.IsSolution x ∧ P.c ⬝ᵥ x = v

def CanonicalLP.toStandardLP (P : CanonicalLP n m K) : StandardLP n (m ⊕ m) K :=
  StandardLP.mk
    (Matrix.fromRows P.A (-P.A))
    (Sum.elim P.b (-P.b))
    P.c

lemma CanonicalLP.toStandardLP_isSolution_iff (P : CanonicalLP n m K) (x : n → K) :
    P.toStandardLP.IsSolution x ↔ P.IsSolution x := by
  constructor
  · intro hyp
    simp only [StandardLP.IsSolution, CanonicalLP.toStandardLP, Matrix.fromRows_mulVec] at hyp
    rw [sumElim_le_sumElim_iff] at hyp
    obtain ⟨⟨ineqPos, ineqNeg⟩, nonneg⟩ := hyp
    constructor
    · apply le_antisymm ineqPos
      intro i
      have almost : - ((P.A *ᵥ x) i) ≤ - (P.b i)
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
      show - ((P.A *ᵥ x) i) ≤ - (P.b i)
      rw [neg_le_neg_iff]
      exact equ.symm.le i
    · exact nonneg

lemma CanonicalLP.toStandardLP_isFeasible_iff (P : CanonicalLP n m K) :
    P.toStandardLP.IsFeasible ↔ P.IsFeasible := by
  constructor <;> intro ⟨x, hx⟩ <;> use x
  · rwa [CanonicalLP.toStandardLP_isSolution_iff] at hx
  · rwa [CanonicalLP.toStandardLP_isSolution_iff]

lemma CanonicalLP.toStandardLP_reaches_iff (P : CanonicalLP n m K) (v : K) :
    P.toStandardLP.Reaches v ↔ P.Reaches v := by
  constructor <;> intro ⟨x, hx⟩ <;> use x
  · rwa [CanonicalLP.toStandardLP_isSolution_iff] at hx
  · rwa [CanonicalLP.toStandardLP_isSolution_iff]

end equalities_only
