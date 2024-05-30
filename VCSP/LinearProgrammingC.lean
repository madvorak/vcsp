import VCSP.LinearProgramming

open scoped Matrix


/-- Linear program in the canonical form. Variables are of type `n`. Conditions are indexed by type `m`. -/
structure CanonicalLP (I J R : Type*) where
  /-- Matrix of coefficients -/
  A : Matrix I J R
  /-- Right-hand side -/
  b : I → R
  /-- Objective function coefficients -/
  c : J → R

variable {I J R : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and
    its multiplication by matrix `A` from the left yields the vector `b`. -/
def CanonicalLP.IsSolution [OrderedSemiring R] (P : CanonicalLP I J R) (x : J → R) : Prop :=
  P.A *ᵥ x = P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there is a vector `x` that is a solution to `P`. -/
def CanonicalLP.IsFeasible [OrderedSemiring R] (P : CanonicalLP I J R) : Prop :=
  ∃ x : J → R, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the costs (given by the vector `c`) and summed up,
    the result is the value `v`. -/
def CanonicalLP.Reaches [OrderedSemiring R] (P : CanonicalLP I J R) (v : R) : Prop :=
  ∃ x : J → R, P.IsSolution x ∧ P.c ⬝ᵥ x = v

def CanonicalLP.toStandardLP [OrderedRing R] (P : CanonicalLP I J R) : StandardLP (I ⊕ I) J R :=
  StandardLP.mk
    (Matrix.fromRows P.A (-P.A))
    (Sum.elim P.b (-P.b))
    P.c

lemma CanonicalLP.toStandardLP_isSolution_iff [OrderedRing R] (P : CanonicalLP I J R) (x : J → R) :
    P.toStandardLP.IsSolution x ↔ P.IsSolution x := by
  constructor
  · intro hyp
    simp only [StandardLP.IsSolution, CanonicalLP.toStandardLP, Matrix.fromRows_mulVec] at hyp
    rw [elim_le_elim_iff] at hyp
    obtain ⟨⟨ineqPos, ineqNeg⟩, nonneg⟩ := hyp
    constructor
    · apply eq_of_le_of_le ineqPos
      intro i
      have almost : -((P.A *ᵥ x) i) ≤ -(P.b i)
      · specialize ineqNeg i
        rwa [Matrix.neg_mulVec] at ineqNeg
      rwa [neg_le_neg_iff] at almost
    · exact nonneg
  · intro ⟨equ, nonneg⟩
    unfold CanonicalLP.toStandardLP StandardLP.IsSolution
    constructor
    · rw [Matrix.fromRows_mulVec, elim_le_elim_iff]
      constructor
      · exact equ.le
      rw [Matrix.neg_mulVec]
      intro i
      show -((P.A *ᵥ x) i) ≤ -(P.b i)
      rw [neg_le_neg_iff]
      exact equ.symm.le i
    · exact nonneg

lemma CanonicalLP.toStandardLP_isFeasible_iff [OrderedRing R] (P : CanonicalLP I J R) :
    P.toStandardLP.IsFeasible ↔ P.IsFeasible := by
  constructor <;>
  · intro ⟨x, hx⟩
    use x
    simpa [CanonicalLP.toStandardLP_isSolution_iff] using hx

lemma CanonicalLP.toStandardLP_reaches_iff [OrderedRing R] (P : CanonicalLP I J R) (v : R) :
    P.toStandardLP.Reaches v ↔ P.Reaches v := by
  constructor <;>
  · intro ⟨x, hx⟩
    use x
    simpa [CanonicalLP.toStandardLP_isSolution_iff] using hx
