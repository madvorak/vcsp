import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import VCSP.Basic


class CompatiblyOrdered (R M : Type*) [OrderedSemiring R] [OrderedAddCommMonoid M] [Module R M] where
  smul_order : ∀ a : R, ∀ v : M, 0 ≤ a → 0 ≤ v → 0 ≤ a • v

instance (R : Type*) [OrderedSemiring R] : CompatiblyOrdered R R := ⟨fun _ _ => smul_nonneg⟩

variable {I : Type*} [Fintype I] -- typically `Fin m`

/- The paper by Bartl is actually more general, in particular allowing "skew fields" (`DivisionRing`),
   but Mathlib does not seem to have a definition `LinearOrderedDivisionRing`,
   so we work with `LinearOrderedField` for now. -/
theorem generalizedFarkasBartl {F V W : Type*} [LinearOrderedField F] -- typically `V` = `F` and `W` = `F^n`
    [LinearOrderedAddCommGroup V] [Module F V] [CompatiblyOrdered F V] [AddCommGroup W] [Module F W]
    (A : W →ₗ[F] I → F) (b : W →ₗ[F] V) :
    (∀ x : W, A x ≤ 0 → b x ≤ 0) ↔ (∃ U : I → V, 0 ≤ U ∧
        ∀ w : W, b w = Finset.univ.sum (fun i : I => A w i • U i)) := by
  sorry


section corollaries

lemma of_iff {P Q : Prop} (hpq : P ↔ Q) : (¬P) ≠ Q := by
  tauto

open Matrix
variable {J : Type*} [Fintype J]

lemma Matrix.neg_mulVec_neg {R : Type*} [Ring R] (v : J → R) (A : Matrix I J R) : (-A) *ᵥ (-v) = A *ᵥ v := by
  rw [Matrix.mulVec_neg, Matrix.neg_mulVec, neg_neg]

macro "finishit" : tactic => `(tactic|
  unfold Matrix.mulVec Matrix.vecMul Matrix.dotProduct <;>
  simp_rw [Finset.sum_mul] <;> rw [Finset.sum_comm] <;>
  congr <;> ext <;> congr <;> ext <;> ring)

theorem equalityFarkas (A : Matrix I J ℚ) (b : I → ℚ) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → ℚ, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  have gener :=
    of_iff
      (generalizedFarkasBartl Aᵀ.mulVecLin (⟨⟨(b ⬝ᵥ ·), Matrix.dotProduct_add b⟩, (Matrix.dotProduct_smul · b)⟩))
  push_neg at gener
  convert gener.symm using 1 <;> clear gener <;> constructor
  · intro ⟨x, hx, hAxb⟩
    refine ⟨x, hx, ?_⟩
    intro
    simp
    rw [←hAxb]
    finishit
  · intro ⟨U, hU, hAU⟩
    refine ⟨U, hU, ?_⟩
    simp at hAU
    apply Matrix.dotProduct_eq
    intro w
    rw [hAU w]
    finishit
  · intro ⟨y, hAy, hby⟩
    use -y
    constructor
    · simpa [Matrix.mulVecLin, Matrix.neg_mulVec] using hAy
    · simpa [Matrix.mulVecLin] using hby
  · intro ⟨x, hAx, hbx⟩
    use -x
    constructor
    · rw [Matrix.neg_mulVec_neg]
      simpa [Matrix.mulVecLin] using hAx
    · simpa [Matrix.mulVecLin] using hbx

theorem mainFarkas (A : Matrix I J ℚ) (b : I → ℚ) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → ℚ, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  sorry

end corollaries
