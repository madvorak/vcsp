import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned
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
    (∀ x : W, A x ≤ 0 → b x ≤ 0) ↔ (∃ U : I → V, 0 ≤ U ∧ ∀ w : W, b w = Finset.univ.sum (fun i : I => A w i • U i)) := by
  sorry


section corollaries

lemma not_neq_of_iff {P Q : Prop} (hpq : P ↔ Q) : (¬P) ≠ Q := by
  tauto

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

lemma le_of_nng_add {α : Type*} [OrderedAddCommGroup α] {a b c : α} (habc : a + b = c) (ha : 0 ≤ a) : b ≤ c := by
  aesop

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
    not_neq_of_iff
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

lemma Matrix.zero_le_one_elem {R : Type*} [OrderedSemiring R] [DecidableEq I] (i i' : I) :
    (0 : R) ≤ (1 : Matrix I I R) i i' := by
  by_cases hi : i = i' <;> simp [hi]

theorem mainFarkas [DecidableEq I] (A : Matrix I J ℚ) (b : I → ℚ) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → ℚ, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  let A' : Matrix I (I ⊕ J) ℚ := Matrix.fromColumns 1 A
  convert equalityFarkas A' b using 1 <;> constructor
  · intro ⟨x, hx, hAxb⟩
    use Sum.elim (b - A *ᵥ x) x
    constructor
    · rw [←Sum.elim_zero_zero, sumElim_le_sumElim_iff]
      exact ⟨fun i : I => sub_nonneg_of_le (hAxb i), hx⟩
    · aesop
  · intro ⟨x, hx, hAxb⟩
    use x ∘ Sum.inr
    constructor
    · intro
      apply hx
    · intro i
      have hi := congr_fun hAxb i
      simp [A', Matrix.mulVec, Matrix.dotProduct, Matrix.fromColumns] at hi
      apply le_of_nng_add hi
      apply Fintype.sum_nonneg
      rw [Pi.le_def]
      intro
      rw [Pi.zero_apply]
      apply Rat.mul_nonneg
      · apply Matrix.zero_le_one_elem
      · apply hx
  · intro ⟨y, hy, hAy, hby⟩
    refine ⟨y, ?_, hby⟩
    intro k
    cases k with
    | inl i => simpa [A', Matrix.neg_mulVec] using Matrix.dotProduct_nonneg_of_nonneg (Matrix.zero_le_one_elem · i) hy
    | inr j => apply hAy
  · intro ⟨y, hAy, hby⟩
    have h1Ay : 0 ≤ (Matrix.fromRows (1 : Matrix I I ℚ) Aᵀ *ᵥ y)
    · intro k
      have hAy' : (-(Matrix.fromRows 1 Aᵀ *ᵥ y)) k ≤ 0
      · simp only [A', Matrix.transpose_fromColumns, Matrix.neg_mulVec, Matrix.transpose_one] at hAy
        apply hAy
      rwa [Pi.neg_apply, neg_le] at hAy'
    refine ⟨y, ?_, ?_, hby⟩
    · intro i
      simpa using h1Ay (Sum.inl i)
    · intro j
      rw [Matrix.neg_mulVec, Pi.neg_apply, neg_le, Pi.zero_apply, neg_zero]
      exact h1Ay (Sum.inr j)

end corollaries
