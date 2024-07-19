import Mathlib.Algebra.Order.Sum
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.DotProduct
import VCSP.FarkasBartl


instance LinearOrderedField.toLinearOrderedDivisionRing {F : Type*} [instF : LinearOrderedField F] :
    LinearOrderedDivisionRing F := { instF with }

variable {I J F : Type*} [Fintype I] [Fintype J] [LinearOrderedField F]

open scoped Matrix

macro "finishit" : tactic => `(tactic| -- should be `private macro` which Lean does not allow
  unfold Matrix.mulVec Matrix.vecMul Matrix.dotProduct <;>
  simp_rw [Finset.sum_mul] <;> rw [Finset.sum_comm] <;>
  congr <;> ext <;> congr <;> ext <;> ring)

theorem equalityFarkas_neg (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → F, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  convert
    coordinateFarkas Aᵀ.mulVecLin ⟨⟨(b ⬝ᵥ ·), Matrix.dotProduct_add b⟩, (Matrix.dotProduct_smul · b)⟩
      using 1
  · constructor
    · intro ⟨x, hx, hAxb⟩
      refine ⟨x, hx, ?_⟩
      intro
      simp
      rw [←hAxb]
      finishit
    · intro ⟨x, hx, hAx⟩
      refine ⟨x, hx, ?_⟩
      simp at hAx
      apply Matrix.dotProduct_eq
      intro w
      rw [←hAx w]
      finishit
  · constructor <;> intro ⟨y, hAy, hby⟩ <;> use -y <;> constructor
    · simpa [Matrix.mulVecLin, Matrix.neg_mulVec] using hAy
    · simpa [Matrix.mulVecLin] using hby
    · simpa [Matrix.mulVecLin, Matrix.neg_mulVec_neg] using hAy
    · simpa [Matrix.mulVecLin] using hby

theorem inequalityFarkas_neg [DecidableEq I] (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  let A' : Matrix I (I ⊕ J) F := Matrix.fromColumns 1 A
  convert equalityFarkas_neg A' b using 1 <;> constructor
  · intro ⟨x, hx, hAxb⟩
    use Sum.elim (b - A *ᵥ x) x
    constructor
    · rw [Sum.nonneg_elim_iff]
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
      apply le_of_nneg_add hi
      apply Fintype.sum_nonneg
      rw [Pi.le_def]
      intro
      rw [Pi.zero_apply]
      apply mul_nonneg
      · apply Matrix.zero_le_one_elem
      · apply hx
  · intro ⟨y, hy, hAy, hby⟩
    refine ⟨y, ?_, hby⟩
    intro k
    cases k with
    | inl i => simpa [A', Matrix.neg_mulVec] using Matrix.dotProduct_nonneg_of_nonneg (Matrix.zero_le_one_elem · i) hy
    | inr j => apply hAy
  · intro ⟨y, hAy, hby⟩
    have h1Ay : 0 ≤ (Matrix.fromRows (1 : Matrix I I F) Aᵀ *ᵥ y)
    · intro k
      have hAy' : (-(Matrix.fromRows 1 Aᵀ *ᵥ y)) k ≤ 0
      · simp only [A', Matrix.transpose_fromColumns, Matrix.neg_mulVec, Matrix.transpose_one] at hAy
        apply hAy
      rwa [Pi.neg_apply, neg_le, neg_zero] at hAy'
    refine ⟨y, ?_, ?_, hby⟩
    · intro i
      simpa using h1Ay (Sum.inl i)
    · intro j
      rw [Matrix.neg_mulVec, Pi.neg_apply, neg_le, Pi.zero_apply, neg_zero]
      exact h1Ay (Sum.inr j)

macro "convertit" : tactic => `(tactic| -- should be `private macro` again
  conv => { rhs; rw [Matrix.neg_mulVec, ←neg_zero] } <;>
  constructor <;> intro hyp i <;> simpa using hyp i)

theorem equalityFarkas (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → F, 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  convert equalityFarkas_neg A b using 4
  convertit

theorem inequalityFarkas [DecidableEq I] (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  convert inequalityFarkas_neg A b using 5
  convertit

lemma equalityFrobenius_lt (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, A *ᵥ x = b) ≠ (∃ y : I → F, Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y < 0) := by
  convert equalityFarkas (Matrix.fromColumns A (-A)) b using 1
  · constructor
    · intro ⟨x, hAx⟩
      use Sum.elim x⁺ x⁻
      constructor
      · rw [Sum.nonneg_elim_iff]
        exact ⟨posPart_nonneg x, negPart_nonneg x⟩
      · rw [Matrix.fromColumns_mulVec_sum_elim, Matrix.neg_mulVec, ←Matrix.mulVec_neg, ←Matrix.mulVec_add, ←sub_eq_add_neg]
        convert hAx
        aesop
    · intro ⟨x, _, hAx⟩
      use x ∘ Sum.inl - x ∘ Sum.inr
      rw [Matrix.mulVec_sub]
      rwa [←Sum.elim_comp_inl_inr x, Matrix.fromColumns_mulVec_sum_elim, Matrix.neg_mulVec, ←sub_eq_add_neg] at hAx
  · constructor
    · intro ⟨y, hAy, hby⟩
      refine ⟨y, ?_, hby⟩
      rw [Matrix.transpose_fromColumns, Matrix.fromRows_mulVec, Sum.nonneg_elim_iff]
      constructor
      · rw [hAy]
      · rw [Matrix.transpose_neg, Matrix.neg_mulVec, hAy, neg_zero]
    · intro ⟨y, hAy, hby⟩
      refine ⟨y, ?_, hby⟩
      rw [Matrix.transpose_fromColumns, Matrix.fromRows_mulVec, Sum.nonneg_elim_iff] at hAy
      obtain ⟨hAyp, hAyn⟩ := hAy
      refine eq_of_le_of_le ?_ hAyp
      intro i
      specialize hAyn i
      rwa [Matrix.transpose_neg, Matrix.neg_mulVec, Pi.zero_apply, Pi.neg_apply, Right.nonneg_neg_iff] at hAyn

theorem equalityFrobenius (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, A *ᵥ x = b) ≠ (∃ y : I → F, Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y ≠ 0) := by
  convert equalityFrobenius_lt A b using 1
  refine ⟨?_, by aesop⟩
  intro ⟨y, hAy, hby⟩
  if hlt : b ⬝ᵥ y < 0 then
    aesop
  else
    use -y
    rw [Matrix.mulVec_neg, hAy, neg_zero, Matrix.dotProduct_neg, neg_lt_zero]
    push_neg at hlt
    exact ⟨rfl, lt_of_le_of_ne hlt hby.symm⟩
