import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import VCSP.Basic


class LinearOrderedDivisionRing (R : Type*) extends
  LinearOrderedRing R, DivisionRing R

theorem nFarkasBartl {n : ℕ} {F V W : Type*} [LinearOrderedDivisionRing F]
    [LinearOrderedAddCommGroup V] [Module F V] [PosSMulMono F V] [AddCommGroup W] [Module F W]
    (A : W →ₗ[F] Fin n → F) (b : W →ₗ[F] V) :
    (∀ x : W, A x ≤ 0 → b x ≤ 0) ↔ (∃ U : Fin n → V, 0 ≤ U ∧ ∀ w : W, b w = Finset.univ.sum (fun i : Fin n => A w i • U i)) := by
  constructor
  · revert A
    induction n with
    | zero =>
      intro A
      have A_tauto : ∀ w : W, A w ≤ 0
      · intro x i
        exfalso
        apply Nat.not_lt_zero
        exact i.isLt
      intro hAb
      refine ⟨0, by rfl, fun x : W => ?_⟩
      simp_rw [Pi.zero_apply, smul_zero, Finset.sum_const_zero]
      apply eq_of_le_of_le
      · exact hAb x (A_tauto x)
      · simpa using hAb (-x) (A_tauto (-x))
    | succ m ih =>
      intro A hA
      if complicated : ∃ x' : W, A x' ≤ 0 ∧ b x' > 0 then
        obtain ⟨x', hx'⟩ := complicated
        -- TODO switch to `A' : W →ₗ[F] Fin m → F` at some point (the earlier the better)
        let x'' := (A x' ⟨m, lt_add_one m⟩)⁻¹ • x'
        have hAx' : A x' ⟨m, lt_add_one m⟩ > 0
        · sorry
        have hAx'' : A x'' ⟨m, lt_add_one m⟩ = 1
        · sorry
        have hAA : ∀ x : W, A (x - (A x ⟨m, lt_add_one m⟩) • x'') ⟨m, lt_add_one m⟩ = 0
        · sorry
        have hh : ∀ x : W, (A (x - (A x ⟨m, lt_add_one m⟩) • x'') ≤ 0) → b (x - (A x ⟨m, lt_add_one m⟩) • x'') ≤ 0
        · sorry
        sorry
      else
        obtain ⟨U, hU, hb⟩ := ih (⟨⟨fun w => fun i => A w i.castSucc, by aesop⟩, by aesop⟩) (by
          intro x hAx
          push_neg at complicated
          apply complicated x -- or `apply hA` ?
          intro i
          if hi : i.val < m then
            sorry
          else
            sorry)
        use (fun i : Fin m.succ => if hi : i.val < m then U ⟨i.val, hi⟩ else 0)
        constructor
        · intro i
          if hi : i.val < m then
            simp [hi]
            apply hU
          else
            simp [hi]
        · intro w
          convert hb w using 1
          -- TODO prove that `S + 0 = S` essentially
          sorry
  · intro ⟨U, hU, hb⟩
    intro x hx
    rw [hb, ←neg_zero, ←le_neg, ←Finset.sum_neg_distrib]
    apply Finset.sum_nonneg
    intro i _
    rw [le_neg, neg_zero]
    exact smul_nonpos_of_nonpos_of_nonneg (hx i) (hU i)

variable {I : Type} [Fintype I]

theorem generalizedFarkasBartl {F V W : Type*} [LinearOrderedDivisionRing F]
    [LinearOrderedAddCommGroup V] [Module F V] [PosSMulMono F V] [AddCommGroup W] [Module F W]
    (A : W →ₗ[F] I → F) (b : W →ₗ[F] V) :
    (∀ x : W, A x ≤ 0 → b x ≤ 0) ↔ (∃ U : I → V, 0 ≤ U ∧ ∀ w : W, b w = Finset.univ.sum (fun i : I => A w i • U i)) := by
  constructor
  · induction' hI : ‹Fintype I›.elems using Finset.cons_induction_on with _i _I _hi _ih
    · intro hAb
      refine ⟨0, by rfl, fun _ : W => ?_⟩
      simp_rw [Pi.zero_apply, smul_zero, Finset.sum_const_zero]
      apply eq_of_le_of_le
      · apply hAb
        intro i
        exfalso
        apply Finset.not_mem_empty i
        exact hI ▸ ‹Fintype I›.complete i
      · rw [←neg_zero, ←neg_le, ←LinearMap.map_neg]
        apply hAb
        intro i
        exfalso
        apply Finset.not_mem_empty i
        exact hI ▸ ‹Fintype I›.complete i
    · sorry
  · intro ⟨U, hU, hb⟩
    intro x hx
    rw [hb, ←neg_zero, ←le_neg, ←Finset.sum_neg_distrib]
    apply Finset.sum_nonneg
    intro i _
    rw [le_neg, neg_zero]
    exact smul_nonpos_of_nonpos_of_nonneg (hx i) (hU i)


section corollaries

variable {F : Type*} [LinearOrderedField F]

instance LinearOrderedField.toLinearOrderedDivisionRing : LinearOrderedDivisionRing F :=
  { ‹LinearOrderedField F› with }

open scoped Matrix
variable {J : Type} [Fintype J]

macro "finishit" : tactic => `(tactic| -- should be `private macro` which Lean does not allow
  unfold Matrix.mulVec Matrix.vecMul Matrix.dotProduct <;>
  simp_rw [Finset.sum_mul] <;> rw [Finset.sum_comm] <;>
  congr <;> ext <;> congr <;> ext <;> ring)

theorem equalityFarkas (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → F, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
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

theorem mainFarkas [DecidableEq I] (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  let A' : Matrix I (I ⊕ J) F := Matrix.fromColumns 1 A
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

end corollaries
