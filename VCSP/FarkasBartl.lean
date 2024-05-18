import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import VCSP.Basic


class LinearOrderedDivisionRing (R : Type*) extends
  LinearOrderedRing R, DivisionRing R

lemma industepFarkasBartl {m : ℕ} {F V W : Type*} [LinearOrderedField F] -- TODO generalize to [LinearOrderedDivisionRing F]
    [LinearOrderedAddCommGroup V] [Module F V] [PosSMulMono F V] [AddCommGroup W] [Module F W]
    (ih : ∀ A₀ : W →ₗ[F] Fin m → F, ∀ b₀ : W →ₗ[F] V,
      (∀ x : W, A₀ x ≤ 0 → b₀ x ≤ 0) →
        (∃ U : Fin m → V, 0 ≤ U ∧ ∀ w : W, b₀ w = Finset.univ.sum (fun i : Fin m => A₀ w i • U i)))
    {A : W →ₗ[F] Fin m.succ → F} {b : W →ₗ[F] V} (hAb : ∀ x : W, A x ≤ 0 → b x ≤ 0) :
    ∃ U : Fin m.succ → V, 0 ≤ U ∧ ∀ w : W, b w = Finset.univ.sum (fun i : Fin m.succ => A w i • U i) := by
  let A' : W →ₗ[F] Fin m → F := ⟨⟨fun w => fun i => A w i.castSucc, by aesop⟩, by aesop⟩
  if is_easy : ∀ x : W, A' x ≤ 0 → b x ≤ 0 then
    obtain ⟨U, hU, hbU⟩ := ih A' b is_easy
    use (fun i : Fin m.succ => if hi : i.val < m then U ⟨i.val, hi⟩ else 0)
    constructor
    · intro i
      if hi : i.val < m then
        simp [hi]
        apply hU
      else
        simp [hi]
    · intro w
      simp_rw [smul_dite, smul_zero]
      rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
      convert hbU w using 1
      sorry -- easy
  else
    push_neg at is_easy
    obtain ⟨x', hax', hbx'⟩ := is_easy
    let j : Fin m.succ := ⟨m, lt_add_one m⟩
    let x := (A x' j)⁻¹ • x'
    have hAx' : A x' j > 0
    · by_contra! contr
      exact ((hAb x' (fun i => if hi : i.val < m then hax' ⟨i, hi⟩ else if hij : i = j then hij ▸ contr else by
          exfalso
          have := i.isLt
          simp [j] at hij
          apply hij
          sorry -- easy
        )).trans_lt hbx').false
    have hAx : A x j = 1
    · convert inv_mul_cancel hAx'.ne.symm
      simp [x]
    have hAA : ∀ w : W, A (w - (A w j • x)) j = 0
    · intro w
      simp [hAx]
    have haAbA : ∀ w : W, A' (w - (A w j • x)) ≤ 0 → b (w - (A w j • x)) ≤ 0
    · intro w hw
      apply hAb
      intro i
      if hi : i.val < m then
        exact hw ⟨i, hi⟩
      else if hij : i = j then
        sorry -- from `hAA`
      else
        sorry -- easy
    have haaAbbA : ∀ w : W, A' w - A' (A w j • x) ≤ 0 → b w - b (A w j • x) ≤ 0
    · simpa using haAbA
    have haAabAb : ∀ w : W, (A' - (A · j • A' x)) w ≤ 0 → (b - (A · j • b x)) w ≤ 0
    · simpa using haaAbbA
    obtain ⟨U', hU', hbU'⟩ := ih ⟨⟨A' - (A · j • A' x), sorry⟩, sorry⟩ ⟨⟨b - (A · j • b x), sorry⟩, sorry⟩ haAabAb -- TODO linearities
    use (fun i : Fin m.succ => if hi : i.val < m then U' ⟨i.val, hi⟩ else b x - Finset.univ.sum (fun i : Fin m => A' x i • U' i))
    constructor
    · intro i
      if hi : i.val < m then
        simp [hi]
        apply hU'
      else
        simp [hi]
        have hAx'inv : 0 ≤ (A x' j)⁻¹
        · exact (inv_pos_of_pos hAx').le
        have hax : A' x ≤ 0
        · simpa [x] using smul_nonpos_of_nonneg_of_nonpos hAx'inv hax'
        have hbx : 0 ≤ b x
        · simpa [x] using smul_nonneg hAx'inv hbx'.le
        have haU' : Finset.univ.sum (fun i => A' x i • U' i) ≤ 0
        · sorry -- follows from `hax` and `hU'` together
        exact haU'.trans hbx
    · intro w
      have key : b w - A w j • b x = Finset.univ.sum (fun i : Fin m => (A' w i - A w j * A' x i) • U' i)
      · simpa using hbU' w
      rw [←add_eq_of_eq_sub key.symm]
      simp_rw [smul_dite]
      rw [Finset.sum_dite]
      show
        Finset.univ.sum (fun i : Fin m => (A' w i - A w j * A' x i) • U' i) + A w j • b x =
        (Finset.univ.filter (·.val < m)).attach.sum (fun i => A w i.val • U' ⟨i.val.val, (Finset.mem_filter.mp i.property).right⟩) +
        (Finset.univ.filter (¬ ·.val < m)).attach.sum (fun j => A w j.val • (b x - Finset.univ.sum (fun i : Fin m => A' x i • U' i)))
      have hAwj :
        (Finset.univ.filter (¬ ·.val < m)).attach.sum (fun j => A w j.val • (b x - Finset.univ.sum (fun i : Fin m => A' x i • U' i))) =
        A w j • (b x - Finset.univ.sum (fun i : Fin m => A' x i • U' i))
      · sorry -- sum over singleton is equal to the single element
      rw [hAwj]
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      simp_rw [←smul_smul, ←Finset.smul_sum]
      rw [smul_sub]
      show
        Finset.univ.sum (fun i : Fin m => A' w i • U' i) - A w j • Finset.univ.sum (fun i : Fin m => A' x i • U' i) +
          A w j • b x =
        (Finset.univ.filter (·.val < m)).attach.sum (fun i => A w i.val • U' ⟨i.val.val, _⟩) +
          (A w j • b x - A w j • Finset.univ.sum (fun i : Fin m => A' x i • U' i))
      suffices :
        Finset.univ.sum (fun i : Fin m => A' w i • U' i) =
        (Finset.univ.filter _).attach.sum
          (fun i : { _i : Fin m.succ // _i ∈ Finset.univ.filter (·.val < m) } => A w i.val • U' ⟨i.val.val, _⟩)
      · sorry -- almost by `linarith`
      sorry -- from now really straighforward (two ways of summing the same thing)

theorem nFarkasBartl {n : ℕ} {F V W : Type*} [LinearOrderedField F] -- TODO generalize to [LinearOrderedDivisionRing F]
    [LinearOrderedAddCommGroup V] [Module F V] [PosSMulMono F V] [AddCommGroup W] [Module F W]
    (A : W →ₗ[F] Fin n → F) (b : W →ₗ[F] V) :
    (∀ x : W, A x ≤ 0 → b x ≤ 0) ↔ (∃ U : Fin n → V, 0 ≤ U ∧ ∀ w : W, b w = Finset.univ.sum (fun i : Fin n => A w i • U i)) := by
  constructor
  · induction n generalizing b with -- note that `A` is "generalized" automatically
    | zero =>
      have A_tauto (w : W) : A w ≤ 0
      · intro i
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
      exact industepFarkasBartl ih
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
    · sorry -- almost certainly wrong
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
