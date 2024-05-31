import Mathlib.Algebra.Order.CompleteField
import VCSP.FarkasBasic

open scoped Matrix

/-!

# Linear programming

We define linear programs over an `OrderedSemiring R` in the standard matrix form.

## Main definitions

 * `StandardLP` defines a linear program in the standard form (maximize `cᵀx` such that `A x ≤ b` and `x ≥ 0`).
 * `StandardLP.IsSolution` tells if given vector is a solution satisfying given standard LP.
 * `StandardLP.IsFeasible` tells if given standard LP has any solution.
 * `StandardLP.Reaches` tells if given value can be obtained as a cost of any solution of given standard LP.
 * `StandardLP.dual` defines a dual problem to given standard LP.

## Main results

* `StandardLP.weakDuality`: The weak duality theorem (`cᵀx` such that `A x ≤ b` and `x ≥ 0` is
   always less or equal to `bᵀy` such that `Aᵀ y ≥ c` and `y ≥ 0`) is provided for matrices over any `OrderedCommRing`.
* `StandardLP.strongDuality`: The strong duality theorem (there is an objective value that is
   reached by both the primar LP and the dual LP) is provided for matrices over any `LinearOrderedField`.

-/

/-- Linear program in the standard form. Variables are of type `J`. Conditions are indexed by type `I`. -/
structure StandardLP (I J R : Type*) where
  /-- Matrix of coefficients -/
  A : Matrix I J R
  /-- Right-hand side -/
  b : I → R
  /-- Objective function coefficients -/
  c : J → R

variable {I J R : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def StandardLP.IsSolution [OrderedSemiring R] (P : StandardLP I J R) (x : J → R) : Prop :=
  P.A *ᵥ x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there is a vector `x` that is a solution to `P`. -/
def StandardLP.IsFeasible [OrderedSemiring R] (P : StandardLP I J R) : Prop :=
  ∃ x : J → R, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the costs (given by the vector `c`) and summed up,
    the result is the value `v`. -/
def StandardLP.Reaches [OrderedSemiring R] (P : StandardLP I J R) (v : R) : Prop :=
  ∃ x : J → R, P.IsSolution x ∧ P.c ⬝ᵥ x = v

/-- Dual linear program to given linear program `P` in the standard form.
    The matrix gets transposed and its values flip signs.
    The original cost function gets flipped signs as well and becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new vector of objective function coefficients. -/
def StandardLP.dual [OrderedRing R] (P : StandardLP I J R) : StandardLP J I R :=
  ⟨-P.Aᵀ, -P.c, P.b⟩

/-- All objective values reached by linear program `P` are all less or equal to
    all objective values reached by the dual of `P`. -/
theorem StandardLP.weakDuality [OrderedCommRing R] {P : StandardLP I J R}
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

lemma StandardLP.unbounded_primal_makes_dual_infeasible [OrderedCommRing R]
    {P : StandardLP I J R} (hP : ∀ r : R, ∃ p : R, r < p ∧ P.Reaches p) :
    ¬ P.dual.IsFeasible :=
  fun ⟨y, hAy, hy⟩ =>
    let ⟨_, hb, hP'⟩ := hP (P.b ⬝ᵥ y)
    ((P.weakDuality hP' ⟨y, ⟨hAy, hy⟩, rfl⟩).trans_lt hb).false

lemma StandardLP.unbounded_dual_makes_primal_infeasible [OrderedCommRing R]
    {P : StandardLP I J R} (hD : ∀ r : R, ∃ q : R, q < r ∧ P.dual.Reaches q) :
    ¬ P.IsFeasible :=
  fun ⟨x, hAx, hx⟩ =>
    let ⟨_, hc, hD'⟩ := hD (P.c ⬝ᵥ x)
    ((P.weakDuality ⟨x, ⟨hAx, hx⟩, rfl⟩ hD').trans_lt hc).false

lemma StandardLP.unbounded_primal_makes_dual_infeasible' [LinearOrderedCommRing R]
    {P : StandardLP I J R} (hP : ∀ r : R, ∃ p : R, r ≤ p ∧ P.Reaches p) :
    ¬ P.dual.IsFeasible :=
  StandardLP.unbounded_primal_makes_dual_infeasible (fun r : R =>
    let ⟨p, hrp, hPp⟩ := hP (r + 1)
    ⟨p, (lt_add_one r).trans_le hrp, hPp⟩)

lemma StandardLP.unbounded_dual_makes_primal_infeasible' [LinearOrderedCommRing R]
    {P : StandardLP I J R} (hD : ∀ r : R, ∃ q : R, q ≤ r ∧ P.dual.Reaches q) :
    ¬ P.IsFeasible :=
  StandardLP.unbounded_dual_makes_primal_infeasible (fun r : R =>
    let ⟨d, hdr, hDd⟩ := hD (r - 1)
    ⟨d, (hdr.trans_lt (sub_one_lt r)), hDd⟩)

lemma sInf_le_sSup_of_both_dualities_of_both_nonempty [ConditionallyCompleteLinearOrder R]
    {P Q : Set R} (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p ≤ q) (hR : ∀ r : R, (∃ p ∈ P, r < p) ≠ (∃ q ∈ Q, q ≤ r)) :
    sInf Q ≤ sSup P := by
  have boundedP : BddAbove P
  · obtain ⟨q₀, hq₀⟩ := hQ
    use q₀
    intro a ha
    exact hPQ a ha q₀ hq₀
  have boundedQ : BddBelow Q
  · obtain ⟨p₀, hp₀⟩ := hP
    use p₀
    intro a ha
    exact hPQ p₀ hp₀ a ha
  have left_false : (∃ p ∈ P, sSup P < p) = False
  · simpa using (fun _ => le_csSup boundedP)
  specialize hR (sSup P)
  simp [left_false] at hR
  obtain ⟨x, hxQ, hxP⟩ := hR
  exact csInf_le_of_le boundedQ hxQ hxP

lemma lt_inv_mul [LinearOrderedField R] {a b c : R} (hb : 0 < b) (habc : a * b < c) : a < b⁻¹ * c := by
  rw [lt_iff_not_le] at habc ⊢
  intro contr
  apply habc
  rwa [inv_mul_le_iff' hb] at contr

/-- The supremum of objective values reached by linear program `P` is equal to
    the infimum of objective values reached by the dual of `P`. -/
theorem StandardLP.strongishDuality [ConditionallyCompleteLinearOrderedField R] [DecidableEq J]
    {P : StandardLP I J R} (hP : P.IsFeasible) (hD : P.dual.IsFeasible) :
    sSup P.Reaches = sInf P.dual.Reaches := by
  have hP' : Set.Nonempty P.Reaches
  · obtain ⟨x, _⟩ := hP
    use P.c ⬝ᵥ x, x
  have hQ' : Set.Nonempty P.dual.Reaches
  · obtain ⟨y, _⟩ := hD
    use P.dual.c ⬝ᵥ y, y
  apply eq_of_le_of_le
  · apply csSup_le hP'
    intro _ hP''
    apply le_csInf hQ'
    intro _ hQ''
    exact StandardLP.weakDuality hP'' hQ''
  apply sInf_le_sSup_of_both_dualities_of_both_nonempty hP' hQ'
  · apply StandardLP.weakDuality
  · intro r
    show
      (∃ p : R, (∃ y', (P.A *ᵥ y' ≤ P.b ∧ 0 ≤ y') ∧ P.c ⬝ᵥ y' = p) ∧ r < p) ≠
      (∃ q : R, (∃ x', (-P.Aᵀ *ᵥ x' ≤ -P.c ∧ 0 ≤ x') ∧ P.b ⬝ᵥ x' = q) ∧ q ≤ r)
    simp
      only [exists_exists_and_eq_and]
    show
      (∃ y' : J → R, (P.A *ᵥ y' ≤ P.b ∧ 0 ≤ y') ∧ r < P.c ⬝ᵥ y') ≠
      (∃ x' : I → R, (-P.Aᵀ *ᵥ x' ≤ -P.c ∧ 0 ≤ x') ∧ P.b ⬝ᵥ x' ≤ r)
    convert
      (inequalityFarkas
        (Matrix.fromRows (-P.Aᵀ) (fun _ : Unit => P.b))
        (Sum.elim (-P.c) (fun _ : Unit => r))
      ).symm
          using 1
    · constructor
      · intro ⟨y', ⟨hAy', hy'⟩, hcy'⟩
        use Sum.elim y' (fun _ => 1)
        constructor
        · rw [zero_le_elim_iff]
          exact ⟨hy', fun _ => zero_le_one⟩
        constructor
        · intro i
          rw [
            Matrix.transpose_fromRows, Matrix.fromColumns_mulVec_sum_elim,
            Matrix.transpose_neg, Matrix.transpose_transpose,
            Pi.add_apply, Matrix.neg_mulVec, Pi.neg_apply]
          simpa [Matrix.mulVec] using hAy' i
        · rwa [
            Matrix.sum_elim_dotProduct_sum_elim, Matrix.dotProduct_pUnit, mul_one,
            Matrix.neg_dotProduct, neg_add_lt_iff_lt_add, add_zero]
      · intro ⟨y, hy, hAby, hcy⟩
        change hAby to 0 ≤ (Matrix.fromRows (-P.Aᵀ) (fun i _ => P.b i)ᵀ)ᵀ *ᵥ y
        rw [
          ←Matrix.transpose_neg P.A, ←Matrix.transpose_fromColumns, Matrix.transpose_transpose,
          ←Sum.elim_comp_inl_inr y, Matrix.fromColumns_mulVec_sum_elim,
          Matrix.neg_mulVec, le_neg_add_iff_le
        ] at hAby
        rw [
          ←Sum.elim_comp_inl_inr y, Matrix.sum_elim_dotProduct_sum_elim,
          Matrix.neg_dotProduct, neg_add_lt_iff_lt_add, add_zero
        ] at hcy
        if last_zero : y (Sum.inr ()) = 0 then
          exfalso
          have h_Aby : P.A *ᵥ y ∘ Sum.inl ≤ 0
          · convert hAby
            ext i
            simp only [Matrix.mulVec, Matrix.dotProduct_pUnit, Function.comp_apply]
            rw [Pi.zero_apply, last_zero, mul_zero]
          have h_cy : 0 < P.c ⬝ᵥ y ∘ Sum.inl
          · simpa [Matrix.dotProduct, last_zero] using hcy
          refine StandardLP.unbounded_primal_makes_dual_infeasible' ?_ hD
          unfold StandardLP.Reaches
          by_contra! contr
          obtain ⟨s, hs⟩ := contr
          obtain ⟨x, hAx, hx⟩ := hP
          if s_big : P.c ⬝ᵥ x ≤ s then
            have coef_nng : 0 ≤ (s - P.c ⬝ᵥ x) / (P.c ⬝ᵥ y ∘ Sum.inl)
            · have num_nng : 0 ≤ s - P.c ⬝ᵥ x
              · exact sub_nonneg_of_le s_big
              positivity
            apply hs (P.c ⬝ᵥ (x + ((s - P.c ⬝ᵥ x) / (P.c ⬝ᵥ y ∘ Sum.inl)) • y ∘ Sum.inl)) (by rw [
                Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul,
                div_mul, div_self h_cy.ne.symm, div_one, add_sub, add_comm, ←add_sub, sub_self, add_zero
              ]) (x + ((s - P.c ⬝ᵥ x) / (P.c ⬝ᵥ y ∘ Sum.inl)) • y ∘ Sum.inl)
            constructor
            · rw [Matrix.mulVec_add, ←add_zero P.b]
              apply add_le_add hAx
              rw [Matrix.mulVec_smul]
              exact smul_nonpos_of_nonneg_of_nonpos coef_nng h_Aby
            · rw [←add_zero 0]
              apply add_le_add hx
              apply smul_nonneg coef_nng
              apply nng_com hy
            · rfl
          else
            exact hs (P.c ⬝ᵥ x) (le_of_not_ge s_big) x ⟨hAx, hx⟩ rfl
        else
          rw [←ne_eq] at last_zero
          have hyo := hy (Sum.inr ())
          have hyop := lt_of_le_of_ne hyo last_zero.symm
          use (y (Sum.inr ()))⁻¹ • y ∘ Sum.inl
          constructor; constructor
          · rw [Matrix.mulVec_smul, inv_smul_le_iff_of_pos hyop]
            convert hAby
            ext i
            simp only [Matrix.mulVec, Matrix.dotProduct_pUnit, Function.comp_apply]
            rw [Pi.smul_apply, smul_eq_mul, mul_comm]
          · apply smul_nonneg (inv_nonneg_of_nonneg hyo)
            apply nng_com hy
          · rw [Matrix.dotProduct_smul, smul_eq_mul]
            apply lt_inv_mul hyop
            simpa using hcy
    · constructor
      · intro ⟨x', ⟨hAx', hx'⟩, hbx'⟩
        refine ⟨x', hx', ?_⟩
        rw [Matrix.fromRows_mulVec, elim_le_elim_iff]
        exact ⟨hAx', fun _ => hbx'⟩
      · intro ⟨x, hx, hPx⟩
        rw [Matrix.fromRows_mulVec, elim_le_elim_iff] at hPx
        exact ⟨x, ⟨hPx.left, hx⟩, hPx.right ()⟩

lemma Matrix.transpose_mulVec_dotProduct [CommSemiring R] (M : Matrix I J R) (v : I → R) (w : J → R) :
    Mᵀ *ᵥ v ⬝ᵥ w = M *ᵥ w ⬝ᵥ v := by
  rw [Matrix.dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem StandardLP.strongDuality [DecidableEq I] [DecidableEq J] [LinearOrderedField R]
    {P : StandardLP I J R} (hP : P.IsFeasible) (hD : P.dual.IsFeasible) :
    ∃ r : R, P.Reaches r ∧ P.dual.Reaches r := by
  cases
    or_of_neq
      (inequalityFarkas
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.row (Sum.elim (-P.c) P.b)))
        (Sum.elim (Sum.elim P.b (-P.c)) 0)) with
  | inl case_x =>
    obtain ⟨x, hx, hAx⟩ := case_x
    rw [Matrix.fromRows_mulVec, Matrix.fromBlocks_mulVec, elim_le_elim_iff, elim_le_elim_iff] at hAx
    have hPx : P.Reaches (P.c ⬝ᵥ x ∘ Sum.inl)
    · exact ⟨x ∘ Sum.inl, ⟨by simpa using hAx.left.left, nng_com hx Sum.inl⟩, rfl⟩
    have hDx : P.dual.Reaches (P.b ⬝ᵥ x ∘ Sum.inr)
    · exact ⟨x ∘ Sum.inr, ⟨by simpa using hAx.left.right, nng_com hx Sum.inr⟩, rfl⟩
    have objectives_eq : P.b ⬝ᵥ (x ∘ Sum.inr) = P.c ⬝ᵥ (x ∘ Sum.inl)
    · apply eq_of_le_of_le
      · rw [←add_zero (P.c ⬝ᵥ x ∘ Sum.inl), ←neg_add_le_iff_le_add, ←Matrix.neg_dotProduct, ←Matrix.sum_elim_dotProduct_sum_elim]
        simpa using hAx.right ()
      · exact StandardLP.weakDuality hPx hDx
    rw [objectives_eq] at hDx
    exact ⟨P.c ⬝ᵥ (x ∘ Sum.inl), hPx, hDx⟩
  | inr case_y =>
    obtain ⟨y, hy, hAy, hbcy⟩ := case_y
    exfalso
    simp [Matrix.transpose_fromRows, Matrix.fromBlocks_transpose] at hAy
    have hcb : Matrix.col (Sum.elim (-P.c) P.b) *ᵥ y ∘ Sum.inr = -(Sum.elim (y (Sum.inr ()) • P.c) (y (Sum.inr ()) • -P.b))
    · ext k
      cases k <;> simp [Matrix.mulVec, mul_comm]
    rw [
      ←Sum.elim_comp_inl_inr y, Matrix.fromColumns_mulVec_sum_elim, Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec, add_zero, Matrix.zero_mulVec, zero_add,
      hcb, le_add_neg_iff_le, elim_le_elim_iff
    ] at hAy
    obtain ⟨hAyb, hAyc⟩ := hAy
    rw [
      ←Sum.elim_comp_inl_inr y, ←Sum.elim_comp_inl_inr (y ∘ Sum.inl),
      Matrix.sum_elim_dotProduct_sum_elim, Matrix.zero_dotProduct, add_zero, Matrix.sum_elim_dotProduct_sum_elim,
      Matrix.neg_dotProduct, add_neg_lt_iff_lt_add, zero_add
    ] at hbcy
    have y_last_pos : 0 < y (Sum.inr ())
    · by_contra contr
      have last_zero : y (Sum.inr ()) = 0
      · exact (eq_of_le_of_not_lt (hy (Sum.inr ())) contr).symm
      rw [last_zero, zero_smul] at hAyb hAyc
      clear contr last_zero
      rw [Matrix.neg_mulVec, Right.nonneg_neg_iff] at hAyc
      if hcylr : 0 < P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr then
        refine StandardLP.unbounded_primal_makes_dual_infeasible' ?_ hD
        unfold StandardLP.Reaches
        by_contra! contr
        obtain ⟨s, hs⟩ := contr
        obtain ⟨p, hAp, hp⟩ := hP
        if s_big : P.c ⬝ᵥ p ≤ s then
          have coef_nng : 0 ≤ (s - P.c ⬝ᵥ p) / (P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr)
          · exact div_nonneg (sub_nonneg_of_le s_big) hcylr.le
          refine hs (P.c ⬝ᵥ (p + ((s - P.c ⬝ᵥ p) / (P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr)) • (y ∘ Sum.inl) ∘ Sum.inr)) (by rw [
              Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul,
              div_mul, div_self hcylr.ne.symm, div_one, add_sub, add_comm, ←add_sub, sub_self, add_zero
            ]) (p + ((s - P.c ⬝ᵥ p) / (P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr)) • (y ∘ Sum.inl) ∘ Sum.inr) ?_ rfl
          constructor
          · rw [Matrix.mulVec_add, ←add_zero P.b]
            apply add_le_add hAp
            rw [Matrix.mulVec_smul]
            exact smul_nonpos_of_nonneg_of_nonpos coef_nng hAyc
          · rw [←add_zero 0]
            apply add_le_add hp
            apply smul_nonneg coef_nng
            apply nng_com hy
        else
          exact hs (P.c ⬝ᵥ p) (le_of_not_ge s_big) p ⟨hAp, hp⟩ rfl
      else
        have hbyll : P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl < 0
        · linarith
        clear hcylr
        refine StandardLP.unbounded_dual_makes_primal_infeasible' ?_ hP
        unfold StandardLP.Reaches
        by_contra! contr
        obtain ⟨s, hs⟩ := contr
        obtain ⟨d, hAd, hd⟩ := hD
        if s_low : s ≤ P.b ⬝ᵥ d then
          have coef_nng : 0 ≤ (s - P.b ⬝ᵥ d) / P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl
          · exact div_nonneg_of_nonpos (sub_nonpos_of_le s_low) hbyll.le
          refine hs (P.b ⬝ᵥ (d + ((s - P.b ⬝ᵥ d) / (P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl)) • (y ∘ Sum.inl) ∘ Sum.inl)) (by rw [
              Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul,
              div_mul, div_self hbyll.ne, div_one, add_sub, add_comm, ←add_sub, sub_self, add_zero
            ]) (d + ((s - P.b ⬝ᵥ d) / (P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl)) • (y ∘ Sum.inl) ∘ Sum.inl) ?_ rfl
          constructor
          · rw [Matrix.mulVec_add, ←add_zero P.dual.b]
            apply add_le_add hAd
            rw [Matrix.mulVec_smul]
            apply smul_nonpos_of_nonneg_of_nonpos coef_nng
            simpa [StandardLP.dual, Matrix.neg_mulVec] using neg_nonpos_of_nonneg hAyb
          · rw [←add_zero 0]
            apply add_le_add hd
            apply smul_nonneg coef_nng
            apply nng_com hy
        else
          exact hs (P.b ⬝ᵥ d) (le_of_not_ge s_low) d ⟨hAd, hd⟩ rfl
    have hbcy' : (y (Sum.inr ()) • P.b) ⬝ᵥ ((y ∘ Sum.inl)) ∘ Sum.inl < (y (Sum.inr ()) • P.c) ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr
    · rw [←mul_lt_mul_left y_last_pos] at hbcy
      convert hbcy <;> simp
    have hAyb' : y (Sum.inr ()) • P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr ≤ P.Aᵀ *ᵥ (y ∘ Sum.inl) ∘ Sum.inl ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr
    · apply Matrix.dotProduct_le_dotProduct_of_nonneg_right hAyb
      apply nng_com hy
    have hAyc' : P.A *ᵥ (y ∘ Sum.inl) ∘ Sum.inr ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl ≤ y (Sum.inr ()) • P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl
    · rw [smul_neg, Matrix.neg_mulVec, neg_le_neg_iff] at hAyc
      apply Matrix.dotProduct_le_dotProduct_of_nonneg_right hAyc
      apply nng_com hy
    rw [Matrix.transpose_mulVec_dotProduct] at hAyb'
    exact ((hbcy'.trans_le hAyb').trans_le hAyc').false

#print axioms StandardLP.strongDuality
