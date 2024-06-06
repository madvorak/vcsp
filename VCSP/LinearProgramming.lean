import Mathlib.Algebra.Order.Pi
import VCSP.FarkasBasic

/-!

# Linear programming

We define linear programs in the standard matrix form and prove the duality theorems.

## Main definitions

 * `StandardLP` defines a linear program in the standard form (maximize `cᵀx` such that `A x ≤ b` and `x ≥ 0`).
 * `StandardLP.IsSolution` tells if given vector is a solution satisfying given standard LP.
 * `StandardLP.IsFeasible` tells if given standard LP has any solution.
 * `StandardLP.Reaches` tells if given value can be obtained as a cost of any solution of given standard LP.
 * `StandardLP.dualize` defines a dual problem to given standard LP.

## Main results

* `StandardLP.weakDuality`: The weak duality theorem (`cᵀx` such that `A x ≤ b` and `x ≥ 0` is
   always less or equal to `bᵀy` such that `Aᵀ y ≥ c` and `y ≥ 0`) is provided for matrices over any `OrderedCommRing`.
* `StandardLP.strongDuality`: The strong duality theorem (there exist vectors `x` and `y` such that
   the inequality from the weak duality theorem above is tight) is provided for matrices over any `LinearOrderedField`.

-/

/-- Linear program in the standard form. Variables are of type `J`. Conditions are indexed by type `I`. -/
structure StandardLP (I J R : Type*) where
  /-- The left-hand-side matrix -/
  A : Matrix I J R
  /-- The right-hand-side vector -/
  b : I → R
  /-- The objective function coefficients -/
  c : J → R

open scoped Matrix
variable {I J R : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def StandardLP.IsSolution [OrderedSemiring R] (P : StandardLP I J R) (x : J → R) : Prop :=
  P.A *ᵥ x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`. -/
def StandardLP.IsFeasible [OrderedSemiring R] (P : StandardLP I J R) : Prop :=
  ∃ x : J → R, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `v`. -/
def StandardLP.Reaches [OrderedSemiring R] (P : StandardLP I J R) (v : R) : Prop :=
  ∃ x : J → R, P.IsSolution x ∧ P.c ⬝ᵥ x = v

/-- Dualizes a linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original cost function gets flipped signs as well and becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new vector of objective function coefficients. -/
def StandardLP.dualize [Ring R] (P : StandardLP I J R) : StandardLP J I R :=
  ⟨-P.Aᵀ, -P.c, P.b⟩


lemma Matrix.transpose_mulVec_dotProduct [CommSemiring R] (M : Matrix I J R) (v : I → R) (w : J → R) :
    Mᵀ *ᵥ v ⬝ᵥ w = M *ᵥ w ⬝ᵥ v := by
  rw [Matrix.dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- All objective values reached by the prim are all less or equal to all objective values reached by the dual. -/
theorem StandardLP.weakDuality [OrderedCommRing R] {P : StandardLP I J R}
    {p : R} (hP : P.Reaches p) {q : R} (hQ : P.dualize.Reaches q) :
    p ≤ q := by
  obtain ⟨x, ⟨hxb, h0x⟩, rfl⟩ := hP
  obtain ⟨y, ⟨hyc, h0y⟩, rfl⟩ := hQ
  have hyxx : -P.Aᵀ *ᵥ y ⬝ᵥ x ≤ -P.c ⬝ᵥ x := Matrix.dotProduct_le_dotProduct_of_nonneg_right hyc h0x
  rw [Matrix.neg_mulVec, Matrix.neg_dotProduct, Matrix.neg_dotProduct, neg_le_neg_iff, Matrix.transpose_mulVec_dotProduct] at hyxx
  exact hyxx.trans (Matrix.dotProduct_le_dotProduct_of_nonneg_right hxb h0y)

lemma StandardLP.unbounded_prim_makes_dual_infeasible_tial [OrderedCommRing R]
    {P : StandardLP I J R} (hP : ∀ r : R, ∃ p : R, r < p ∧ P.Reaches p) :
    ¬ P.dualize.IsFeasible :=
  fun ⟨y, hAy, hy⟩ =>
    let ⟨_, hb, hP'⟩ := hP (P.b ⬝ᵥ y)
    ((P.weakDuality hP' ⟨y, ⟨hAy, hy⟩, rfl⟩).trans_lt hb).false

lemma StandardLP.unbounded_dual_makes_prim_infeasible_tial [OrderedCommRing R]
    {P : StandardLP I J R} (hQ : ∀ r : R, ∃ q : R, q < r ∧ P.dualize.Reaches q) :
    ¬ P.IsFeasible :=
  fun ⟨x, hAx, hx⟩ =>
    let ⟨_, hc, hQ'⟩ := hQ (P.c ⬝ᵥ x)
    ((P.weakDuality ⟨x, ⟨hAx, hx⟩, rfl⟩ hQ').trans_lt hc).false

lemma StandardLP.feasible_dual_makes_prim_bounded_tial [OrderedCommRing R]
    {P : StandardLP I J R} (hQ : P.dualize.IsFeasible) :
    ∃ r : R, ∀ p : R, r < p → ¬P.Reaches p := by
  by_contra! contr
  exact P.unbounded_prim_makes_dual_infeasible_tial contr hQ

lemma StandardLP.feasible_prim_makes_dual_bounded_tial [OrderedCommRing R]
    {P : StandardLP I J R} (hP : P.IsFeasible) :
    ∃ r : R, ∀ q : R, q < r → ¬P.dualize.Reaches q := by
  by_contra! contr
  exact P.unbounded_dual_makes_prim_infeasible_tial contr hP

lemma StandardLP.unbounded_prim_makes_dual_infeasible [LinearOrderedCommRing R]
    {P : StandardLP I J R} (hP : ∀ r : R, ∃ p : R, r ≤ p ∧ P.Reaches p) :
    ¬ P.dualize.IsFeasible :=
  P.unbounded_prim_makes_dual_infeasible_tial (fun r : R =>
    let ⟨p, hrp, hPp⟩ := hP (r + 1)
    ⟨p, (lt_add_one r).trans_le hrp, hPp⟩)

lemma StandardLP.unbounded_dual_makes_prim_infeasible [LinearOrderedCommRing R]
    {P : StandardLP I J R} (hQ : ∀ r : R, ∃ q : R, q ≤ r ∧ P.dualize.Reaches q) :
    ¬ P.IsFeasible :=
  P.unbounded_dual_makes_prim_infeasible_tial (fun r : R =>
    let ⟨q, hqr, hQq⟩ := hQ (r - 1)
    ⟨q, (hqr.trans_lt (sub_one_lt r)), hQq⟩)

theorem StandardLP.feasible_dual_makes_prim_bounded [LinearOrderedCommRing R]
    {P : StandardLP I J R} (hQ : P.dualize.IsFeasible) :
    ∃ r : R, ∀ p : R, P.Reaches p → p < r := by
  by_contra! contr
  simp_rw [and_comm] at contr
  exact P.unbounded_prim_makes_dual_infeasible contr hQ

theorem StandardLP.feasible_prim_makes_dual_bounded [LinearOrderedCommRing R]
    {P : StandardLP I J R} (hP : P.IsFeasible) :
    ∃ r : R, ∀ q : R, P.dualize.Reaches q → r < q := by
  by_contra! contr
  simp_rw [and_comm] at contr
  exact P.unbounded_dual_makes_prim_infeasible contr hP

/-- If both the prim and the dual are feasible, there is an objective value that is reached
    by both the prim and the dual. -/
theorem StandardLP.strongDuality [DecidableEq I] [DecidableEq J] [LinearOrderedField R]
    {P : StandardLP I J R} (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : R, P.Reaches r ∧ P.dualize.Reaches r := by
  cases
    or_of_neq
      (inequalityFarkas
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.row (Sum.elim (-P.c) P.b)))
        (Sum.elim (Sum.elim P.b (-P.c)) 0)) with
  | inl case_x =>
    obtain ⟨x, hx, hAx⟩ := case_x
    rw [Matrix.fromRows_mulVec, Matrix.fromBlocks_mulVec, Sum.elim_le_elim_iff, Sum.elim_le_elim_iff] at hAx
    have hPx : P.Reaches (P.c ⬝ᵥ x ∘ Sum.inl)
    · exact ⟨x ∘ Sum.inl, ⟨by simpa using hAx.left.left, nneg_comp hx Sum.inl⟩, rfl⟩
    have hQx : P.dualize.Reaches (P.b ⬝ᵥ x ∘ Sum.inr)
    · exact ⟨x ∘ Sum.inr, ⟨by simpa using hAx.left.right, nneg_comp hx Sum.inr⟩, rfl⟩
    have objectives_eq : P.b ⬝ᵥ (x ∘ Sum.inr) = P.c ⬝ᵥ (x ∘ Sum.inl)
    · apply eq_of_le_of_le
      · rw [←add_zero (P.c ⬝ᵥ x ∘ Sum.inl), ←neg_add_le_iff_le_add, ←Matrix.neg_dotProduct, ←Matrix.sum_elim_dotProduct_sum_elim]
        simpa using hAx.right ()
      · exact P.weakDuality hPx hQx
    rw [objectives_eq] at hQx
    exact ⟨P.c ⬝ᵥ (x ∘ Sum.inl), hPx, hQx⟩
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
      hcb, le_add_neg_iff_le, Sum.elim_le_elim_iff
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
        refine P.unbounded_prim_makes_dual_infeasible ?_ hQ
        unfold StandardLP.Reaches
        by_contra! contr
        obtain ⟨s, hs⟩ := contr
        obtain ⟨p, hAp, hp⟩ := hP
        if s_big : P.c ⬝ᵥ p ≤ s then
          have coef_nneg : 0 ≤ (s - P.c ⬝ᵥ p) / (P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr)
          · exact div_nonneg (sub_nonneg_of_le s_big) hcylr.le
          refine hs (P.c ⬝ᵥ (p + ((s - P.c ⬝ᵥ p) / (P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr)) • (y ∘ Sum.inl) ∘ Sum.inr)) (by rw [
              Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul,
              div_mul, div_self hcylr.ne.symm, div_one, add_sub, add_comm, ←add_sub, sub_self, add_zero
            ]) (p + ((s - P.c ⬝ᵥ p) / (P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr)) • (y ∘ Sum.inl) ∘ Sum.inr) ?_ rfl
          constructor
          · rw [Matrix.mulVec_add, ←add_zero P.b]
            apply add_le_add hAp
            rw [Matrix.mulVec_smul]
            exact smul_nonpos_of_nonneg_of_nonpos coef_nneg hAyc
          · rw [←add_zero 0]
            apply add_le_add hp
            apply smul_nonneg coef_nneg
            apply nneg_comp hy
        else
          exact hs (P.c ⬝ᵥ p) (le_of_not_ge s_big) p ⟨hAp, hp⟩ rfl
      else
        have hbyll : P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl < 0
        · rw [not_lt] at hcylr
          exact hbcy.trans_le hcylr
        clear hcylr
        refine P.unbounded_dual_makes_prim_infeasible ?_ hP
        unfold StandardLP.Reaches
        by_contra! contr
        obtain ⟨s, hs⟩ := contr
        obtain ⟨q, hAq, hq⟩ := hQ
        if s_low : s ≤ P.b ⬝ᵥ q then
          have coef_nneg : 0 ≤ (s - P.b ⬝ᵥ q) / P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl
          · exact div_nonneg_of_nonpos (sub_nonpos_of_le s_low) hbyll.le
          refine hs (P.b ⬝ᵥ (q + ((s - P.b ⬝ᵥ q) / (P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl)) • (y ∘ Sum.inl) ∘ Sum.inl)) (by rw [
              Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul,
              div_mul, div_self hbyll.ne, div_one, add_sub, add_comm, ←add_sub, sub_self, add_zero
            ]) (q + ((s - P.b ⬝ᵥ q) / (P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl)) • (y ∘ Sum.inl) ∘ Sum.inl) ?_ rfl
          constructor
          · rw [Matrix.mulVec_add, ←add_zero P.dualize.b]
            apply add_le_add hAq
            rw [Matrix.mulVec_smul]
            apply smul_nonpos_of_nonneg_of_nonpos coef_nneg
            simpa [StandardLP.dualize, Matrix.neg_mulVec] using neg_nonpos_of_nonneg hAyb
          · rw [←add_zero 0]
            apply add_le_add hq
            apply smul_nonneg coef_nneg
            apply nneg_comp hy
        else
          exact hs (P.b ⬝ᵥ q) (le_of_not_ge s_low) q ⟨hAq, hq⟩ rfl
    have hbcy' : (y (Sum.inr ()) • P.b) ⬝ᵥ ((y ∘ Sum.inl)) ∘ Sum.inl < (y (Sum.inr ()) • P.c) ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr
    · rw [←mul_lt_mul_left y_last_pos] at hbcy
      convert hbcy <;> simp
    have hAyb' : y (Sum.inr ()) • P.c ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr ≤ P.Aᵀ *ᵥ (y ∘ Sum.inl) ∘ Sum.inl ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inr
    · apply Matrix.dotProduct_le_dotProduct_of_nonneg_right hAyb
      apply nneg_comp hy
    have hAyc' : P.A *ᵥ (y ∘ Sum.inl) ∘ Sum.inr ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl ≤ y (Sum.inr ()) • P.b ⬝ᵥ (y ∘ Sum.inl) ∘ Sum.inl
    · rw [smul_neg, Matrix.neg_mulVec, neg_le_neg_iff] at hAyc
      apply Matrix.dotProduct_le_dotProduct_of_nonneg_right hAyc
      apply nneg_comp hy
    rw [Matrix.transpose_mulVec_dotProduct] at hAyb'
    exact ((hbcy'.trans_le hAyb').trans_le hAyc').false

#print axioms StandardLP.strongDuality
