import Mathlib.Algebra.Order.Pi
import VCSP.FarkasSpecial


/-- Linear program in the standard form. Variables are of type `J`. Conditions are indexed by type `I`. -/
structure ExtendedLP (I J : Type*) where
  /-- The left-hand-side matrix -/
  A : Matrix I J ℚ∞
  /-- The right-hand-side vector -/
  b : I → ℚ∞
  /-- The objective function coefficients -/
  c : J → ℚ∞

open scoped Matrix
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution (P : ExtendedLP I J) (x : J → ℚ) : Prop :=
  P.A ₘ* x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `v`. -/
def ExtendedLP.Reaches (P : ExtendedLP I J) (v : ℚ∞) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x ∧ P.c ᵥ⬝ x = v

/-- Dualizes a linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original cost function gets flipped signs as well and becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new vector of objective function coefficients. -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨-P.Aᵀ, -P.c, P.b⟩


lemma Matrix.transpose_mulWeig_dotProd (M : Matrix I J ℚ∞) (v : I → ℚ∞) (w : J → ℚ∞) :
    Mᵀ ₘ* v ᵥ⬝ w = M ₘ* w ᵥ⬝ v := by
  sorry -- rw [Matrix.dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- All objective values reached by the prim are all less or equal to all objective values reached by the dual. -/
theorem ExtendedLP.weakDuality {P : ExtendedLP I J}
    {p : ℚ∞} (hP : P.Reaches p) {q : ℚ∞} (hQ : P.dualize.Reaches q) :
    p ≤ q := by
  obtain ⟨x, ⟨hxb, h0x⟩, rfl⟩ := hP
  obtain ⟨y, ⟨hyc, h0y⟩, rfl⟩ := hQ
  have hyxx : -P.Aᵀ ₘ* y ᵥ⬝ x ≤ -P.c ᵥ⬝ x
  · sorry
  -- rw [Matrix.neg_mulWeig, Matrix.neg_dotProd, Matrix.neg_dotProd, neg_le_neg_iff, Matrix.transpose_mulWeig_dotProd] at hyxx
  sorry -- exact hyxx.trans (Matrix.dotProduct_le_dotProduct_of_nonneg_right hxb h0y)

lemma ExtendedLP.unbounded_prim_makes_dual_infeasible_aux
    {P : ExtendedLP I J} (hP : ∀ r : ℚ∞, ∃ p : ℚ∞, r < p ∧ P.Reaches p) :
    ¬ P.dualize.IsFeasible :=
    -- true but entirely pointless in `ℚ∞`
  fun ⟨y, hAy, hy⟩ =>
    let ⟨_, hb, hP'⟩ := hP (P.b ᵥ⬝ y)
    ((P.weakDuality hP' ⟨y, ⟨hAy, hy⟩, rfl⟩).trans_lt hb).false

lemma ExtendedLP.unbounded_dual_makes_prim_infeasible_aux
    {P : ExtendedLP I J} (hQ : ∀ r : ℚ∞, ∃ q : ℚ∞, q < r ∧ P.dualize.Reaches q) :
    ¬ P.IsFeasible :=
    -- true but entirely pointless in `ℚ∞`
  fun ⟨x, hAx, hx⟩ =>
    let ⟨_, hc, hQ'⟩ := hQ (P.c ᵥ⬝ x)
    ((P.weakDuality ⟨x, ⟨hAx, hx⟩, rfl⟩ hQ').trans_lt hc).false

lemma ExtendedLP.feasible_dual_makes_prim_bounded_aux
    {P : ExtendedLP I J} (hQ : P.dualize.IsFeasible) :
    ∃ r : ℚ∞, ∀ p : ℚ∞, r < p → ¬P.Reaches p := by
    -- true but entirely pointless in `ℚ∞`
  by_contra! contr
  exact P.unbounded_prim_makes_dual_infeasible_aux contr hQ

lemma ExtendedLP.feasible_prim_makes_dual_bounded_aux
    {P : ExtendedLP I J} (hP : P.IsFeasible) :
    ∃ r : ℚ∞, ∀ q : ℚ∞, q < r → ¬P.dualize.Reaches q := by
    -- true but entirely pointless in `ℚ∞`
  by_contra! contr
  exact P.unbounded_dual_makes_prim_infeasible_aux contr hP

lemma Matrix.fromRows_mulWeig {α γ m₁ m₂ n : Type*} [Fintype n] [AddCommMonoid α] [SMul γ α]
    (A₁ : Matrix m₁ n α) (A₂ : Matrix m₂ n α) (v : n → γ) :
    Matrix.fromRows A₁ A₂ ₘ* v = Sum.elim (A₁ ₘ* v) (A₂ ₘ* v) := by
  ext i
  cases i <;> rfl

lemma Matrix.fromBlocks_mulWeig {α γ m₁ m₂ n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂] [AddCommMonoid α] [SMul γ α]
    (A₁₁ : Matrix m₁ n₁ α) (A₁₂ : Matrix m₁ n₂ α) (A₂₁ : Matrix m₂ n₁ α) (A₂₂ : Matrix m₂ n₂ α) (v : Sum n₁ n₂ → γ) :
    Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ ₘ* v =
    Sum.elim (A₁₁ ₘ* v ∘ Sum.inl + A₁₂ ₘ* v ∘ Sum.inr) (A₂₁ ₘ* v ∘ Sum.inl + A₂₂ ₘ* v ∘ Sum.inr) := by
  ext i
  cases i <;> simp [Matrix.mulWeig, Matrix.dotProd]

lemma Matrix.zero_mulWeig {α γ m n : Type*} [Fintype n] [AddCommMonoid α] [SMul γ α]
    (v : n → γ) : -- TODO what about `⊥` ???
    (0 : Matrix m n α) ₘ* v = (0 : m → α) := by
  sorry

/-- If both the prim and the dual are feasible, there is an objective value that is reached
    by both the prim and the dual. -/
theorem ExtendedLP.strongDuality [DecidableEq I] [DecidableEq J]
    {P : ExtendedLP I J} (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible)
    (hA : P.A.Good) (hAT : P.Aᵀ.Good) (hb : ¬∃ i : I, P.b i = ⊤) (hc : ¬∃ j : J, P.c j = ⊥)
    (hAb' : P.A.Good' P.b) (hAb : P.A.Good'' P.b) (hAc' : P.Aᵀ.Good' P.c) (hAc : P.Aᵀ.Good'' P.c) :
    ∃ r : ℚ∞, P.Reaches r ∧ P.dualize.Reaches r := by
  cases
    or_of_neq
      (@extendedFarkas _ _ _ _
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.row (Sum.elim (-P.c) P.b)))
        (Sum.elim (Sum.elim P.b (-P.c)) 0)
        (by
          unfold Matrix.Good
          by_contra! contr
          obtain ⟨k, ⟨s, his⟩, ⟨t, hit⟩⟩ := contr
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              rw [Matrix.fromRows_apply_inl] at his hit
              /-
              rw [←Matrix.transpose_transpose P.A, ←@Matrix.transpose_zero I, ←@Matrix.transpose_zero J,
                  ←Matrix.transpose_neg, ←Matrix.fromBlocks_transpose,
                  Matrix.transpose_transpose, Matrix.transpose_apply
              ] at his-/
              sorry
            | inr j =>
              rw [Matrix.fromRows_apply_inl] at his hit
              sorry
          | inr _ =>
            rw [Matrix.fromRows_apply_inr, Matrix.row_apply] at his hit
            -- If finer conditions instead of `hb` and `hc` are desired, refine the commented code below.
            cases t with
            | inl jₜ =>
              rw [Sum.elim_inl, Pi.neg_apply, ERat.neg_eq_top_iff] at hit
              apply hc
              use jₜ
            | inr iₜ =>
              rw [Sum.elim_inr] at hit
              apply hb
              use iₜ
            /-
            cases s with
            | inl jₛ =>
              rw [Sum.elim_inl, Pi.neg_apply, ERat.neg_eq_bot_iff] at his
              cases t with
              | inl jₜ =>
                rw [Sum.elim_inl, Pi.neg_apply, ERat.neg_eq_top_iff] at hit
                apply hc
                use jₜ
              | inr iₜ =>
                rw [Sum.elim_inr] at hit
                apply hb
                use iₜ
            | inr iₛ =>
              rw [Sum.elim_inr] at his
              cases t with
              | inl jₜ =>
                rw [Sum.elim_inl, Pi.neg_apply, ERat.neg_eq_top_iff] at hit
                apply hc
                use jₜ
              | inr iₜ =>
                rw [Sum.elim_inr] at hit
                apply hb
                use iₜ
            -/
        )
        sorry sorry sorry) with
  | inl case_x =>
    obtain ⟨x, hx, hAx⟩ := case_x
    rw [
      Matrix.fromRows_mulWeig, Matrix.fromBlocks_mulWeig,
      elim_le_elim_iff, elim_le_elim_iff,
      Matrix.zero_mulWeig, Matrix.zero_mulWeig
    ] at hAx
    have hPx : P.Reaches (P.c ᵥ⬝ x ∘ Sum.inl)
    · exact ⟨x ∘ Sum.inl, ⟨by simpa using hAx.left.left, nneg_comp hx Sum.inl⟩, rfl⟩
    have hQx : P.dualize.Reaches (P.b ᵥ⬝ x ∘ Sum.inr)
    · exact ⟨x ∘ Sum.inr, ⟨by simpa using hAx.left.right, nneg_comp hx Sum.inr⟩, rfl⟩
    have objectives_eq : P.b ᵥ⬝ (x ∘ Sum.inr) = P.c ᵥ⬝ (x ∘ Sum.inl)
    · apply eq_of_le_of_le
      · rw [←add_zero (P.c ᵥ⬝ x ∘ Sum.inl), /-←neg_add_le_iff_le_add, ←Matrix.neg_dotProd, ←Matrix.sum_elim_dotProd_sum_elim-/]
        sorry --simpa using hAx.right ()
      · exact P.weakDuality hPx hQx
    exact ⟨P.c ᵥ⬝ (x ∘ Sum.inl), hPx, objectives_eq ▸ hQx⟩
  | inr case_y =>
    obtain ⟨y, hy, hAy, hbcy⟩ := case_y
    exfalso
    simp [Matrix.transpose_fromRows, Matrix.fromBlocks_transpose] at hAy
    have hcb : Matrix.col (Sum.elim (-P.c) P.b) ₘ* y ∘ Sum.inr = -(Sum.elim (y (Sum.inr ()) • P.c) (y (Sum.inr ()) • -P.b))
    · ext k
      sorry
    sorry
