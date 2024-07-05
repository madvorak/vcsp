import Mathlib.Algebra.Order.Pi
import VCSP.FarkasSpecial

open scoped Matrix


/-- Linear program over `ℚ∞` in the standard form (system of linear inequalities with nonnegative `ℚ` variables).
    Variables are of type `J`. Conditions are indexed by type `I`. -/
structure ExtendedLP (I J : Type*) where
  /-- The left-hand-side matrix. -/
  A : Matrix I J ℚ∞
  /-- The right-hand-side vector. -/
  b : I → ℚ
  /-- The objective function coefficients. -/
  c : J → ℚ
  /-- No `⊥` and `⊤` in the same row. -/
  hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤)
  /-- No `⊥` and `⊤` in the same column. -/
  hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤)

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution (P : ExtendedLP I J) (x : J → ℚ) : Prop :=
  P.A ₘ* x ≤ Rat.toERat ∘ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`.
    Linear program `P` is considered feasible even if all solutions yield `⊥` as the objective. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. Note that `⊤` can be reached but `⊥` cannot. -/
def ExtendedLP.Reaches (P : ExtendedLP I J) (r : ℚ) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x ∧ P.c ⬝ᵥ x = r

/-- Linear program `P` is bounded by `r` iff all values reached by `P` are less or equal to `r`.
    Linear program `P` is always bounded by `⊤` which is allowed by this definition. -/
def ExtendedLP.IsBoundedBy (P : ExtendedLP I J) (r : ℚ) : Prop :=
  ∀ p : ℚ, P.Reaches p → p ≤ r

lemma Matrix.dotProd_eq_bot {v : J → ℚ∞} {w : J → ℚ} (hw : 0 ≤ w) (hvw : v ᵥ⬝ w = ⊥) :
    ∃ j : J, v j = ⊥ := by
  by_contra! contr
  exact Matrix.no_bot_dotProd_nneg contr hw hvw

/-- Dualize a linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original cost function gets flipped signs as well and becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new vector of objective function coefficients. -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨-P.Aᵀ, -P.c, P.b, by {intro; apply P.hAj; aesop}, by {intro; apply P.hAi; aesop}⟩

lemma Matrix.ERat_neg_neg (A : Matrix I J ℚ∞) : -(-A) = A := by
  ext
  apply neg_neg

lemma Matrix.ERat_neg_zero : -(0 : Matrix I J ℚ∞) = 0 := by
  ext
  apply neg_zero

lemma Matrix.sumElim_dotProd_sumElim (u : I → ℚ∞) (v : J → ℚ∞) (x : I → ℚ) (y : J → ℚ) :
    Sum.elim u v ᵥ⬝ Sum.elim x y = u ᵥ⬝ x + v ᵥ⬝ y := by
  simp [Matrix.dotProd]

lemma Matrix.zero_dotProd (w : J → ℚ) : (0 : J → ℚ∞) ᵥ⬝ w = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact smul_zero (w j)

lemma Matrix.dotProd_le_dotProd_of_nneg_right {u v : J → ℚ∞} {w : J → ℚ} (huv : u ≤ v) (hw : 0 ≤ w) :
    u ᵥ⬝ w ≤ v ᵥ⬝ w := by
  apply Finset.sum_le_sum
  intro i _
  have huvi := huv i
  show (w i).toERat * u i ≤ (w i).toERat * v i
  match hui : u i with
  | ⊥ =>
    rw [ERat.coe_mul_bot_of_nneg (hw i)]
    apply bot_le
  | ⊤ =>
    match hvi : v i with
    | ⊥ =>
      exfalso
      rw [hui, hvi] at huvi
      exact (bot_lt_top.trans_le huvi).false
    | ⊤ =>
      rfl
    | (q : ℚ) =>
      exfalso
      rw [hui, hvi] at huvi
      exact ((ERat.coe_lt_top q).trans_le huvi).false
  | (p : ℚ) =>
    match hvi : v i with
    | ⊥ =>
      exfalso
      rw [hui, hvi] at huvi
      exact ((ERat.bot_lt_coe p).trans_le huvi).false
    | ⊤ =>
      if hwi0 : w i = 0 then
        rw [hwi0, ERat.coe_zero, ERat.zero_mul (ERat.coe_ne_bot p), ERat.zero_mul bot_lt_top.ne.symm]
      else
        rw [ERat.coe_mul_top_of_pos (lt_of_le_of_ne (hw i) (Ne.symm hwi0))]
        apply le_top
    | (q : ℚ) =>
      rw [←ERat.coe_mul, ←ERat.coe_mul, ERat.coe_le_coe_iff]
      have hpq : p ≤ q
      · rw [←ERat.coe_le_coe_iff]
        rwa [hui, hvi] at huvi
      exact mul_le_mul_of_nonneg_left hpq (hw i)

-- TODO what assumptions do the following three lemmas need?

lemma Matrix.neg_dotProd (v : J → ℚ∞) (w : J → ℚ) : -v ᵥ⬝ w = -(v ᵥ⬝ w) := by
  sorry

lemma Matrix.neg_mulWeig (A : Matrix I J ℚ∞) (w : J → ℚ) : -A ₘ* w = -(A ₘ* w) := by
  ext
  apply Matrix.neg_dotProd

lemma Matrix.transpose_mulWeig_dotProd (M : Matrix I J ℚ∞) (v : I → ℚ) (w : J → ℚ) :
    Mᵀ ₘ* v ᵥ⬝ w = M ₘ* w ᵥ⬝ v := by
  show
    ∑ j : J, w j • ∑ i : I, v i • M i j = ∑ i : I, v i • ∑ j : J, w j • M i j
  show
    ∑ j : J, (w j).toERat * ∑ i : I, (v i).toERat * M i j =
    ∑ i : I, (v i).toERat * ∑ j : J, (w j).toERat * M i j
  sorry

theorem ExtendedLP.weakDuality {P : ExtendedLP I J} {p : ℚ} (hP : P.Reaches p) {q : ℚ} (hQ : P.dualize.Reaches q) :
    p ≤ q := by
  obtain ⟨x, ⟨hxb, h0x⟩, rfl⟩ := hP
  obtain ⟨y, ⟨hyc, h0y⟩, rfl⟩ := hQ
  sorry

lemma ERat.sub_nonpos_iff (p q : ℚ∞) : p - q ≤ 0 ↔ p ≤ q := by
  match p with
  | ⊥ => convert_to True ↔ True <;> simp
  | ⊤ => match q with
    | ⊥ => decide
    | ⊤ => decide
    | (_ : ℚ) => convert_to False ↔ False <;> simp
  | (_ : ℚ) => match q with
    | ⊥ => convert_to False ↔ False <;> simp
    | ⊤ => convert_to True ↔ True <;> simp
    | (_ : ℚ) => simp [ERat.coe_nonneg, sub_eq_add_neg, ←ERat.coe_neg, ←ERat.coe_add]

lemma ERat.sub_nonpos_iff' (p q : ℚ∞) : p + (-q) ≤ 0 ↔ p ≤ q := by
  simpa using ERat.sub_nonpos_iff p q

lemma ERat.vec_sub_nonpos_iff' (x y : I → ℚ∞) : x + (-y) ≤ 0 ↔ x ≤ y := by
  constructor <;> intro hxy i <;> simpa [ERat.sub_nonpos_iff'] using hxy i

lemma ERat.add_neg_lt_zero_iff {r s : ℚ∞} (neq_bot : r ≠ ⊥ ∨ s ≠ ⊥) (neq_top : r ≠ ⊤ ∨ s ≠ ⊤) :
    r + (-s) < 0 ↔ r < s := by
  match s with
  | ⊥ => match r with
    | ⊥ => simp at neq_bot
    | ⊤ => convert_to False ↔ False <;> simp
    | (p : ℚ) => convert_to False ↔ False <;> simp
  | ⊤ => match r with
    | ⊥ => convert_to True ↔ True <;> simp
    | ⊤ => simp at neq_top
    | (p : ℚ) => convert_to True ↔ True <;> simp
  | (q : ℚ) => match r with
    | ⊥ => convert_to True ↔ True <;> simp
    | ⊤ => convert_to False ↔ False <;> simp [←sub_eq_add_neg]
    | (p : ℚ) => simp [←ERat.coe_neg, ←ERat.coe_add]

lemma ERat.smul_lt_smul_left {x : ℚ} (hx : 0 < x) (y z : ℚ∞) :
    x • y < x • z ↔ y < z := by
  show x.toERat * y < x.toERat * z ↔ y < z
  match z with
  | ⊥ =>
    convert_to False ↔ False
    · rw [ERat.coe_mul_bot_of_nneg hx.le, iff_false]
      apply not_lt_bot
    · simp
    rfl
  | ⊤ =>
    match y with
    | ⊥ =>
      convert_to True ↔ True
      · rw [ERat.coe_mul_top_of_pos hx, ERat.coe_mul_bot_of_nneg hx.le, iff_true]
        apply bot_lt_top
      · simp
      rfl
    | ⊤ =>
      convert_to False ↔ False
      · apply lt_self_iff_false
      · apply lt_self_iff_false
      rfl
    | (p : ℚ) =>
      convert_to True ↔ True
      · rw [ERat.coe_mul_top_of_pos hx, ←ERat.coe_mul, iff_true]
        apply coe_lt_top
      · simp
      rfl
  | (q : ℚ) =>
    match y with
    | ⊥ =>
      convert_to True ↔ True
      · rw [ERat.coe_mul_bot_of_nneg hx.le, ←ERat.coe_mul, iff_true]
        apply bot_lt_coe
      · simp
      rfl
    | ⊤ =>
      convert_to False ↔ False
      · rw [ERat.coe_mul_top_of_pos hx, iff_false]
        apply not_top_lt
      · simp
      rfl
    | (p : ℚ) =>
      rw [←ERat.coe_mul, ←ERat.coe_mul, ERat.coe_lt_coe_iff, ERat.coe_lt_coe_iff]
      exact mul_lt_mul_left hx

lemma ERat.smul_neg {x : ℚ} {y : ℚ∞} (hxy : x = 0 → y ≠ ⊥ ∧ y ≠ ⊤) :
    x • (-y) = -(x • y) := by
  show x.toERat * (-y) = -(x.toERat * y)
  match y with
  | ⊥ =>
    rw [neg_bot]
    if hx : 0 < x then
      rw [ERat.coe_mul_top_of_pos hx, ERat.coe_mul_bot_of_nneg hx.le, neg_bot]
    else
      if hx' : x < 0 then
        rw [ERat.coe_mul_bot_of_neg hx', ERat.coe_mul_top_of_neg hx', neg_top]
      else
        exfalso
        simp [show x = 0 by linarith] at hxy
  | ⊤ =>
    rw [neg_top]
    if hx : 0 < x then
      rw [ERat.coe_mul_top_of_pos hx, ERat.coe_mul_bot_of_nneg hx.le, neg_top]
    else
      if hx' : x < 0 then
        rw [ERat.coe_mul_bot_of_neg hx', ERat.coe_mul_top_of_neg hx', neg_bot]
      else
        exfalso
        simp [show x = 0 by linarith] at hxy
  | (q : ℚ) =>
    rw [←ERat.coe_mul, ←ERat.coe_neg, ←ERat.coe_mul, mul_neg, ERat.coe_neg]

lemma ERat.pos_smul_neg {x : ℚ} (hx : 0 < x) (y : ℚ∞) :
    x • (-y) = -(x • y) := by
  apply ERat.smul_neg
  intro h0
  exfalso
  exact (h0 ▸ hx).false

lemma ERat.pos_smul_neg_vec {x : ℚ} (hx : 0 < x) (y : I → ℚ∞) :
    x • (-y) = -(x • y) := by
  ext i
  exact ERat.pos_smul_neg hx (y i)

lemma ERat.vec_zero_smul {a : I → ℚ∞} (ha : ∀ i, a i ≠ ⊥) : (0 : ℚ) • a = 0 := by
  ext i
  exact ERat.zero_mul (ha i)

lemma Matrix.fromRows_mulWeig {I₁ I₂ : Type*} (A₁ : Matrix I₁ J ℚ∞) (A₂ : Matrix I₂ J ℚ∞) (v : J → ℚ) :
    Matrix.fromRows A₁ A₂ ₘ* v = Sum.elim (A₁ ₘ* v) (A₂ ₘ* v) := by
  ext i
  cases i <;> rfl

lemma Matrix.fromColumns_mulWeig_sumElim {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (A₁ : Matrix I J₁ ℚ∞) (A₂ : Matrix I J₂ ℚ∞) (v₁ : J₁ → ℚ) (v₂ : J₂ → ℚ) :
    Matrix.fromColumns A₁ A₂ ₘ* Sum.elim v₁ v₂ = A₁ ₘ* v₁ + A₂ ₘ* v₂ := by
  ext
  simp [Matrix.fromColumns, Matrix.mulWeig, Matrix.dotProd]

lemma Matrix.zero_mulWeig (v : J → ℚ) : (0 : Matrix I J ℚ∞) ₘ* v = 0 := by
  ext
  simp [Matrix.mulWeig, Matrix.dotProd]

lemma Matrix.sumElim_dotProd (u : I → ℚ∞) (v : J → ℚ∞) (x : (I ⊕ J) → ℚ) :
    Sum.elim u v ᵥ⬝ x = u ᵥ⬝ (x ∘ Sum.inl) + v ᵥ⬝ (x ∘ Sum.inr) := by
  simp [Matrix.dotProd]

lemma Matrix.ERat_smul_dotProd (c : ℚ) (v : J → ℚ∞) (w : J → ℚ) : -- TODO ass?
    (c • v) ᵥ⬝ w = c • (v ᵥ⬝ w) := by
  sorry

lemma Multiset.sum_neq_ERat_top {s : Multiset ℚ∞} (hs : ⊤ ∉ s) : s.sum ≠ ⊤ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.sum_cons]
    match a with
    | ⊥ => simp
    | ⊤ => simp at hs
    | (q : ℚ) => match hm : m.sum with
      | ⊥ => simp
      | ⊤ => exact (ih (by simpa using hs) hm).elim
      | (p : ℚ) => simp [←ERat.coe_add]

lemma Matrix.no_top_dotProd_nneg {v : I → ℚ∞} (hv : ∀ i, v i ≠ ⊤) {w : I → ℚ} (hw : 0 ≤ w) :
    v ᵥ⬝ w ≠ (⊤ : ℚ∞) := by
  apply Multiset.sum_neq_ERat_top
  rw [Multiset.mem_map]
  intro ⟨i, _, hi⟩
  match hvi : v i with
  | ⊥ => exact bot_ne_top (ERat.coe_mul_bot_of_nneg (hw i) ▸ hvi ▸ show (w i).toERat * v i = ⊤ from hi)
  | ⊤ => exact false_of_ne (hvi ▸ hv i)
  | (q : ℚ) => exact ERat.coe_ne_top _ (hvi ▸ hi)

variable [DecidableEq I] [DecidableEq J]

theorem ExtendedLP.strongDuality {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : ℚ, P.Reaches r ∧ P.dualize.Reaches r := by
  cases
    or_of_neq
      (extendedFarkas
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          ((Matrix.ro1 (Sum.elim (-P.c) P.b)).map Rat.toERat))
        (Rat.toERat ∘ Sum.elim (Sum.elim P.b (-P.c)) 0)
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              apply P.hAi
              use i
              constructor
              · cases s with
                | inl jₛ =>
                  use jₛ
                  simpa using hks
                | inr iₛ =>
                  exfalso
                  simp at hks
              · cases t with
                | inl jₜ =>
                  use jₜ
                  simpa using hkt
                | inr iₜ =>
                  exfalso
                  simp at hkt
            | inr j =>
              apply P.hAj
              use j
              constructor
              · cases t with
                | inl jₜ =>
                  exfalso
                  simp at hkt
                | inr iₜ =>
                  use iₜ
                  simpa using hkt
              · cases s with
                | inl jₛ =>
                  exfalso
                  simp at hks
                | inr iₛ =>
                  use iₛ
                  simpa using hks
          | inr => simp at hks
        )
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl j =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ =>
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ => exact P.hAj ⟨j, ⟨⟨iₛ, hks⟩, ⟨iₜ, hkt⟩⟩⟩
                  | inr jₜ => simp at hkt
                | inr => simp at hkt
              | inr jₛ => simp at hks
            | inr => simp at hks
          | inr i =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ => simp at hks
              | inr jₛ =>
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ => simp at hkt
                  | inr jₜ =>
                    apply P.hAi
                    use i
                    constructor
                    · use jₜ
                      simpa using hkt
                    · use jₛ
                      simpa using hks
                | inr => simp at hkt
            | inr => simp at hks
        )
        (by simp)
        (by simp)
      ) with
  | inl case_x =>
    obtain ⟨x, hx, hAx⟩ := case_x
    rw [Matrix.fromRows_mulWeig] at hAx
    sorry
  | inr case_y =>
    obtain ⟨y, hy, hAy, hbcy⟩ := case_y
    exfalso
    simp [Matrix.transpose_fromRows, Matrix.fromBlocks_transpose] at hAy
    have y_last_pos : 0 < y (Sum.inr 0)
    · by_contra contr
      have last_zero : y (Sum.inr 0) = 0
      · exact (eq_of_le_of_not_lt (hy (Sum.inr 0)) contr).symm
      clear contr
      sorry
    sorry
