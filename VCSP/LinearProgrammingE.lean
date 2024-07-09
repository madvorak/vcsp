import Mathlib.Algebra.Order.Pi
import VCSP.FarkasSpecial

open scoped Matrix


/-- Linear program over `ℚ∞` in the standard form (system of linear inequalities with nonnegative `ℚ` variables).
    Variables are of type `J`. Conditions are indexed by type `I`. -/
structure ExtendedLP (I J : Type*) where
  /-- The left-hand-side matrix. -/
  A : Matrix I J ℚ∞
  /-- The right-hand-side vector. -/
  b : I → ℚ∞
  /-- The objective function coefficients. -/
  c : J → ℚ∞
  /-- No `⊥` and `⊤` in the same row. -/
  hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤)
  /-- No `⊥` and `⊤` in the same column. -/
  hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤)
  /-- No `⊥` in the right-hand-side vector. -/
  hbi : ¬∃ i : I, b i = ⊥
  /-- No `⊥` in the objective function coefficients. -/
  hcj : ¬∃ j : J, c j = ⊥
  /-- No `⊤` in the row where the right-hand-side vector has `⊤`. -/
  hAb : ¬∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤
  /-- No `⊥` in the column where the objective function has `⊤`. -/
  hAc : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ c j = ⊤

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution (P : ExtendedLP I J) (x : J → ℚ) : Prop :=
  P.A ₘ* x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`.
    Linear program `P` is considered feasible even if all solutions yield `⊥` as the objective. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. Note that `⊤` can be reached but `⊥` cannot. -/
def ExtendedLP.Reaches (P : ExtendedLP I J) (r : ℚ∞) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x ∧ P.c ᵥ⬝ x = r

/-- Linear program `P` is bounded by `r` iff all values reached by `P` are less or equal to `r`.
    Linear program `P` is always bounded by `⊤` which is allowed by this definition. -/
def ExtendedLP.IsBoundedBy (P : ExtendedLP I J) (r : ℚ∞) : Prop :=
  ∀ p : ℚ∞, P.Reaches p → p ≤ r

/-- Dualize a linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function. -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨-P.Aᵀ, P.c, P.b, by aeply P.hAj, by aeply P.hAi, P.hcj, P.hbi, by aeply P.hAc, by aeply P.hAb⟩

lemma Matrix.dotProd_eq_bot {v : J → ℚ∞} {w : J → ℚ} (hw : 0 ≤ w) (hvw : v ᵥ⬝ w = ⊥) :
    ∃ j : J, v j = ⊥ := by
  by_contra! contr
  exact Matrix.no_bot_dotProd_nneg contr hw hvw

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

lemma Matrix.fromRows_mulWeig {I₁ I₂ : Type*} (A₁ : Matrix I₁ J ℚ∞) (A₂ : Matrix I₂ J ℚ∞) (v : J → ℚ) :
    Matrix.fromRows A₁ A₂ ₘ* v = Sum.elim (A₁ ₘ* v) (A₂ ₘ* v) := by
  ext i
  cases i <;> rfl

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

lemma Matrix.fromColumns_mulWeig_sumElim {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (A₁ : Matrix I J₁ ℚ∞) (A₂ : Matrix I J₂ ℚ∞) (v₁ : J₁ → ℚ) (v₂ : J₂ → ℚ) :
    Matrix.fromColumns A₁ A₂ ₘ* Sum.elim v₁ v₂ = A₁ ₘ* v₁ + A₂ ₘ* v₂ := by
  ext
  simp [Matrix.fromColumns, Matrix.mulWeig, Matrix.dotProd]

theorem ExtendedLP.weakDuality [DecidableEq I] [DecidableEq J] {P : ExtendedLP I J}
    {p : ℚ∞} (hP : P.Reaches p) {q : ℚ∞} (hQ : P.dualize.Reaches q) :
    0 ≤ p + q := by
  obtain ⟨A, b, c, hai, haj, hbi, hcj, hAb, hAc⟩ := P
  obtain ⟨x, ⟨hxb, h0x⟩, rfl⟩ := hP
  obtain ⟨y, ⟨hyc, h0y⟩, rfl⟩ := hQ
  dsimp [ExtendedLP.dualize] at *
  by_contra contr
  apply
    not_and_of_neq
      (extendedFarkas
        (Matrix.fromRows A (Matrix.ro1 c))
        (Sum.elim b (fun _ => c ᵥ⬝ x))
        (by
          intro ⟨i, ⟨s, his⟩, ⟨t, hit⟩⟩
          cases i with
          | inl i' => exact hai ⟨i', ⟨s, his⟩, ⟨t, hit⟩⟩
          | inr => exact hcj ⟨s, his⟩
        )
        (by
          intro ⟨j, ⟨s, hjs⟩, ⟨t, hjt⟩⟩
          cases s with
          | inl iₛ =>
            cases t with
            | inl iₜ => exact haj ⟨j, ⟨iₛ, hjs⟩, ⟨iₜ, hjt⟩⟩
            | inr => exact hAc ⟨j, ⟨iₛ, hjs⟩, hjt⟩
          | inr => exact hcj ⟨j, hjs⟩
        )
        (by
          intro ⟨i, ⟨j, hij⟩, hi⟩
          cases i with
          | inl i' => exact hAb ⟨i', ⟨j, hij⟩, hi⟩
          | inr =>
            simp at hij hi
            push_neg at contr
            rw [hi] at contr
            match hby : b ᵥ⬝ y with
            | ⊥ =>
              exact Matrix.no_bot_dotProd_nneg (by simpa using hbi) h0y hby
            | ⊤ =>
              rw [hby] at contr
              change contr to ⊤ + ⊤ < 0
              simp at contr
            | (q : ℚ) =>
              rw [hby] at contr
              change contr to ⊤ + q.toERat < 0
              simp at contr
        )
        (by
          intro ⟨i, ⟨j, hij⟩, hi⟩
          cases i with
          | inl i' => exact hbi ⟨i', hi⟩
          | inr => exact hcj ⟨j, hij⟩
        )
      )
  constructor
  · use x
    constructor
    · exact h0x
    rw [Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff]
    exact ⟨hxb, by rfl⟩
  · use Sum.elim y 1
    constructor
    · rw [Sum.nonneg_elim_iff]
      exact ⟨h0y, zero_le_one⟩
    constructor
    · rw [Matrix.transpose_fromRows, Matrix.fromColumns_neg]
      suffices : (-Aᵀ) ₘ* y + (-c) ≤ 0
      · rw [Matrix.fromColumns_mulWeig_sumElim]
        convert this -- TODO cleanup
        ext j
        simp [Matrix.mulWeig, Matrix.dotProd]
        apply ERat.one_mul
      rwa [ERat.vec_sub_nonpos_iff']
    · suffices : b ᵥ⬝ y + c ᵥ⬝ x < 0
      · rw [Matrix.sumElim_dotProd_sumElim]
        conv => lhs; right; simp [Matrix.dotProd]
        show b ᵥ⬝ y + 1 * (c ᵥ⬝ x) < 0
        rwa [ERat.one_mul]
      push_neg at contr
      rw [add_comm]
      exact contr

#print axioms ExtendedLP.weakDuality

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

lemma Matrix.zero_mulWeig (v : J → ℚ) : (0 : Matrix I J ℚ∞) ₘ* v = 0 := by
  ext
  simp [Matrix.mulWeig, Matrix.dotProd]

lemma Matrix.sumElim_dotProd (u : I → ℚ∞) (v : J → ℚ∞) (x : (I ⊕ J) → ℚ) :
    Sum.elim u v ᵥ⬝ x = u ᵥ⬝ (x ∘ Sum.inl) + v ᵥ⬝ (x ∘ Sum.inr) := by
  simp [Matrix.dotProd]

lemma ERat.smul_smul {k : ℚ} (hk : 0 < k) (v : ℚ∞) (w : ℚ) :
    w • (k • v) = k • (w • v) := by
  match v with
  | ⊥ =>
    show w.toERat * (k.toERat * ⊥) = k.toERat * (w.toERat * ⊥)
    rw [ERat.coe_mul_bot_of_nneg hk.le]
    if hw : 0 ≤ w then
      rw [ERat.coe_mul_bot_of_nneg hw, ERat.coe_mul_bot_of_nneg hk.le]
    else
      push_neg at hw
      rw [ERat.coe_mul_bot_of_neg hw, ERat.coe_mul_top_of_pos hk]
  | ⊤ =>
    show w.toERat * (k.toERat * ⊤) = k.toERat * (w.toERat * ⊤)
    rw [ERat.coe_mul_top_of_pos hk]
    if hwp : 0 < w then
      rw [ERat.coe_mul_top_of_pos hwp, ERat.coe_mul_top_of_pos hk]
    else if hw0 : w = 0 then
      rw [hw0, ERat.coe_zero, zero_mul top_ne_bot, ←ERat.coe_zero, ←ERat.coe_mul, mul_zero]
    else
      push_neg at hwp
      rw [ERat.coe_mul_top_of_neg (lt_of_le_of_ne hwp hw0), ERat.coe_mul_bot_of_nneg hk.le]
  | (q : ℚ) =>
    exact ERat.coe_eq_coe_iff.mpr (mul_left_comm w k q)

lemma ERat.smul_add {k : ℚ} (hk : 0 < k) (x y : ℚ∞) :
    k • (x + y) = k • x + k • y := by
  match x, y with
  | ⊥, _ =>
    show k.toERat * (⊥ + _) = k.toERat * ⊥ + k.toERat * _
    rw [ERat.bot_add, ERat.coe_mul_bot_of_nneg hk.le, ERat.bot_add]
  | _, ⊥ =>
    show k.toERat * (_ + ⊥) = k.toERat * _ + k.toERat * ⊥
    rw [ERat.add_bot, ERat.coe_mul_bot_of_nneg hk.le, ERat.add_bot]
  | (p : ℚ), (q : ℚ) =>
    show k.toERat * (p.toERat + q.toERat) = k.toERat * p.toERat + k.toERat * q.toERat
    rw [←ERat.coe_add, ←ERat.coe_mul, ←ERat.coe_mul, ←ERat.coe_mul, ←ERat.coe_add, mul_add]
  | (p : ℚ), ⊤ =>
    rw [ERat.coe_add_top, show k • ⊤ = (⊤ : ℚ∞) from ERat.coe_mul_top_of_pos hk]
    show ⊤ = (k * p).toERat + ⊤
    rw [ERat.coe_add_top]
  | ⊤, (q : ℚ) =>
    rw [ERat.top_add_coe, show k • ⊤ = (⊤ : ℚ∞) from ERat.coe_mul_top_of_pos hk]
    show ⊤ = ⊤ + (k * q).toERat
    rw [ERat.top_add_coe]
  | ⊤, ⊤ =>
    rw [ERat.top_add_top, show k • ⊤ = (⊤ : ℚ∞) from ERat.coe_mul_top_of_pos hk, ERat.top_add_top]

lemma Multiset.smul_ERat_sum {k : ℚ} (hk : 0 < k) (s : Multiset ℚ∞) :
    s.summap (k • ·) = k • s.sum := by
  induction s using Multiset.induction with
  | empty => simp [Multiset.summap]
  | cons a m ih => simp [Multiset.summap, ERat.smul_add hk, ←ih]

lemma Finset.smul_ERat_sum {k : ℚ} (hk : 0 < k) (v : J → ℚ∞) :
    ∑ j : J, k • v j = k • ∑ j : J, v j := by
  convert Multiset.smul_ERat_sum hk (Finset.univ.val.map v)
  simp [Multiset.summap]

lemma Matrix.ERat_smul_dotProd {k : ℚ} (hk : 0 < k) (v : J → ℚ∞) (w : J → ℚ) :
    (k • v) ᵥ⬝ w = k • (v ᵥ⬝ w) := by
  show ∑ j : J, w j • k • v j = k • ∑ j : J, w j • v j
  conv => lhs; congr; rfl; ext i; rw [ERat.smul_smul hk]
  apply Finset.smul_ERat_sum hk

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

theorem ExtendedLP.strongDuality [DecidableEq I] [DecidableEq J] {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : ℚ, P.Reaches (-r) ∧ P.dualize.Reaches r := by
  obtain ⟨A, b, c, hai, haj, hbi, hcj, hAb, hAc⟩ := P
  dsimp only [dualize, Reaches, IsSolution, IsFeasible] at hP hQ ⊢
  cases
    or_of_neq
      (extendedFarkas
        (Matrix.fromRows
          (Matrix.fromBlocks A 0 0 (-Aᵀ))
          (Matrix.ro1 (Sum.elim c b)))
        (Sum.elim (Sum.elim b c) 0)
        sorry sorry sorry sorry
      ) with
  | inl case_x =>
    obtain ⟨x, hx, hAx⟩ := case_x
    rw [
      Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
      ←Sum.elim_comp_inl_inr x, Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add
    ] at hAx
    set y := x ∘ Sum.inr
    set x := x ∘ Sum.inl
    sorry
  | inr case_y =>
    obtain ⟨y, hy, hAy, hbcy⟩ := case_y
    exfalso
    rw [
      Matrix.transpose_fromRows, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero,
      Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.transpose_row, Matrix.fromColumns_neg,
      ←Sum.elim_comp_inl_inr y, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.fromBlocks_neg, Matrix.ERat_neg_neg, Matrix.ERat_neg_zero, Matrix.ERat_neg_zero, Matrix.neg_mulWeig,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig,
      ←Sum.elim_comp_inl_inr (y ∘ Sum.inl), Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add,
    ] at hAy
    rw [←Sum.elim_comp_inl_inr y, ←Sum.elim_comp_inl_inr (y ∘ Sum.inl)] at hbcy
    set z := y ∘ Sum.inr
    set x := (y ∘ Sum.inl) ∘ Sum.inr
    set y := (y ∘ Sum.inl) ∘ Sum.inl
    have y_last_pos : 0 < z
    · by_contra contr
      have last_zero : z = 0
      · have aux := (eq_of_le_of_not_lt (hy (Sum.inr 0)) (by rw [Pi.zero_apply]; simp [z]; sorry)).symm
        rw [Pi.zero_apply] at aux
        sorry --exact aux
      clear contr
      sorry
    sorry
