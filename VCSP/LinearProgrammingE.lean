import Mathlib.Algebra.Order.Pi
import VCSP.FarkasSpecial


/-- Linear program over `ℚ∞` in the standard form (system of linear inequalities with `ℚ≥0` variables).
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

open scoped Matrix
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution (P : ExtendedLP I J) (x : J → ℚ≥0) : Prop :=
  P.A ₘ* x ≤ P.b

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`.
    Linear program `P` is considered feasible even if all solutions yield `⊥` as the objective. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ x : J → ℚ≥0, P.IsSolution x

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. Note that `⊤` can be reached but `⊥` cannot. -/
def ExtendedLP.Reaches (P : ExtendedLP I J) (r : ℚ∞) : Prop :=
  ∃ x : J → ℚ≥0, P.IsSolution x ∧ P.c ᵥ⬝ x = r

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


lemma Matrix.dotProd_eq_bot {v : J → ℚ∞} {w : J → ℚ≥0} (hvw : v ᵥ⬝ w = ⊥) :
    ∃ j : J, v j = ⊥ := by
  by_contra! contr
  exact Matrix.no_bot_dotProd_nneg contr w hvw

lemma Matrix.ERat_neg_neg (A : Matrix I J ℚ∞) : -(-A) = A := by
  ext
  apply neg_neg

lemma Matrix.ERat_neg_zero : -(0 : Matrix I J ℚ∞) = 0 := by
  ext
  apply neg_zero

lemma Matrix.sumElim_dotProd_sumElim (u : I → ℚ∞) (v : J → ℚ∞) (x : I → ℚ≥0) (y : J → ℚ≥0) :
    Sum.elim u v ᵥ⬝ Sum.elim x y = u ᵥ⬝ x + v ᵥ⬝ y := by
  simp [Matrix.dotProd]

lemma Matrix.zero_dotProd (w : J → ℚ≥0) : (0 : J → ℚ∞) ᵥ⬝ w = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact smul_zero (w j)

lemma Matrix.fromRows_mulWeig {I₁ I₂ : Type*} (A₁ : Matrix I₁ J ℚ∞) (A₂ : Matrix I₂ J ℚ∞) (v : J → ℚ≥0) :
    Matrix.fromRows A₁ A₂ ₘ* v = Sum.elim (A₁ ₘ* v) (A₂ ₘ* v) := by
  ext i
  cases i <;> rfl

lemma Matrix.dotProd_le_dotProd_of_nneg_right {u v : J → ℚ∞} (w : J → ℚ≥0) (huv : u ≤ v) :
    u ᵥ⬝ w ≤ v ᵥ⬝ w := by
  apply Finset.sum_le_sum
  intro i _
  have huvi := huv i
  match hui : u i with
  | ⊥ =>
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
        rw [hwi0, zero_smul_ERat_nonbot top_ne_bot, zero_smul_ERat_nonbot (ERat.coe_neq_bot p)]
      else
        rw [pos_smul_ERat_top (lt_of_le_of_ne (w i).property (Ne.symm hwi0))]
        apply le_top
    | (q : ℚ) =>
      have hpq : p ≤ q
      · rw [←ERat.coe_le_coe_iff]
        rwa [hui, hvi] at huvi
      exact ERat.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hpq (w i).property)

-- TODO what assumptions do the following three lemmas need?

lemma Matrix.neg_dotProd (v : J → ℚ∞) (w : J → ℚ≥0) : -v ᵥ⬝ w = -(v ᵥ⬝ w) := by
  sorry

lemma Matrix.neg_mulWeig (A : Matrix I J ℚ∞) (w : J → ℚ≥0) : -A ₘ* w = -(A ₘ* w) := by
  ext
  apply Matrix.neg_dotProd

lemma Matrix.transpose_mulWeig_dotProd (M : Matrix I J ℚ∞) (v : I → ℚ≥0) (w : J → ℚ≥0) :
    Mᵀ ₘ* v ᵥ⬝ w = M ₘ* w ᵥ⬝ v := by
  show
    ∑ j : J, w j • ∑ i : I, v i • M i j = ∑ i : I, v i • ∑ j : J, w j • M i j
  sorry

lemma ERat.sub_nonpos_iff (p q : ℚ∞) : p + (-q) ≤ 0 ↔ p ≤ q := by
  match p with
  | ⊥ => convert_to True ↔ True <;> simp
  | ⊤ => match q with
    | ⊥ => decide
    | ⊤ => decide
    | (_ : ℚ) => convert_to False ↔ False <;> simp [←ERat.coe_neg]
  | (_ : ℚ) => match q with
    | ⊥ => convert_to False ↔ False <;> simp
    | ⊤ => convert_to True ↔ True <;> simp
    | (_ : ℚ) => simp [←ERat.coe_neg, ←ERat.coe_add]

lemma ERat.vec_sub_nonpos_iff (x y : I → ℚ∞) : x + (-y) ≤ 0 ↔ x ≤ y := by
  constructor <;> intro hxy i <;> simpa [ERat.sub_nonpos_iff] using hxy i

lemma ERat.one_smul (a : ℚ∞) : (1 : ℚ≥0) • a = a :=
  match a with
  | ⊥ => rfl
  | ⊤ => rfl
  | (q : ℚ) => congr_arg Rat.toERat (one_mul q)

lemma Matrix.fromColumns_mulWeig_sumElim {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (A₁ : Matrix I J₁ ℚ∞) (A₂ : Matrix I J₂ ℚ∞) (v₁ : J₁ → ℚ≥0) (v₂ : J₂ → ℚ≥0) :
    Matrix.fromColumns A₁ A₂ ₘ* Sum.elim v₁ v₂ = A₁ ₘ* v₁ + A₂ ₘ* v₂ := by
  ext
  simp [Matrix.fromColumns, Matrix.mulWeig, Matrix.dotProd]

theorem ExtendedLP.weakDuality [DecidableEq I] [DecidableEq J] {P : ExtendedLP I J}
    {p : ℚ∞} (hP : P.Reaches p) {q : ℚ∞} (hQ : P.dualize.Reaches q) :
    0 ≤ p + q := by
  obtain ⟨A, b, c, hai, haj, hbi, hcj, hAb, hAc⟩ := P
  obtain ⟨x, hx, rfl⟩ := hP
  obtain ⟨y, hy, rfl⟩ := hQ
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
              exact Matrix.no_bot_dotProd_nneg (by simpa using hbi) y hby
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
    rw [Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff]
    exact ⟨hx, by rfl⟩
  · use Sum.elim y 1
    constructor
    · rw [Matrix.transpose_fromRows, Matrix.fromColumns_neg]
      suffices : (-Aᵀ) ₘ* y + (-c) ≤ 0
      · rw [Matrix.fromColumns_mulWeig_sumElim]
        convert this -- TODO cleanup
        ext j
        simp [Matrix.mulWeig, Matrix.dotProd]
        apply ERat.one_smul
      rwa [ERat.vec_sub_nonpos_iff]
    · suffices : b ᵥ⬝ y + c ᵥ⬝ x < 0
      · rw [Matrix.sumElim_dotProd_sumElim]
        conv => lhs; right; simp [Matrix.dotProd]
        rwa [ERat.one_smul]
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
    | ⊤ => convert_to False ↔ False <;> simp [←ERat.coe_neg]
    | (p : ℚ) => simp [←ERat.coe_neg, ←ERat.coe_add]

lemma ERat.smul_lt_smul_left {x : ℚ≥0} (hx : 0 < x) (y z : ℚ∞) :
    x • y < x • z ↔ y < z := by
  match z with
  | ⊥ =>
    convert_to False ↔ False
    · rw [iff_false]
      apply not_lt_bot
    · simp
    rfl
  | ⊤ =>
    match y with
    | ⊥ =>
      convert_to True ↔ True
      · rw [pos_smul_ERat_top hx, iff_true]
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
      · rw [pos_smul_ERat_top hx, iff_true]
        apply coe_lt_top
      · simp
      rfl
  | (q : ℚ) =>
    match y with
    | ⊥ =>
      convert_to True ↔ True
      · rw [iff_true]
        apply bot_lt_coe
      · simp
      rfl
    | ⊤ =>
      convert_to False ↔ False
      · rw [pos_smul_ERat_top hx, iff_false]
        apply not_top_lt
      · simp
      rfl
    | (p : ℚ) =>
      rw [ERat.coe_lt_coe_iff]
      show (x * p).toERat < (x * q).toERat ↔ p < q
      rw [ERat.coe_lt_coe_iff]
      exact mul_lt_mul_left hx

lemma ERat.smul_neg {x : ℚ≥0} {y : ℚ∞} (hxy : x = 0 → y ≠ ⊥ ∧ y ≠ ⊤) :
    x • (-y) = -(x • y) := by
  match y with
  | ⊥ =>
    rw [neg_bot]
    if hx : 0 < x then
      rewrite [pos_smul_ERat_top hx]
      rfl
    else
      exfalso
      simp_all
  | ⊤ =>
    rw [neg_top]
    if hx : 0 < x then
      rewrite [pos_smul_ERat_top hx, neg_top]
      rfl
    else
      exfalso
      simp_all
  | (q : ℚ) =>
    rw [←ERat.coe_neg]
    show (x * (-q)).toERat = (-(x * q)).toERat
    rw [mul_neg]

lemma ERat.pos_smul_neg {x : ℚ≥0} (hx : 0 < x) (y : ℚ∞) :
    x • (-y) = -(x • y) := by
  apply ERat.smul_neg
  intro h0
  exfalso
  exact (h0 ▸ hx).false

lemma ERat.pos_smul_neg_vec {x : ℚ≥0} (hx : 0 < x) (y : I → ℚ∞) :
    x • (-y) = -(x • y) := by
  ext i
  exact ERat.pos_smul_neg hx (y i)

lemma ERat.vec_zero_smul {v : I → ℚ∞} (hv : ∀ i, v i ≠ ⊥) : (0 : ℚ≥0) • v = 0 := by
  ext i
  exact zero_smul_ERat_nonbot (hv i)

lemma Matrix.zero_mulWeig (v : J → ℚ≥0) : (0 : Matrix I J ℚ∞) ₘ* v = 0 := by
  ext
  simp [Matrix.mulWeig, Matrix.dotProd]

lemma Matrix.sumElim_dotProd (u : I → ℚ∞) (v : J → ℚ∞) (x : (I ⊕ J) → ℚ≥0) :
    Sum.elim u v ᵥ⬝ x = u ᵥ⬝ (x ∘ Sum.inl) + v ᵥ⬝ (x ∘ Sum.inr) := by
  simp [Matrix.dotProd]

lemma ERat.smul_smul {p : ℚ≥0} (hp : 0 < p) (r : ℚ≥0) (x : ℚ∞) :
    r • (p • x) = p • (r • x) := by
  match x with
  | ⊥ =>
    rw [smul_ERat_bot, smul_ERat_bot, smul_ERat_bot]
  | ⊤ =>
    rw [pos_smul_ERat_top hp]
    if hr : 0 < r then
      rw [pos_smul_ERat_top hr, pos_smul_ERat_top hp]
    else if hr0 : r = 0 then
      rw [hr0]
      symm
      apply smul_zero
    else
      exfalso
      simp_all only [not_lt, nonpos_iff_eq_zero]
  | (q : ℚ) =>
    exact ERat.coe_eq_coe_iff.mpr (mul_left_comm r.val p.val q)

lemma ERat.smul_add {k : ℚ≥0} (hk : 0 < k) (x y : ℚ∞) :
    k • (x + y) = k • x + k • y := by
  match x, y with
  | ⊥, _ =>
    rw [ERat.bot_add, smul_ERat_bot, ERat.bot_add]
  | _, ⊥ =>
    rw [ERat.add_bot, smul_ERat_bot, ERat.add_bot]
  | (p : ℚ), (q : ℚ) =>
    show (k * (p + q)).toERat = (k * p).toERat + (k * q).toERat
    rewrite [mul_add]
    rfl
  | (p : ℚ), ⊤ =>
    rw [ERat.coe_add_top, pos_smul_ERat_top hk]
    show ⊤ = (k * p).toERat + ⊤
    rw [ERat.coe_add_top]
  | ⊤, (q : ℚ) =>
    rw [ERat.top_add_coe, pos_smul_ERat_top hk]
    show ⊤ = ⊤ + (k * q).toERat
    rw [ERat.top_add_coe]
  | ⊤, ⊤ =>
    rw [ERat.top_add_top, pos_smul_ERat_top hk, ERat.top_add_top]

lemma Multiset.smul_ERat_sum {k : ℚ≥0} (hk : 0 < k) (s : Multiset ℚ∞) :
    s.summap (k • ·) = k • s.sum := by
  induction s using Multiset.induction with
  | empty => simp [Multiset.summap]
  | cons a m ih => simp [Multiset.summap, ERat.smul_add hk, ←ih]

lemma Finset.smul_ERat_sum {k : ℚ≥0} (hk : 0 < k) (v : J → ℚ∞) :
    ∑ j : J, k • v j = k • ∑ j : J, v j := by
  convert Multiset.smul_ERat_sum hk (Finset.univ.val.map v)
  simp [Multiset.summap]

lemma Matrix.ERat_smul_dotProd {k : ℚ≥0} (hk : 0 < k) (v : J → ℚ∞) (w : J → ℚ≥0) :
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

lemma Matrix.no_top_dotProd_nneg {v : I → ℚ∞} (hv : ∀ i, v i ≠ ⊤) (w : I → ℚ≥0) :
    v ᵥ⬝ w ≠ (⊤ : ℚ∞) := by
  apply Multiset.sum_neq_ERat_top
  rw [Multiset.mem_map]
  intro ⟨i, _, hi⟩
  match hvi : v i with
  | ⊥ => exact bot_ne_top (hvi ▸ hi)
  | ⊤ => exact false_of_ne (hvi ▸ hv i)
  | (q : ℚ) => exact ERat.coe_neq_top _ (hvi ▸ hi)


lemma ExtendedLP.strongDuality_aux [DecidableEq I] [DecidableEq J] {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ p q : ℚ, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 := by
  obtain ⟨A, b, c, hai, haj, hbi, hcj, hAb, hAc⟩ := P
  dsimp only [ExtendedLP.dualize, ExtendedLP.Reaches, ExtendedLP.IsSolution, ExtendedLP.IsFeasible] at *
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
    obtain ⟨x, hx⟩ := case_x
    rw [
      Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
      ←Sum.elim_comp_inl_inr x, Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add
    ] at hx
    set y := x ∘ Sum.inr
    set x := x ∘ Sum.inl
    sorry
  | inr case_y =>
    obtain ⟨y, hAy, hbcy⟩ := case_y
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
      · sorry
      clear contr
      sorry
    sorry

theorem ExtendedLP.strongDuality [DecidableEq I] [DecidableEq J] {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : ℚ, P.Reaches (-r).toERat ∧ P.dualize.Reaches r.toERat := by
  obtain ⟨p, q, hp, hq, hpq⟩ := P.strongDuality_aux hP hQ
  have := P.weakDuality hp hq
  rw [←ERat.coe_add, ←ERat.coe_zero, ERat.coe_le_coe_iff] at this
  use q
  have hqp : -q = p
  · linarith
  rw [hqp]
  exact ⟨hp, hq⟩
