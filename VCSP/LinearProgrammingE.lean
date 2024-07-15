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

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. Note that `⊤` can be reached but `⊥` cannot. -/
def ExtendedLP.Reaches (P : ExtendedLP I J) (r : ℚ∞) : Prop :=
  ∃ x : J → ℚ≥0, P.IsSolution x ∧ P.c ᵥ⬝ x = r

/-- Linear program `P` is feasible iff `P` reaches a finite objective value. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ p : ℚ, P.Reaches p.toERat

/-- Linear program `P` is unbounded iff TODO. -/
def ExtendedLP.IsUnbounded (P : ExtendedLP I J) : Prop :=
  ∀ r : ℚ, ∃ p : ℚ∞, p ≤ r ∧ P.Reaches p

/-- Dualize a linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function. -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨-P.Aᵀ, P.c, P.b, by aeply P.hAj, by aeply P.hAi, P.hcj, P.hbi, by aeply P.hAc, by aeply P.hAb⟩

lemma ExtendedLP.dualize_dualize (P : ExtendedLP I J) : P.dualize.dualize = P := by
  obtain ⟨_, _, _⟩ := P
  simp [ExtendedLP.dualize, ←Matrix.ext_iff]


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

lemma ERat.one_smul_vec (v : J → ℚ∞) : (1 : ℚ≥0) • v = v := by
  ext
  apply ERat.one_smul

lemma Matrix.fromColumns_mulWeig_sumElim {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (A₁ : Matrix I J₁ ℚ∞) (A₂ : Matrix I J₂ ℚ∞) (v₁ : J₁ → ℚ≥0) (v₂ : J₂ → ℚ≥0) :
    Matrix.fromColumns A₁ A₂ ₘ* Sum.elim v₁ v₂ = A₁ ₘ* v₁ + A₂ ₘ* v₂ := by
  ext
  simp [Matrix.fromColumns, Matrix.mulWeig, Matrix.dotProd]

theorem ExtendedLP.weakDuality [DecidableEq I] [DecidableEq J] {P : ExtendedLP I J}
    {p : ℚ∞} (hP : P.Reaches p) {q : ℚ∞} (hQ : P.dualize.Reaches q) :
    0 ≤ p + q := by
  obtain ⟨A, b, c, hAi, hAj, hbi, hcj, hAb, hAc⟩ := P
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
          | inl i' => exact hAi ⟨i', ⟨s, his⟩, ⟨t, hit⟩⟩
          | inr => exact hcj ⟨s, his⟩
        )
        (by
          intro ⟨j, ⟨s, hjs⟩, ⟨t, hjt⟩⟩
          cases s with
          | inl iₛ =>
            cases t with
            | inl iₜ => exact hAj ⟨j, ⟨iₛ, hjs⟩, ⟨iₜ, hjt⟩⟩
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


lemma ERat.smul_nonpos {x : ℚ∞} (hx : x ≤ 0) (c : ℚ≥0) :
    c • x ≤ 0 := by
  match x with
  | ⊥ => apply bot_le
  | ⊤ => simp at hx
  | (q : ℚ) => exact ERat.coe_le_coe_iff.mpr (mul_nonpos_of_nonneg_of_nonpos c.property (coe_nonpos.mp hx))

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

lemma ERat.smul_le_smul_left {x : ℚ≥0} (hx : 0 < x) (y z : ℚ∞) :
    x • y ≤ x • z ↔ y ≤ z := by
  convert neg_iff_neg (ERat.smul_lt_smul_left hx z y) <;> exact Iff.symm not_lt

lemma ERat.vec_smul_le_smul_left {k : ℚ≥0} (hk : 0 < k) (x y : I → ℚ∞) :
    k • x ≤ k • y ↔ x ≤ y := by
  constructor <;> intro hxy <;> intro i <;> specialize hxy i
  · exact (ERat.smul_le_smul_left hk _ _).mp hxy
  · exact (ERat.smul_le_smul_left hk _ _).mpr hxy

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

lemma ERat.smul_add_vec {k : ℚ≥0} (hk : 0 < k) (v w : J → ℚ∞) :
    k • (v + w) = k • v + k • w := by
  ext
  apply ERat.smul_add hk

lemma ERat.add_smul (c d : ℚ≥0) (x : ℚ∞) :
    (c + d) • x = c • x + d • x := by
  match x with
  | ⊥ =>
    rewrite [smul_ERat_bot, smul_ERat_bot, smul_ERat_bot]
    rfl
  | ⊤ =>
    if c_eq_0 : c = 0 then
      rw [c_eq_0, zero_smul_ERat_nonbot top_ne_bot, zero_add, zero_add]
    else
      have c_pos : 0 < c -- TODO lemma
      · apply lt_of_le_of_ne c.property
        intro contr
        exact c_eq_0 (by simpa using contr.symm)
      rw [pos_smul_ERat_top (add_pos_of_pos_of_nonneg c_pos d.property)]
      rw [pos_smul_ERat_top c_pos]
      if d_eq_0 : d = 0 then
        rewrite [d_eq_0]
        rfl
      else
        have d_pos : 0 < d
        · apply lt_of_le_of_ne d.property
          intro contr
          exact d_eq_0 (by simpa using contr.symm)
        rewrite [pos_smul_ERat_top d_pos]
        rfl
  | (q : ℚ) =>
    show ((c + d) * q).toERat = (c * q).toERat + (d * q).toERat
    rw [←ERat.coe_add, add_mul]

lemma ERat.mul_smul (c d : ℚ≥0) (x : ℚ∞) :
    (c * d) • x = c • (d • x) := by
  match x with
  | ⊥ =>
    iterate 3 rw [smul_ERat_bot]
  | ⊤ =>
    if d_eq_0 : d = 0 then
      rw [d_eq_0, zero_smul_ERat_nonbot top_ne_bot, mul_zero, zero_smul_ERat_nonbot top_ne_bot, smul_zero]
    else
      have d_pos : 0 < d
      · apply lt_of_le_of_ne d.property
        intro contr
        exact d_eq_0 (by simpa using contr.symm)
      rw [pos_smul_ERat_top d_pos]
      if c_eq_0 : c = 0 then
        rw [c_eq_0, zero_smul_ERat_nonbot top_ne_bot, zero_mul, zero_smul_ERat_nonbot top_ne_bot]
      else
        have c_pos : 0 < c
        · apply lt_of_le_of_ne c.property
          intro contr
          exact c_eq_0 (by simpa using contr.symm)
        rw [pos_smul_ERat_top c_pos, pos_smul_ERat_top (mul_pos c_pos d_pos)]
  | (q : ℚ) =>
    show ((c * d) * q).toERat = (c * (d * q)).toERat
    rw [mul_assoc]

lemma ERat.mul_smul_vec (c d : ℚ≥0) (x : J → ℚ∞) :
    (c * d) • x = c • (d • x) := by
  ext
  apply ERat.mul_smul

lemma Matrix.dotProd_add (x : J → ℚ∞) (v w : J → ℚ≥0) :
    x ᵥ⬝ (v + w) = x ᵥ⬝ v + x ᵥ⬝ w := by
  simp [Matrix.dotProd, ERat.add_smul, Finset.sum_add_distrib]

lemma Matrix.mulWeig_add (M : Matrix I J ℚ∞) (v w : J → ℚ≥0) :
    M ₘ* (v + w) = M ₘ* v + M ₘ* w := by
  ext
  apply Matrix.dotProd_add

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

lemma Matrix.dotProd_smul {k : ℚ≥0} (hk : 0 < k) (x : J → ℚ∞) (v : J → ℚ≥0) :
    x ᵥ⬝ (k • v) = k • (x ᵥ⬝ v) := by
  show ∑ j : J, (k * v j) • x j = k • ∑ j : J, v j • x j
  rw [←Finset.smul_ERat_sum hk]
  apply congr_arg
  ext
  apply ERat.mul_smul

lemma Matrix.mulWeig_smul {k : ℚ≥0} (hk : 0 < k) (M : Matrix I J ℚ∞) (v : J → ℚ≥0) :
    M ₘ* (k • v) = k • (M ₘ* v) := by
  ext
  apply Matrix.dotProd_smul hk

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
        rw [hwi0, zero_smul_ERat_nonbot top_ne_bot, zero_smul_toERat]
      else
        rw [pos_smul_ERat_top (lt_of_le_of_ne (w i).property (Ne.symm hwi0))]
        apply le_top
    | (q : ℚ) =>
      have hpq : p ≤ q
      · rw [←ERat.coe_le_coe_iff]
        rwa [hui, hvi] at huvi
      exact ERat.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hpq (w i).property)


variable [DecidableEq I] [DecidableEq J]

lemma ExtendedLP.infeasible_of_unbounded {P : ExtendedLP I J} (hP : P.IsUnbounded) :
    ¬ P.dualize.IsFeasible := by
  intro ⟨q, hq⟩
  obtain ⟨p, hpq, hp⟩ := hP (-(q+1))
  have weak_duality := P.weakDuality hp hq
  match p with
  | ⊥ => simp at weak_duality
  | ⊤ => exact (hpq.trans_lt (ERat.coe_lt_top _)).false
  | (p' : ℚ) =>
    rw [←ERat.coe_add, ←ERat.coe_zero] at weak_duality
    rw [ERat.coe_le_coe_iff] at weak_duality hpq
    linarith

lemma ExtendedLP.unbounded_of_feasible_of_neg {P : ExtendedLP I J} (hP : P.IsFeasible)
    {x₀ : J → ℚ≥0} (hx₀ : P.c ᵥ⬝ x₀ < 0) (hAx₀ : P.A ₘ* x₀ + (0 : ℚ≥0) • (-P.b) ≤ 0) :
    P.IsUnbounded := by
  obtain ⟨e, xₚ, hxₚ, he⟩ := hP
  intro s
  if hs : e ≤ s then
    exact ⟨e, by simpa using hs, xₚ, hxₚ, he⟩
  else
    push_neg at hs
    match hcx₀ : P.c ᵥ⬝ x₀ with
    | ⊥ =>
      exfalso
      apply P.hcj
      exact Matrix.dotProd_eq_bot hcx₀
    | ⊤ =>
      exfalso
      rw [hcx₀] at hx₀
      exact (hx₀.trans_le le_top).false
    | (d : ℚ) =>
      rw [hcx₀] at hx₀
      have coef_pos : 0 < (s - e) / d -- TODO cleanup
      · apply div_pos_of_neg_of_neg
        · rwa [sub_neg]
        · rwa [←ERat.coe_neg']
      let k : ℚ≥0 := ⟨((s - e) / d), coef_pos.le⟩
      have k_pos : 0 < k
      · exact coef_pos
      refine ⟨s, by rfl, xₚ + k • x₀, ?_, ?_⟩
      · intro i
        match hi : P.b i with
        | ⊥ =>
          exfalso
          exact P.hbi ⟨i, hi⟩
        | ⊤ =>
          apply le_top
        | (bᵢ : ℚ) =>
          specialize hAx₀ i
          rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hi] at hAx₀
          have zeros : (P.A ₘ* x₀) i + (0 : ℚ∞) ≤ 0
          · convert hAx₀
            show 0 = 0 • -(bᵢ.toERat)
            rw [←ERat.coe_neg, zero_smul_toERat]
          rw [add_zero] at zeros
          rw [Matrix.mulWeig_add, Matrix.mulWeig_smul k_pos, Pi.add_apply]
          apply add_le_of_le_of_nonpos
          · convert_to (P.A ₘ* xₚ) i ≤ P.b i
            · exact hi.symm
            exact hxₚ i
          · exact ERat.smul_nonpos zeros k
      · rw [Matrix.dotProd_add, he, Matrix.dotProd_smul k_pos, hcx₀]
        show (e + ((s - e) / d) * d).toERat = s.toERat
        rw [ERat.coe_eq_coe_iff, div_mul_cancel_of_imp]
        exact add_sub_cancel e s
        intro hd
        exfalso
        rw [hd] at hx₀
        exact hx₀.false

lemma ExtendedLP.strongDuality_aux {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ p q : ℚ, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 := by
  cases
    or_of_neq
      (extendedFarkas
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.ro1 (Sum.elim P.c P.b)))
        (Sum.elim (Sum.elim P.b P.c) 0)
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ =>
                cases t with
                | inl jₜ => exact P.hAi ⟨i, ⟨⟨jₛ, by simpa using hks⟩, ⟨jₜ, by simpa using hkt⟩⟩⟩
                | inr iₜ => simp at hkt
              | inr iₛ => simp at hks
            | inr j =>
              cases t with
              | inl jₜ => simp at hkt
              | inr iₜ =>
                cases s with
                | inl jₛ => simp at hks
                | inr iₛ => exact P.hAj ⟨j, ⟨iₜ, by simpa using hkt⟩, ⟨iₛ, by simpa using hks⟩⟩
          | inr =>
            cases s with
            | inl jₛ => exact P.hcj ⟨jₛ, hks⟩
            | inr iₛ => exact P.hbi ⟨iₛ, hks⟩
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
                | inr => exact P.hAc ⟨j, ⟨iₛ, hks⟩, hkt⟩
              | inr jₛ => simp at hks
            | inr => exact P.hcj ⟨j, hks⟩
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
                  | inr jₜ => exact P.hAi ⟨i, ⟨jₜ, by simpa using hkt⟩, ⟨jₛ, by simpa using hks⟩⟩
                | inr => exact P.hAb ⟨i, ⟨jₛ, by simpa using hks⟩, hkt⟩
            | inr => exact P.hbi ⟨i, hks⟩
        )
        (by
          intro ⟨k, ⟨t, hkt⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases t with
              | inl jₜ => exact P.hAb ⟨i, ⟨jₜ, hkt⟩, hk⟩
              | inr iₜ => simp at hkt
            | inr j =>
              cases t with
              | inl jₜ => simp at hkt
              | inr iₜ => exact P.hAc ⟨j, ⟨iₜ, by simpa using hkt⟩, hk⟩
          | inr => simp at hk
        )
        (by
          intro ⟨k, ⟨s, hks⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ => exact P.hbi ⟨i, hk⟩
              | inr iₛ => simp at hks
            | inr j =>
              cases s with
              | inl jₛ => simp at hks
              | inr iₛ => exact P.hcj ⟨j, hk⟩
          | inr => simp at hk
        )
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
    obtain ⟨⟨hx, hy⟩, hxy⟩ := hx
    specialize hxy 0
    change hxy to Sum.elim P.c P.b ᵥ⬝ Sum.elim x y ≤ 0
    rw [Matrix.sumElim_dotProd_sumElim] at hxy
    match hcx : P.c ᵥ⬝ x with
    | ⊥ =>
      exfalso
      apply P.hcj
      exact Matrix.dotProd_eq_bot hcx
    | ⊤ =>
      exfalso
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        apply P.hbi
        exact Matrix.dotProd_eq_bot hby
      | ⊤ =>
        rw [hcx, hby] at hxy
        exact (hxy.trans_lt ERat.zero_lt_top).false
      | (q : ℚ) =>
        rw [hcx, hby] at hxy
        exact (hxy.trans_lt ERat.zero_lt_top).false
    | (p : ℚ) =>
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        exfalso
        apply P.hbi
        exact Matrix.dotProd_eq_bot hby
      | ⊤ =>
        exfalso
        rw [hcx, hby] at hxy
        exact (hxy.trans_lt ERat.zero_lt_top).false
      | (q : ℚ) =>
        refine ⟨p, q, ⟨x, hx, hcx⟩, ⟨y, hy, hby⟩, ?_⟩
        rw [←ERat.coe_le_coe_iff]
        rwa [hcx, hby] at hxy
  | inr case_y =>
    obtain ⟨y, hAy, hbc⟩ := case_y
    rw [
      Matrix.transpose_fromRows, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero,
      Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.transpose_row, Matrix.fromColumns_neg,
      ←Sum.elim_comp_inl_inr y, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.fromBlocks_neg, Matrix.ERat_neg_neg, Matrix.ERat_neg_zero, Matrix.ERat_neg_zero,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig,
      ←Sum.elim_comp_inl_inr (y ∘ Sum.inl), Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add,
    ] at hAy
    rw [←Sum.elim_comp_inl_inr y, ←Sum.elim_comp_inl_inr (y ∘ Sum.inl)] at hbc
    set z := y ∘ Sum.inr
    set x := (y ∘ Sum.inl) ∘ Sum.inr
    set y := (y ∘ Sum.inl) ∘ Sum.inl
    have hAyx : Sum.elim (-P.Aᵀ ₘ* y) (P.A ₘ* x) + z 0 • (-Sum.elim P.c P.b) ≤ 0
    · convert hAy
      ext
      simp [Matrix.col, Matrix.mulWeig, Matrix.dotProd]
    set z := z 0
    have hAyx' : Sum.elim (-P.Aᵀ ₘ* y) (P.A ₘ* x) + Sum.elim (z • (-P.c)) (z • (-P.b)) ≤ 0
    · convert hAyx
      aesop
    rw [←Sum.elim_add_add, Sum.elim_nonpos_iff] at hAyx'
    obtain ⟨hy, hx⟩ := hAyx'
    clear hAy hAyx
    rw [Matrix.sumElim_dotProd_sumElim, Matrix.zero_dotProd, add_zero, Matrix.sumElim_dotProd_sumElim] at hbc
    have z_pos : 0 < z
    · by_contra contr
      have z_eq_0 : z = 0
      · push_neg at contr
        exact nonpos_iff_eq_zero.mp contr
      rw [z_eq_0] at hx hy
      clear contr z_eq_0 z
      if hxc : P.c ᵥ⬝ x < 0 then
        exact P.infeasible_of_unbounded (P.unbounded_of_feasible_of_neg hP hxc hx) hQ
      else
        have hyb : P.b ᵥ⬝ y < 0
        · push_neg at hxc
          by_contra! contr
          exact (hbc.trans_le (add_nonneg contr hxc)).false
        exact P.dualize.infeasible_of_unbounded (P.dualize.unbounded_of_feasible_of_neg hQ hyb hy) (P.dualize_dualize.symm ▸ hP)
    match hcx : P.c ᵥ⬝ x with
    | ⊥ =>
      exfalso
      apply P.hcj
      exact Matrix.dotProd_eq_bot hcx
    | ⊤ =>
      exfalso
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        apply P.hbi
        exact Matrix.dotProd_eq_bot hby
      | ⊤ =>
        rw [hcx, hby] at hbc
        exact (hbc.trans ERat.zero_lt_top).false
      | (q : ℚ) =>
        rw [hcx, hby] at hbc
        exact (hbc.trans ERat.zero_lt_top).false
    | (p : ℚ) =>
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        exfalso
        apply P.hbi
        exact Matrix.dotProd_eq_bot hby
      | ⊤ =>
        exfalso
        rw [hcx, hby] at hbc
        exact (hbc.trans ERat.zero_lt_top).false
      | (q : ℚ) =>
        have z_inv_pos : 0 < z⁻¹
        · exact inv_pos_of_pos z_pos
        refine ⟨z⁻¹ • p, z⁻¹ • q, ⟨z⁻¹ • x, ?_, ?_⟩, ⟨z⁻¹ • y, ?_, ?_⟩, ?_⟩
        · rwa [
            ←ERat.vec_smul_le_smul_left z_inv_pos, smul_zero,
            ERat.smul_add_vec z_inv_pos, ←Matrix.mulWeig_smul z_inv_pos, ←ERat.mul_smul_vec,
            inv_mul_cancel (ne_of_lt z_pos).symm, ERat.one_smul_vec, ERat.vec_sub_nonpos_iff
          ] at hx
        · rewrite [Matrix.dotProd_smul z_inv_pos, hcx]
          rfl
        · rwa [
            ←ERat.vec_smul_le_smul_left z_inv_pos, smul_zero,
            ERat.smul_add_vec z_inv_pos, ←Matrix.mulWeig_smul z_inv_pos, ←ERat.mul_smul_vec,
            inv_mul_cancel (ne_of_lt z_pos).symm, ERat.one_smul_vec, ERat.vec_sub_nonpos_iff
          ] at hy
        · dsimp only [ExtendedLP.dualize]
          rewrite [Matrix.dotProd_smul z_inv_pos, hby]
          rfl
        rw [hcx, hby] at hbc
        show z⁻¹ * p + z⁻¹ * q ≤ 0
        rw [←mul_add]
        have hpq : p + q < 0
        · rw [←ERat.coe_lt_coe_iff, add_comm]
          exact hbc
        exact Linarith.mul_nonpos hpq.le z_inv_pos

theorem ExtendedLP.strongDuality {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : ℚ, P.Reaches (-r).toERat ∧ P.dualize.Reaches r.toERat := by
  obtain ⟨p, q, hp, hq, hpq⟩ := P.strongDuality_aux hP hQ
  have := P.weakDuality hp hq -- TODO cleanup
  rw [←ERat.coe_add, ←ERat.coe_zero, ERat.coe_le_coe_iff] at this
  use q
  have hqp : -q = p
  · linarith
  rw [hqp]
  exact ⟨hp, hq⟩

#print axioms ExtendedLP.strongDuality

lemma ExtendedLP.unbounded_of_feasible_of_infeasible {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : ¬P.dualize.IsFeasible) :
    P.IsUnbounded := by
  cases
    or_of_neq
      (extendedFarkas (-P.Aᵀ) P.c (by aeply P.hAj) (by aeply P.hAi) (by aeply P.hAc) (by aeply P.hcj)) with
  | inl caseI =>
    exfalso
    obtain ⟨y, hy⟩ := caseI
    match hby : P.b ᵥ⬝ y with
    | ⊥ => exact Matrix.no_bot_dotProd_nneg (by simpa using P.hbi) y hby
    | ⊤ =>
      have unbound : P.dualize.IsUnbounded
      · intro r
        use ⊥
        constructor
        · exact bot_le
        use y
        exact ⟨hy, sorry⟩
      exact ExtendedLP.infeasible_of_unbounded unbound (P.dualize_dualize.symm ▸ hP)
    | (q : ℚ) => exact hQ ⟨q, y, hy, hby⟩
  | inr caseJ =>
    obtain ⟨x, hAx, hcx⟩ := caseJ
    apply ExtendedLP.unbounded_of_feasible_of_neg hP hcx
    rw [Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.ERat_neg_neg] at hAx
    intro i
    match hbi : P.b i with
    | ⊥ =>
      exfalso
      exact P.hbi ⟨i, hbi⟩
    | ⊤ =>
      change hbi to P.b i = ⊤
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi, ERat.neg_top, smul_ERat_bot, ERat.add_bot]
      apply bot_le
    | (q : ℚ) =>
      change hbi to P.b i = q.toERat
      have hq : -q.toERat ≠ (⊥ : ℚ∞)
      · rw [←ERat.coe_neg]
        apply ERat.coe_neq_bot
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi, zero_smul_ERat_nonbot hq, add_zero]
      exact hAx i
