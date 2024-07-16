import VCSP.FarkasSpecial


/-- Linear program over `ℚ∞` in the standard form (system of linear inequalities with `ℚ≥0` variables).
    Variables are of type `J`. Conditions are indexed by type `I`.
    Its objective function is intended to be minimized. -/
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


section extended_LP_definitions

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

/-- Linear program `P` is feasible iff `P` reaches a finite value. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ p : ℚ, P.Reaches p.toERat

/-- Linear program `P` is bounded by `r` iff every value reached by `P` is
    greater or equal to `r` (i.e., `P` is bounded from below). -/
def ExtendedLP.IsBoundedBy (P : ExtendedLP I J) (r : ℚ) : Prop :=
  ∀ p : ℚ∞, P.Reaches p → r ≤ p

/-- Linear program `P` is unbounded iff values reached by `P` have no finite lower bound. -/
def ExtendedLP.IsUnbounded (P : ExtendedLP I J) : Prop :=
  ¬∃ r : ℚ, P.IsBoundedBy r

/-- Dualize a linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function. -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨-P.Aᵀ, P.c, P.b, by aeply P.hAj, by aeply P.hAi, P.hcj, P.hbi, by aeply P.hAc, by aeply P.hAb⟩

open scoped Classical in
/-- Extended notion of "optimum" of "minimization LP". -/
noncomputable def ExtendedLP.optimum (P : ExtendedLP I J) : Option ℚ∞ :=
  if P.IsFeasible then
    if P.IsUnbounded then
      some ⊥ -- unbounded means that the minimum is `⊥`
    else
      if hr : ∃ r : ℚ, P.Reaches r.toERat ∧ P.IsBoundedBy r then
        some hr.choose.toERat -- the minimum is finite
      else
        none -- invalid finite value (infimum is not attained; later, we prove it cannot happen)
  else
    some ⊤ -- infeasible means that the minimum is `⊤`

end extended_LP_definitions


section weak_duality

lemma ERat.one_smul (r : ℚ∞) : (1 : ℚ≥0) • r = r :=
  match r with
  | ⊥ => rfl
  | ⊤ => rfl
  | (q : ℚ) => congr_arg Rat.toERat (one_mul q)

lemma ERat.sub_nonpos_iff (r s : ℚ∞) : r + (-s) ≤ 0 ↔ r ≤ s := by
  match r with
  | ⊥ => convert_to True ↔ True <;> simp
  | ⊤ => match s with
    | ⊥ => decide
    | ⊤ => decide
    | (_ : ℚ) => convert_to False ↔ False <;> simp [←ERat.coe_neg]
  | (_ : ℚ) => match s with
    | ⊥ => convert_to False ↔ False <;> simp
    | ⊤ => convert_to True ↔ True <;> simp
    | (_ : ℚ) => simp [←ERat.coe_neg, ←ERat.coe_add]

lemma ERat.vec_sub_nonpos_iff (u v : I → ℚ∞) : u + (-v) ≤ 0 ↔ u ≤ v := by
  constructor <;> intro huv i <;> simpa [ERat.sub_nonpos_iff] using huv i

lemma Matrix.sumElim_dotProd_sumElim (u : I → ℚ∞) (v : J → ℚ∞) (x : I → ℚ≥0) (y : J → ℚ≥0) :
    Sum.elim u v ᵥ⬝ Sum.elim x y = u ᵥ⬝ x + v ᵥ⬝ y := by
  simp [Matrix.dotProd]

lemma Matrix.fromRows_mulWeig {I₁ I₂ : Type*} (M₁ : Matrix I₁ J ℚ∞) (M₂ : Matrix I₂ J ℚ∞) (v : J → ℚ≥0) :
    Matrix.fromRows M₁ M₂ ₘ* v = Sum.elim (M₁ ₘ* v) (M₂ ₘ* v) := by
  ext i
  cases i <;> rfl

lemma Matrix.fromColumns_mulWeig_sumElim {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (M₁ : Matrix I J₁ ℚ∞) (M₂ : Matrix I J₂ ℚ∞) (v₁ : J₁ → ℚ≥0) (v₂ : J₂ → ℚ≥0) :
    Matrix.fromColumns M₁ M₂ ₘ* Sum.elim v₁ v₂ = M₁ ₘ* v₁ + M₂ ₘ* v₂ := by
  ext
  simp [Matrix.fromColumns, Matrix.mulWeig, Matrix.dotProd]

theorem ExtendedLP.weakDuality [DecidableEq I] [DecidableEq J] {P : ExtendedLP I J}
    {p : ℚ∞} (hP : P.Reaches p) {q : ℚ∞} (hQ : P.dualize.Reaches q) :
    0 ≤ p + q := by
  obtain ⟨x, hx, rfl⟩ := hP
  obtain ⟨y, hy, rfl⟩ := hQ
  by_contra contr
  apply
    not_and_of_neq
      (extendedFarkas
        (Matrix.fromRows P.A (Matrix.ro1 P.c))
        (Sum.elim P.b (fun _ => P.c ᵥ⬝ x))
        (by
          intro ⟨i, ⟨s, his⟩, ⟨t, hit⟩⟩
          cases i with
          | inl i' => exact P.hAi ⟨i', ⟨s, his⟩, ⟨t, hit⟩⟩
          | inr => exact P.hcj ⟨s, his⟩
        )
        (by
          intro ⟨j, ⟨s, hjs⟩, ⟨t, hjt⟩⟩
          cases s with
          | inl iₛ =>
            cases t with
            | inl iₜ => exact P.hAj ⟨j, ⟨iₛ, hjs⟩, ⟨iₜ, hjt⟩⟩
            | inr => exact P.hAc ⟨j, ⟨iₛ, hjs⟩, hjt⟩
          | inr => exact P.hcj ⟨j, hjs⟩
        )
        (by
          intro ⟨i, ⟨j, hij⟩, hi⟩
          cases i with
          | inl i' => exact P.hAb ⟨i', ⟨j, hij⟩, hi⟩
          | inr =>
            rw [Sum.elim_inr] at hi
            push_neg at contr
            rw [hi] at contr
            match hby : P.b ᵥ⬝ y with
            | ⊥ =>
              exact Matrix.no_bot_dotProd_nneg (by simpa using P.hbi) y hby
            | ⊤ =>
              dsimp only [ExtendedLP.dualize] at contr
              rw [hby] at contr
              change contr to ⊤ + ⊤ < 0
              simp at contr
            | (q : ℚ) =>
              dsimp only [ExtendedLP.dualize] at contr
              rw [hby] at contr
              change contr to ⊤ + q.toERat < 0
              simp at contr
        )
        (by
          intro ⟨i, ⟨j, hij⟩, hi⟩
          cases i with
          | inl i' => exact P.hbi ⟨i', hi⟩
          | inr => exact P.hcj ⟨j, hij⟩
        )
      )
  constructor
  · use x
    rw [Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff]
    exact ⟨hx, by rfl⟩
  · use Sum.elim y 1
    constructor
    · rw [Matrix.transpose_fromRows, Matrix.fromColumns_neg, Matrix.fromColumns_mulWeig_sumElim]
      have hle0 : (-P.Aᵀ) ₘ* y + (-P.c) ≤ 0
      · rwa [ERat.vec_sub_nonpos_iff]
      convert hle0
      ext
      simp [Matrix.mulWeig, Matrix.dotProd, ERat.one_smul]
    · have hlt0 : P.b ᵥ⬝ y + P.c ᵥ⬝ x < 0
      · push_neg at contr
        rwa [add_comm]
      rw [Matrix.sumElim_dotProd_sumElim]
      simp [Matrix.dotProd]
      rwa [ERat.one_smul]

end weak_duality


section strong_duality

lemma NNRat.pos_of_not_zero {k : ℚ≥0} (hk : ¬(k = 0)) :
    0 < k := by
  apply lt_of_le_of_ne k.property
  intro contr
  apply hk
  simpa using contr.symm

section misc_ERat_properties

lemma ERat.smul_nonpos {r : ℚ∞} (hr : r ≤ 0) (k : ℚ≥0) :
    k • r ≤ 0 := by
  match r with
  | ⊥ => apply bot_le
  | ⊤ => simp at hr
  | (_ : ℚ) => exact ERat.coe_le_coe_iff.mpr (mul_nonpos_of_nonneg_of_nonpos k.property (coe_nonpos.mp hr))

lemma ERat.smul_lt_smul_left {k : ℚ≥0} (hk : 0 < k) (r s : ℚ∞) :
    k • r < k • s ↔ r < s := by
  match s with
  | ⊥ =>
    convert_to False ↔ False
    · rw [iff_false]
      apply not_lt_bot
    · simp
    rfl
  | ⊤ =>
    match r with
    | ⊥ =>
      convert_to True ↔ True
      · rw [ERat.pos_smul_top hk, iff_true]
        apply bot_lt_top
      · simp
      rfl
    | ⊤ =>
      convert_to False ↔ False
      · apply lt_self_iff_false
      · apply lt_self_iff_false
      rfl
    | (_ : ℚ) =>
      convert_to True ↔ True
      · rw [ERat.pos_smul_top hk, iff_true]
        apply coe_lt_top
      · simp
      rfl
  | (q : ℚ) =>
    match r with
    | ⊥ =>
      convert_to True ↔ True
      · rw [iff_true]
        apply bot_lt_coe
      · simp
      rfl
    | ⊤ =>
      convert_to False ↔ False
      · rw [ERat.pos_smul_top hk, iff_false]
        apply not_top_lt
      · simp
      rfl
    | (p : ℚ) =>
      rw [ERat.coe_lt_coe_iff]
      show (k * p).toERat < (k * q).toERat ↔ p < q
      rw [ERat.coe_lt_coe_iff]
      exact mul_lt_mul_left hk

lemma ERat.smul_le_smul_left {k : ℚ≥0} (hk : 0 < k) (r s : ℚ∞) :
    k • r ≤ k • s ↔ r ≤ s := by
  convert neg_iff_neg (ERat.smul_lt_smul_left hk s r) <;> exact Iff.symm not_lt

lemma ERat.smul_neg {k : ℚ≥0} {r : ℚ∞} (hkr : k = 0 → r ≠ ⊥ ∧ r ≠ ⊤) :
    k • (-r) = -(k • r) := by
  match r with
  | ⊥ =>
    rw [neg_bot]
    if hk : 0 < k then
      rewrite [ERat.pos_smul_top hk]
      rfl
    else
      exfalso
      simp_all
  | ⊤ =>
    rw [neg_top]
    if hk : 0 < k then
      rewrite [ERat.pos_smul_top hk, neg_top]
      rfl
    else
      exfalso
      simp_all
  | (q : ℚ) =>
    rw [←ERat.coe_neg]
    show (k * (-q)).toERat = (-(k * q)).toERat
    rw [mul_neg]

lemma ERat.pos_smul_neg {k : ℚ≥0} (hk : 0 < k) (r : ℚ∞) :
    k • (-r) = -(k • r) := by
  apply ERat.smul_neg
  intro h0
  exfalso
  exact (h0 ▸ hk).false

lemma ERat.smul_smul {k : ℚ≥0} (hk : 0 < k) (l : ℚ≥0) (r : ℚ∞) :
    l • (k • r) = k • (l • r) := by
  match r with
  | ⊥ =>
    rw [ERat.smul_bot, ERat.smul_bot, ERat.smul_bot]
  | ⊤ =>
    rw [ERat.pos_smul_top hk]
    if hl : 0 < l then
      rw [ERat.pos_smul_top hl, ERat.pos_smul_top hk]
    else if hl0 : l = 0 then
      rw [hl0]
      symm
      apply smul_zero
    else
      exfalso
      simp_all only [not_lt, nonpos_iff_eq_zero]
  | (q : ℚ) =>
    exact ERat.coe_eq_coe_iff.mpr (mul_left_comm l.val k.val q)

lemma ERat.add_smul (k l : ℚ≥0) (r : ℚ∞) :
    (k + l) • r = k • r + l • r := by
  match r with
  | ⊥ =>
    rewrite [ERat.smul_bot, ERat.smul_bot, ERat.smul_bot]
    rfl
  | ⊤ =>
    if k_eq_0 : k = 0 then
      rw [k_eq_0, ERat.zero_smul_nonbot top_ne_bot, zero_add, zero_add]
    else
      have k_pos : 0 < k
      · exact NNRat.pos_of_not_zero k_eq_0
      rw [ERat.pos_smul_top (add_pos_of_pos_of_nonneg k_pos l.property)]
      rw [ERat.pos_smul_top k_pos]
      if l_eq_0 : l = 0 then
        rewrite [l_eq_0]
        rfl
      else
        rewrite [ERat.pos_smul_top (NNRat.pos_of_not_zero l_eq_0)]
        rfl
  | (q : ℚ) =>
    show ((k + l) * q).toERat = (k * q).toERat + (l * q).toERat
    rw [←ERat.coe_add, add_mul]

lemma ERat.smul_add {k : ℚ≥0} (hk : 0 < k) (r s : ℚ∞) :
    k • (r + s) = k • r + k • s := by
  match r, s with
  | ⊥, _ =>
    rw [ERat.bot_add, ERat.smul_bot, ERat.bot_add]
  | _, ⊥ =>
    rw [ERat.add_bot, ERat.smul_bot, ERat.add_bot]
  | (p : ℚ), (q : ℚ) =>
    show (k * (p + q)).toERat = (k * p).toERat + (k * q).toERat
    rewrite [mul_add]
    rfl
  | (p : ℚ), ⊤ =>
    rw [ERat.coe_add_top, ERat.pos_smul_top hk]
    show ⊤ = (k * p).toERat + ⊤
    rw [ERat.coe_add_top]
  | ⊤, (q : ℚ) =>
    rw [ERat.top_add_coe, ERat.pos_smul_top hk]
    show ⊤ = ⊤ + (k * q).toERat
    rw [ERat.top_add_coe]
  | ⊤, ⊤ =>
    rw [ERat.top_add_top, ERat.pos_smul_top hk, ERat.top_add_top]

lemma ERat.mul_smul (k l : ℚ≥0) (r : ℚ∞) :
    (k * l) • r = k • (l • r) := by
  match r with
  | ⊥ =>
    iterate 3 rw [ERat.smul_bot]
  | ⊤ =>
    if l_eq_0 : l = 0 then
      rw [l_eq_0, ERat.zero_smul_nonbot top_ne_bot, mul_zero, ERat.zero_smul_nonbot top_ne_bot, smul_zero]
    else
      have l_pos : 0 < l
      · apply lt_of_le_of_ne l.property
        intro contr
        exact l_eq_0 (by simpa using contr.symm)
      rw [ERat.pos_smul_top l_pos]
      if k_eq_0 : k = 0 then
        rw [k_eq_0, ERat.zero_smul_nonbot top_ne_bot, zero_mul, ERat.zero_smul_nonbot top_ne_bot]
      else
        have c_pos : 0 < k
        · exact NNRat.pos_of_not_zero k_eq_0
        rw [ERat.pos_smul_top c_pos, ERat.pos_smul_top (mul_pos c_pos l_pos)]
  | (q : ℚ) =>
    show ((k * l) * q).toERat = (k * (l * q)).toERat
    rw [mul_assoc]

lemma ERat.one_smul_vec (v : J → ℚ∞) :
    (1 : ℚ≥0) • v = v := by
  ext
  apply ERat.one_smul

lemma ERat.smul_add_vec {k : ℚ≥0} (hk : 0 < k) (v w : J → ℚ∞) :
    k • (v + w) = k • v + k • w := by
  ext
  apply ERat.smul_add hk

lemma ERat.mul_smul_vec (k l : ℚ≥0) (v : J → ℚ∞) :
    (k * l) • v = k • (l • v) := by
  ext
  apply ERat.mul_smul

lemma ERat.vec_smul_le_smul_left {k : ℚ≥0} (hk : 0 < k) (u v : I → ℚ∞) :
    k • u ≤ k • v ↔ u ≤ v := by
  constructor <;> intro huv <;> intro i <;> specialize huv i
  · exact (ERat.smul_le_smul_left hk _ _).mp huv
  · exact (ERat.smul_le_smul_left hk _ _).mpr huv

lemma Multiset.sum_neq_ERat_top {s : Multiset ℚ∞} (hs : ⊤ ∉ s) :
    s.sum ≠ ⊤ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.sum_cons]
    match a with
    | ⊥ => simp
    | ⊤ => simp at hs
    | (_ : ℚ) => match hm : m.sum with
      | ⊥ => simp
      | ⊤ => exact (ih (by simpa using hs) hm).elim
      | (_ : ℚ) => simp [←ERat.coe_add]

lemma Multiset.smul_ERat_sum {k : ℚ≥0} (hk : 0 < k) (s : Multiset ℚ∞) :
    s.summap (k • ·) = k • s.sum := by
  induction s using Multiset.induction with
  | empty => simp [Multiset.summap]
  | cons a m ih => simp [Multiset.summap, ERat.smul_add hk, ←ih]

lemma Finset.smul_ERat_sum {k : ℚ≥0} (hk : 0 < k) (v : J → ℚ∞) :
    ∑ j : J, k • v j = k • ∑ j : J, v j := by
  convert Multiset.smul_ERat_sum hk (Finset.univ.val.map v)
  simp [Multiset.summap]

end misc_ERat_properties

section dotProd_ERat_properties

lemma Matrix.dotProd_eq_bot {v : J → ℚ∞} {w : J → ℚ≥0} (hvw : v ᵥ⬝ w = ⊥) :
    ∃ j : J, v j = ⊥ := by
  by_contra! contr
  exact Matrix.no_bot_dotProd_nneg contr w hvw

lemma Matrix.zero_dotProd (w : J → ℚ≥0) : (0 : J → ℚ∞) ᵥ⬝ w = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact smul_zero (w j)

lemma Matrix.dotProd_add (x : J → ℚ∞) (v w : J → ℚ≥0) :
    x ᵥ⬝ (v + w) = x ᵥ⬝ v + x ᵥ⬝ w := by
  simp [Matrix.dotProd, ERat.add_smul, Finset.sum_add_distrib]

lemma Matrix.dotProd_smul {k : ℚ≥0} (hk : 0 < k) (x : J → ℚ∞) (v : J → ℚ≥0) :
    x ᵥ⬝ (k • v) = k • (x ᵥ⬝ v) := by
  show ∑ j : J, (k * v j) • x j = k • ∑ j : J, v j • x j
  rw [←Finset.smul_ERat_sum hk]
  apply congr_arg
  ext
  apply ERat.mul_smul

lemma Matrix.no_top_dotProd_nneg {v : I → ℚ∞} (hv : ∀ i, v i ≠ ⊤) (w : I → ℚ≥0) :
    v ᵥ⬝ w ≠ (⊤ : ℚ∞) := by
  apply Multiset.sum_neq_ERat_top
  rw [Multiset.mem_map]
  intro ⟨i, _, hi⟩
  match hvi : v i with
  | ⊥ => exact bot_ne_top (hvi ▸ hi)
  | ⊤ => exact false_of_ne (hvi ▸ hv i)
  | (_ : ℚ) => exact ERat.coe_neq_top _ (hvi ▸ hi)

end dotProd_ERat_properties

section matrix_ERat_properties

lemma Matrix.ERat_neg_zero : -(0 : Matrix I J ℚ∞) = 0 := by
  ext
  apply neg_zero

lemma Matrix.ERat_neg_neg (M : Matrix I J ℚ∞) : -(-M) = M := by
  ext
  apply neg_neg

lemma Matrix.zero_mulWeig (v : J → ℚ≥0) : (0 : Matrix I J ℚ∞) ₘ* v = 0 := by
  ext
  simp [Matrix.mulWeig, Matrix.dotProd]

lemma Matrix.mulWeig_add (M : Matrix I J ℚ∞) (v w : J → ℚ≥0) :
    M ₘ* (v + w) = M ₘ* v + M ₘ* w := by
  ext
  apply Matrix.dotProd_add

lemma Matrix.mulWeig_smul {k : ℚ≥0} (hk : 0 < k) (M : Matrix I J ℚ∞) (v : J → ℚ≥0) :
    M ₘ* (k • v) = k • (M ₘ* v) := by
  ext
  apply Matrix.dotProd_smul hk

end matrix_ERat_properties

section extended_LP_properties

lemma ExtendedLP.IsUnbounded.iff (P : ExtendedLP I J) :
    P.IsUnbounded ↔ ∀ r : ℚ, ∃ p : ℚ∞, P.Reaches p ∧ p < r := by
  simp [ExtendedLP.IsUnbounded, ExtendedLP.IsBoundedBy]

lemma ExtendedLP.unbounded_of_reaches_le {P : ExtendedLP I J} (hP : ∀ r : ℚ, ∃ p : ℚ∞, P.Reaches p ∧ p ≤ r) :
    P.IsUnbounded := by
  rw [ExtendedLP.IsUnbounded.iff]
  intro r
  obtain ⟨p, hPp, hpr⟩ := hP (r-1)
  exact ⟨p, hPp, hpr.trans_lt (ERat.coe_lt_coe_iff.mpr (sub_one_lt r))⟩

lemma ExtendedLP.dualize_dualize (P : ExtendedLP I J) : P = P.dualize.dualize := by
  obtain ⟨_, _, _⟩ := P
  simp [ExtendedLP.dualize, ←Matrix.ext_iff]

variable [DecidableEq I] [DecidableEq J]

lemma ExtendedLP.infeasible_of_unbounded {P : ExtendedLP I J} (hP : P.IsUnbounded) :
    ¬P.dualize.IsFeasible := by
  intro ⟨q, hq⟩
  rw [ExtendedLP.IsUnbounded.iff] at hP
  obtain ⟨p, hp, hpq⟩ := hP (-q)
  have wd := P.weakDuality hp hq
  match p with
  | ⊥ => simp at wd
  | ⊤ => simp at hpq
  | (_ : ℚ) =>
    rw [←ERat.coe_add, ←ERat.coe_zero, ERat.coe_le_coe_iff] at wd
    rw [ERat.coe_lt_coe_iff] at hpq
    linarith

lemma ExtendedLP.unbounded_of_feasible_of_neg {P : ExtendedLP I J} (hP : P.IsFeasible)
    {x₀ : J → ℚ≥0} (hx₀ : P.c ᵥ⬝ x₀ < 0) (hAx₀ : P.A ₘ* x₀ + (0 : ℚ≥0) • (-P.b) ≤ 0) :
    P.IsUnbounded := by
  obtain ⟨e, xₚ, hxₚ, he⟩ := hP
  apply ExtendedLP.unbounded_of_reaches_le
  intro s
  if hs : e ≤ s then
    refine ⟨e, ⟨xₚ, hxₚ, he⟩, ?_⟩
    simpa using hs
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
      have coef_pos : 0 < (s - e) / d
      · apply div_pos_of_neg_of_neg
        · rwa [sub_neg]
        · rwa [←ERat.coe_neg']
      let k : ℚ≥0 := ⟨((s - e) / d), coef_pos.le⟩
      let k_pos : 0 < k := coef_pos
      refine ⟨s, ⟨xₚ + k • x₀, ?_, ?_⟩, by rfl⟩
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
            rw [←ERat.coe_neg, ERat.zero_smul_coe]
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
        intro d_eq_0
        exfalso
        rw [d_eq_0] at hx₀
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
  | inl case_X =>
    obtain ⟨X, hX⟩ := case_X
    rw [
      Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
      ←Sum.elim_comp_inl_inr X, Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add
    ] at hX
    set y := X ∘ Sum.inr
    set x := X ∘ Sum.inl
    obtain ⟨⟨hx, hy⟩, hxy⟩ := hX
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
      | (_ : ℚ) =>
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
  | inr case_Y =>
    obtain ⟨Y, hAY, hbc⟩ := case_Y
    rw [
      Matrix.transpose_fromRows, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero,
      Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.transpose_row, Matrix.fromColumns_neg,
      ←Sum.elim_comp_inl_inr Y, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.fromBlocks_neg, Matrix.ERat_neg_neg, Matrix.ERat_neg_zero, Matrix.ERat_neg_zero,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig,
      ←Sum.elim_comp_inl_inr (Y ∘ Sum.inl), Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add,
    ] at hAY
    rw [←Sum.elim_comp_inl_inr Y, ←Sum.elim_comp_inl_inr (Y ∘ Sum.inl)] at hbc
    set z := Y ∘ Sum.inr
    set x := (Y ∘ Sum.inl) ∘ Sum.inr
    set y := (Y ∘ Sum.inl) ∘ Sum.inl
    have hAyx : Sum.elim (-P.Aᵀ ₘ* y) (P.A ₘ* x) + z 0 • (-Sum.elim P.c P.b) ≤ 0
    · convert hAY
      ext
      simp [Matrix.col, Matrix.mulWeig, Matrix.dotProd]
    set z := z 0
    have hAyx' : Sum.elim (-P.Aᵀ ₘ* y) (P.A ₘ* x) + Sum.elim (z • (-P.c)) (z • (-P.b)) ≤ 0
    · convert hAyx
      aesop
    clear hAY hAyx
    rw [←Sum.elim_add_add, Sum.elim_nonpos_iff] at hAyx'
    obtain ⟨hy, hx⟩ := hAyx'
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
        exact P.dualize.infeasible_of_unbounded (P.dualize.unbounded_of_feasible_of_neg hQ hyb hy) (P.dualize_dualize ▸ hP)
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
      | (_ : ℚ) =>
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

lemma ExtendedLP.strongDuality_of_both_feasible {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : ℚ, P.Reaches (-r).toERat ∧ P.dualize.Reaches r.toERat := by
  obtain ⟨p, q, hp, hq, hpq⟩ := P.strongDuality_aux hP hQ
  have h0pq : 0 ≤ p + q
  · rw [←ERat.coe_le_coe_iff, ERat.coe_add, ERat.coe_zero]
    exact P.weakDuality hp hq
  have hqp : -q = p
  · rw [neg_eq_iff_add_eq_zero, add_comm]
    exact eq_of_le_of_le hpq h0pq
  exact ⟨q, hqp ▸ hp, hq⟩

lemma ExtendedLP.unbounded_of_feasible_of_infeasible {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : ¬P.dualize.IsFeasible) :
    P.IsUnbounded := by
  let I' : Type _ := { i : I // P.b i ≠ ⊤ }
  let A' : Matrix I' J ℚ∞ := Matrix.of (fun i' : I' => P.A i'.val)
  let b' : I' → ℚ∞ := (fun i' : I' => P.b i'.val)
  cases or_of_neq (extendedFarkas (-A'ᵀ) P.c (by aeply P.hAj) (by aeply P.hAi) (by aeply P.hAc) (by aeply P.hcj)) with
  | inl caseI =>
    exfalso
    obtain ⟨y, hy⟩ := caseI
    match hby : b' ᵥ⬝ y with
    | ⊥ => exact Matrix.no_bot_dotProd_nneg (fun i hi => P.hbi ⟨i.val, hi⟩) y hby
    | ⊤ => exact Matrix.no_top_dotProd_nneg (·.property) y hby
    | (q : ℚ) =>
      apply hQ
      use q, (fun i : I => if hi : (P.b i ≠ ⊤) then y ⟨i, hi⟩ else 0)
      constructor
      · unfold ExtendedLP.dualize ExtendedLP.IsSolution Matrix.mulWeig
        convert hy
        simp only [Matrix.mulWeig, Matrix.dotProd, dite_not, dite_smul]
        rw [Finset.sum_dite]
        convert zero_add _ using 1
        apply congr_arg₂
        · apply Finset.sum_eq_zero
          intro i _
          apply ERat.zero_smul_nonbot
          intro contr
          exact P.hAb ⟨i.val, by aesop, by aesop⟩
        · rw [←Finset.sum_coe_sort_eq_attach]
          apply Finset.subtype_univ_sum_eq_subtype_univ_sum
          · simp [Finset.mem_filter]
          · intros
            rfl
      · simp only [Matrix.dotProd, dite_not, dite_smul]
        rw [Finset.sum_dite]
        convert zero_add _
        · apply Finset.sum_eq_zero
          intro i _
          apply ERat.zero_smul_nonbot
          intro contr
          exact P.hbi ⟨i.val, contr⟩
        · change hby to b' ᵥ⬝ y = q.toERat
          rw [←Finset.sum_coe_sort_eq_attach, ←hby]
          apply Finset.subtype_univ_sum_eq_subtype_univ_sum
          · simp [Finset.mem_filter]
          · intros
            rfl
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
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi, ERat.neg_top, ERat.smul_bot, ERat.add_bot]
      apply bot_le
    | (q : ℚ) =>
      change hbi to P.b i = q.toERat
      have hq : -q.toERat ≠ (⊥ : ℚ∞)
      · rw [←ERat.coe_neg]
        apply ERat.coe_neq_bot
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi, ERat.zero_smul_nonbot hq, add_zero]
      exact hAx ⟨i, hbi ▸ ERat.coe_neq_top q⟩

lemma ExtendedLP.optimum_unique {P : ExtendedLP I J} {r s : ℚ}
    (hPr : P.Reaches r.toERat ∧ P.IsBoundedBy r) (hPs : P.Reaches s.toERat ∧ P.IsBoundedBy s) :
    r = s := by
  rw [←ERat.coe_eq_coe_iff]
  apply eq_of_le_of_le
  · apply hPr.right
    exact hPs.left
  · apply hPs.right
    exact hPr.left

lemma ExtendedLP.optimum_eq_of_reaches_bounded {P : ExtendedLP I J} {r : ℚ}
    (reaches : P.Reaches r.toERat) (bounded : P.IsBoundedBy r) :
    P.optimum = some r := by
  have hP : P.IsFeasible
  · obtain ⟨x, hx⟩ := reaches
    exact ⟨r, x, hx⟩
  have hPP : ∃ r : ℚ, P.Reaches r.toERat ∧ P.IsBoundedBy r
  · use r
  have hPb : ¬P.IsUnbounded
  · exact (· ⟨r, bounded⟩)
  simp [ExtendedLP.optimum, hP, hPP, hPb]
  congr
  exact ExtendedLP.optimum_unique hPP.choose_spec ⟨reaches, bounded⟩

/-- `Opposites p q` essentially says `p ≠ none ∧ q ≠ none ∧ p = -q`. -/
def Opposites : Option ℚ∞ → Option ℚ∞ → Prop
| (p : ℚ∞), (q : ℚ∞) => p = -q  -- includes `⊥ = -⊤` and `⊤ = -⊥`
| _       , _        => False   -- namely `none ≠ -none`

lemma opposites_comm (p q : Option ℚ∞) : Opposites p q ↔ Opposites q p := by
  cases p with
  | none =>
    convert_to False ↔ False
    · simp [Opposites]
    rfl
  | some r =>
    cases q with
    | none => trivial
    | some s =>
      if hrs : r = -s then
        convert_to True ↔ True
        · simpa [Opposites]
        · simpa [Opposites, neg_eq_iff_eq_neg] using hrs.symm
        rfl
      else
        convert_to False ↔ False
        · simpa [Opposites]
        · simpa [Opposites, neg_eq_iff_eq_neg] using Ne.symm hrs
        rfl

lemma ExtendedLP.strongDuality_of_prim_feas {P : ExtendedLP I J} (hP : P.IsFeasible) :
    Opposites P.optimum P.dualize.optimum := by
  if hQ : P.dualize.IsFeasible then
    obtain ⟨r, hPr, hQr⟩ := P.strongDuality_of_both_feasible hP hQ
    have hPopt : P.optimum = some (-r).toERat
    · apply ExtendedLP.optimum_eq_of_reaches_bounded hPr
      intro p hPp
      have Pwd := P.weakDuality hPp hQr
      match p with
      | ⊥ => simp at Pwd
      | ⊤ => apply le_top
      | (_ : ℚ) =>
        rw [←ERat.coe_add, ←ERat.coe_zero] at Pwd
        rw [ERat.coe_le_coe_iff] at Pwd ⊢
        rwa [neg_le_iff_add_nonneg]
    have hQopt : P.dualize.optimum = some r.toERat
    · apply ExtendedLP.optimum_eq_of_reaches_bounded hQr
      intro q hQq
      have Qwd := P.weakDuality hPr hQq
      match q with
      | ⊥ => simp at Qwd
      | ⊤ => apply le_top
      | (_ : ℚ) =>
        rw [←ERat.coe_add, ←ERat.coe_zero, add_comm] at Qwd
        rw [ERat.coe_le_coe_iff] at Qwd ⊢
        rwa [le_add_neg_iff_le] at Qwd
    rewrite [hPopt, hQopt]
    rfl
  else
    have hPopt : P.optimum = some ⊥
    · simp [ExtendedLP.optimum, hP, ExtendedLP.unbounded_of_feasible_of_infeasible hP hQ]
    have hQopt : P.dualize.optimum = some ⊤
    · simp [ExtendedLP.optimum, hQ]
    rw [hPopt, hQopt]
    exact ERat.neg_top

lemma ExtendedLP.strongDuality_of_dual_feas {P : ExtendedLP I J} (hQ : P.dualize.IsFeasible) :
    Opposites P.optimum P.dualize.optimum := by
  rw [opposites_comm]
  nth_rw 2 [P.dualize_dualize]
  exact P.dualize.strongDuality_of_prim_feas hQ

theorem ExtendedLP.strongDuality {P : ExtendedLP I J} (feas : P.IsFeasible ∨ P.dualize.IsFeasible) :
    Opposites P.optimum P.dualize.optimum :=
  feas.casesOn
    (P.strongDuality_of_prim_feas ·)
    (P.strongDuality_of_dual_feas ·)

end extended_LP_properties

end strong_duality

#print axioms ExtendedLP.strongDuality
