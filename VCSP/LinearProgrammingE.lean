import VCSP.FarkasSpecial


/-- Linear program over `F∞` in the standard form (i.e.,
    a system of linear inequalities with nonnegative variables).
    Variables are of type `J`. Conditions are indexed by type `I`.
    Its objective function is intended to be minimized. -/
structure ExtendedLP (I J F : Type*) [LinearOrderedField F] where
  /-- The left-hand-side matrix. -/
  A : Matrix I J (F∞)
  /-- The right-hand-side vector. -/
  b : I → (F∞)
  /-- The objective function coefficients. -/
  c : J → (F∞)
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

variable {I J F : Type*} [Fintype I] [Fintype J] [LinearOrderedField F]

section extended_LP_definitions

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution (P : ExtendedLP I J F) (x : J → { a : F // 0 ≤ a }) : Prop :=
  P.A ₘ* x ≤ P.b

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. Note that `⊤` can be reached but `⊥` cannot. -/
def ExtendedLP.Reaches (P : ExtendedLP I J F) (r : F∞) : Prop :=
  ∃ x : J → { a : F // 0 ≤ a }, P.IsSolution x ∧ P.c ᵥ⬝ x = r

/-- Linear program `P` is feasible iff `P` reaches a finite value. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J F) : Prop :=
  ∃ p : F, P.Reaches (toE p)

/-- Linear program `P` is bounded by `r` iff every value reached by `P` is
    greater or equal to `r` (i.e., `P` is bounded from below). -/
def ExtendedLP.IsBoundedBy (P : ExtendedLP I J F) (r : F) : Prop :=
  ∀ p : F∞, P.Reaches p → r ≤ p

/-- Linear program `P` is unbounded iff values reached by `P` have no finite lower bound. -/
def ExtendedLP.IsUnbounded (P : ExtendedLP I J F) : Prop :=
  ¬∃ r : F, P.IsBoundedBy r

/-- Dualize a linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function. -/
def ExtendedLP.dualize (P : ExtendedLP I J F) : ExtendedLP J I F :=
  ⟨-P.Aᵀ, P.c, P.b, by aeply P.hAj, by aeply P.hAi, P.hcj, P.hbi, by aeply P.hAc, by aeply P.hAb⟩

open scoped Classical in
/-- Extended notion of "optimum" of "minimization LP" (the less the better). -/
noncomputable def ExtendedLP.optimum (P : ExtendedLP I J F) : Option F∞ :=
  if P.IsFeasible then
    if P.IsUnbounded then
      some none --some ⊥ -- unbounded means that the minimum is `⊥`
    else
      if hr : ∃ r : F, P.Reaches (toE r) ∧ P.IsBoundedBy r then
        some (toE hr.choose) -- the minimum is finite
      else
        none -- invalid finite value (infimum is not attained; later, we prove it cannot happen)
  else
    some ⊤ -- infeasible means that the minimum is `⊤`

/-- `OppositesOpt p q` essentially says `none ≠ p = -q`. -/
def OppositesOpt : Option (F∞) → Option (F∞) → Prop
| (p : F∞), (q : F∞) => p = -q  -- opposite values; includes `⊥ = -⊤` and `⊤ = -⊥`
| _       , _        => False   -- namely `OppositesOpt none none = False`

end extended_LP_definitions


section weak_duality

lemma EF.one_smul (r : F∞) : (1 : { a : F // 0 ≤ a }) • r = r :=
  match r with
  | ⊥ => rfl
  | ⊤ => sorry--rfl
  | (q : F) => congr_arg toE (one_mul q)

lemma EF.sub_nonpos_iff (r s : F∞) : r + (-s) ≤ 0 ↔ r ≤ s := by
  match r with
  | ⊥ => convert_to True ↔ True <;> simp
  | ⊤ => match s with
    | ⊥ => convert_to False ↔ False <;> simp
    | ⊤ => convert_to True ↔ True <;> simp
    | (_ : F) => convert_to False ↔ False <;> simp [←EF.coe_neg]
  | (_ : F) => match s with
    | ⊥ => convert_to False ↔ False <;> simp
    | ⊤ => convert_to True ↔ True <;> simp
    | (_ : F) => simp [←EF.coe_neg, ←EF.coe_add]

lemma EF.vec_sub_nonpos_iff (u v : I → F∞) : u + (-v) ≤ 0 ↔ u ≤ v := by
  constructor <;> intro huv i <;> simpa [EF.sub_nonpos_iff] using huv i

lemma Matrix.sumElim_dotProd_sumElim (u : I → F∞) (v : J → F∞) (x : I → { a : F // 0 ≤ a }) (y : J → { a : F // 0 ≤ a }) :
    Sum.elim u v ᵥ⬝ Sum.elim x y = u ᵥ⬝ x + v ᵥ⬝ y := by
  simp [Matrix.dotProd]

lemma Matrix.fromRows_mulWeig {I₁ I₂ : Type*} (M₁ : Matrix I₁ J (F∞)) (M₂ : Matrix I₂ J (F∞)) (v : J → { a : F // 0 ≤ a }) :
    Matrix.fromRows M₁ M₂ ₘ* v = Sum.elim (M₁ ₘ* v) (M₂ ₘ* v) := by
  ext i
  cases i <;> rfl

lemma Matrix.fromColumns_mulWeig_sumElim {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (M₁ : Matrix I J₁ (F∞)) (M₂ : Matrix I J₂ (F∞)) (v₁ : J₁ → { a : F // 0 ≤ a }) (v₂ : J₂ → { a : F // 0 ≤ a }) :
    Matrix.fromColumns M₁ M₂ ₘ* Sum.elim v₁ v₂ = M₁ ₘ* v₁ + M₂ ₘ* v₂ := by
  ext
  simp [Matrix.fromColumns, Matrix.mulWeig, Matrix.dotProd]

theorem ExtendedLP.weakDuality [DecidableEq I] [DecidableEq J] {P : ExtendedLP I J F}
    {p : F∞} (hP : P.Reaches p) {q : F∞} (hQ : P.dualize.Reaches q) :
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
            | (q : F) =>
              dsimp only [ExtendedLP.dualize] at contr
              rw [hby] at contr
              change contr to ⊤ + toE q < 0
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
      · rwa [EF.vec_sub_nonpos_iff]
      convert hle0
      ext
      simp [Matrix.mulWeig, Matrix.dotProd, EF.one_smul]
    · have hlt0 : P.b ᵥ⬝ y + P.c ᵥ⬝ x < 0
      · push_neg at contr
        rwa [add_comm]
      rw [Matrix.sumElim_dotProd_sumElim]
      simp [Matrix.dotProd]
      rwa [EF.one_smul]

end weak_duality


section strong_duality

lemma NNRat.pos_of_not_zero {k : { a : F // 0 ≤ a }} (hk : ¬(k = 0)) :
    0 < k := by
  apply lt_of_le_of_ne k.property
  intro contr
  apply hk
  sorry--simpa using contr.symm

section misc_EF_properties

lemma EF.smul_nonpos {r : F∞} (hr : r ≤ 0) (k : { a : F // 0 ≤ a }) :
    k • r ≤ 0 := by
  match r with
  | ⊥ => apply bot_le
  | ⊤ => simp at hr
  | (_ : F) => exact EF.coe_le_coe_iff.mpr (mul_nonpos_of_nonneg_of_nonpos k.property (coe_nonpos.mp hr))

lemma EF.smul_lt_smul_left {k : { a : F // 0 ≤ a }} (hk : 0 < k) (r s : F∞) :
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
      · rw [EF.pos_smul_top hk, iff_true]
        apply bot_lt_top
      · simp
      rfl
    | ⊤ =>
      convert_to False ↔ False
      · apply lt_self_iff_false
      · apply lt_self_iff_false
      rfl
    | (_ : F) =>
      convert_to True ↔ True
      · rw [EF.pos_smul_top hk, iff_true]
        apply coe_lt_top
      · simp
      rfl
  | (q : F) =>
    match r with
    | ⊥ =>
      convert_to True ↔ True
      · rw [iff_true]
        apply bot_lt_coe
      · simp
      rfl
    | ⊤ =>
      convert_to False ↔ False
      · rw [EF.pos_smul_top hk, iff_false]
        apply not_top_lt
      · simp
      rfl
    | (p : F) =>
      rw [EF.coe_lt_coe_iff]
      show toE (k * p) < toE (k * q) ↔ p < q
      rw [EF.coe_lt_coe_iff]
      exact mul_lt_mul_left hk

lemma EF.smul_le_smul_left {k : { a : F // 0 ≤ a }} (hk : 0 < k) (r s : F∞) :
    k • r ≤ k • s ↔ r ≤ s := by
  convert neg_iff_neg (EF.smul_lt_smul_left hk s r) <;> exact Iff.symm not_lt

lemma EF.smul_neg {k : { a : F // 0 ≤ a }} {r : F∞} (hkr : k = 0 → r ≠ ⊥ ∧ r ≠ ⊤) :
    k • (-r) = -(k • r) := by
  match r with
  | ⊥ =>
    rw [neg_bot]
    if hk : 0 < k then
      rewrite [EF.pos_smul_top hk]
      rfl
    else
      exfalso
      simp_all
  | ⊤ =>
    rw [neg_top]
    if hk : 0 < k then
      rewrite [EF.pos_smul_top hk, neg_top]
      rfl
    else
      exfalso
      simp_all
  | (q : F) =>
    rw [←EF.coe_neg]
    show toE (k * (-q)) = toE (-(k * q))
    rw [mul_neg]

lemma EF.pos_smul_neg {k : { a : F // 0 ≤ a }} (hk : 0 < k) (r : F∞) :
    k • (-r) = -(k • r) := by
  apply EF.smul_neg
  intro h0
  exfalso
  exact (h0 ▸ hk).false

lemma EF.smul_smul {k : { a : F // 0 ≤ a }} (hk : 0 < k) (l : { a : F // 0 ≤ a }) (r : F∞) :
    l • (k • r) = k • (l • r) := by
  match r with
  | ⊥ =>
    rw [EF.smul_bot, EF.smul_bot, EF.smul_bot]
  | ⊤ =>
    rw [EF.pos_smul_top hk]
    if hl : 0 < l then
      rw [EF.pos_smul_top hl, EF.pos_smul_top hk]
    else if hl0 : l = 0 then
      rw [hl0]
      symm
      sorry--apply smul_zero
    else
      exfalso
      simp_all only [not_lt, nonpos_iff_eq_zero]
  | (q : F) =>
    exact EF.coe_eq_coe_iff.mpr (mul_left_comm l.val k.val q)

lemma EF.add_smul (k l : { a : F // 0 ≤ a }) (r : F∞) :
    (k + l) • r = k • r + l • r := by
  match r with
  | ⊥ =>
    rewrite [EF.smul_bot, EF.smul_bot, EF.smul_bot]
    rfl
  | ⊤ =>
    if k_eq_0 : k = 0 then
      rw [k_eq_0, EF.zero_smul_nonbot top_ne_bot, zero_add, zero_add]
    else
      have k_pos : 0 < k
      · exact NNRat.pos_of_not_zero k_eq_0
      rw [EF.pos_smul_top (add_pos_of_pos_of_nonneg k_pos l.property)]
      rw [EF.pos_smul_top k_pos]
      if l_eq_0 : l = 0 then
        rewrite [l_eq_0]
        sorry--rfl
      else
        rewrite [EF.pos_smul_top (NNRat.pos_of_not_zero l_eq_0)]
        rfl
  | (q : F) =>
    show toE ((k + l) * q) = toE (k * q) + toE (l * q)
    rw [←EF.coe_add, add_mul]

lemma EF.smul_add {k : { a : F // 0 ≤ a }} (hk : 0 < k) (r s : F∞) :
    k • (r + s) = k • r + k • s := by
  match r, s with
  | ⊥, _ =>
    rw [EF.bot_add, EF.smul_bot, EF.bot_add]
  | _, ⊥ =>
    rw [EF.add_bot, EF.smul_bot, EF.add_bot]
  | (p : F), (q : F) =>
    show toE (k * (p + q)) = toE (k * p) + toE (k * q)
    rewrite [mul_add]
    rfl
  | (p : F), ⊤ =>
    rw [EF.coe_add_top, EF.pos_smul_top hk]
    show ⊤ = toE (k * p) + ⊤
    rw [EF.coe_add_top]
  | ⊤, (q : F) =>
    rw [EF.top_add_coe, EF.pos_smul_top hk]
    show ⊤ = ⊤ + toE (k * q)
    rw [EF.top_add_coe]
  | ⊤, ⊤ =>
    rw [EF.top_add_top, EF.pos_smul_top hk, EF.top_add_top]

lemma EF.mul_smul (k l : { a : F // 0 ≤ a }) (r : F∞) :
    (k * l) • r = k • (l • r) := by
  match r with
  | ⊥ =>
    iterate 3 rw [EF.smul_bot]
  | ⊤ =>
    if l_eq_0 : l = 0 then
      rw [l_eq_0, EF.zero_smul_nonbot top_ne_bot, mul_zero, EF.zero_smul_nonbot top_ne_bot, smul_zero]
    else
      have l_pos : 0 < l
      · apply lt_of_le_of_ne l.property
        intro contr
        apply l_eq_0
        convert contr.symm
        exact eq_iff_eq_of_cmp_eq_cmp rfl
      rw [EF.pos_smul_top l_pos]
      if k_eq_0 : k = 0 then
        rw [k_eq_0, EF.zero_smul_nonbot top_ne_bot, zero_mul, EF.zero_smul_nonbot top_ne_bot]
      else
        have c_pos : 0 < k
        · exact NNRat.pos_of_not_zero k_eq_0
        rw [EF.pos_smul_top c_pos, EF.pos_smul_top (mul_pos c_pos l_pos)]
  | (q : F) =>
    show toE ((k * l) * q) = toE (k * (l * q))
    rw [mul_assoc]

lemma EF.one_smul_vec (v : J → F∞) :
    (1 : { a : F // 0 ≤ a }) • v = v := by
  ext
  apply EF.one_smul

lemma EF.smul_add_vec {k : { a : F // 0 ≤ a }} (hk : 0 < k) (v w : J → F∞) :
    k • (v + w) = k • v + k • w := by
  ext
  apply EF.smul_add hk

lemma EF.mul_smul_vec (k l : { a : F // 0 ≤ a }) (v : J → F∞) :
    (k * l) • v = k • (l • v) := by
  ext
  apply EF.mul_smul

lemma EF.vec_smul_le_smul_left {k : { a : F // 0 ≤ a }} (hk : 0 < k) (u v : I → F∞) :
    k • u ≤ k • v ↔ u ≤ v := by
  constructor <;> intro huv <;> intro i <;> specialize huv i
  · exact (EF.smul_le_smul_left hk _ _).mp huv
  · exact (EF.smul_le_smul_left hk _ _).mpr huv

lemma Multiset.sum_neq_EF_top {s : Multiset (F∞)} (hs : ⊤ ∉ s) :
    s.sum ≠ ⊤ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.sum_cons]
    match a with
    | ⊥ => simp
    | ⊤ => simp at hs
    | (_ : F) => match hm : m.sum with
      | ⊥ => simp
      | ⊤ => exact (ih (by simpa using hs) hm).elim
      | (_ : F) => simp [←EF.coe_add]

lemma Multiset.smul_EF_sum {k : { a : F // 0 ≤ a }} (hk : 0 < k) (s : Multiset (F∞)) :
    s.summap (k • ·) = k • s.sum := by
  induction s using Multiset.induction with
  | empty => simp [Multiset.summap]
  | cons a m ih => simp [Multiset.summap, EF.smul_add hk, ←ih]

lemma Finset.smul_EF_sum {k : { a : F // 0 ≤ a }} (hk : 0 < k) (v : J → F∞) :
    ∑ j : J, k • v j = k • ∑ j : J, v j := by
  convert Multiset.smul_EF_sum hk (Finset.univ.val.map v)
  simp [Multiset.summap]

end misc_EF_properties

section dotProd_EF_properties

lemma Matrix.dotProd_eq_bot {v : J → F∞} {w : J → { a : F // 0 ≤ a }} (hvw : v ᵥ⬝ w = ⊥) :
    ∃ j : J, v j = ⊥ := by
  by_contra! contr
  exact Matrix.no_bot_dotProd_nneg contr w hvw

lemma Matrix.zero_dotProd (w : J → { a : F // 0 ≤ a }) : (0 : J → F∞) ᵥ⬝ w = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact smul_zero (w j)

lemma Matrix.dotProd_add (x : J → F∞) (v w : J → { a : F // 0 ≤ a }) :
    x ᵥ⬝ (v + w) = x ᵥ⬝ v + x ᵥ⬝ w := by
  simp [Matrix.dotProd, EF.add_smul, Finset.sum_add_distrib]

lemma Matrix.dotProd_smul {k : { a : F // 0 ≤ a }} (hk : 0 < k) (x : J → F∞) (v : J → { a : F // 0 ≤ a }) :
    x ᵥ⬝ (k • v) = k • (x ᵥ⬝ v) := by
  show ∑ j : J, (k * v j) • x j = k • ∑ j : J, v j • x j
  rw [←Finset.smul_EF_sum hk]
  apply congr_arg
  ext
  apply EF.mul_smul

lemma Matrix.no_top_dotProd_nneg {v : I → F∞} (hv : ∀ i, v i ≠ ⊤) (w : I → { a : F // 0 ≤ a }) :
    v ᵥ⬝ w ≠ (⊤ : F∞) := by
  apply Multiset.sum_neq_EF_top
  rw [Multiset.mem_map]
  intro ⟨i, _, hi⟩
  match hvi : v i with
  | ⊥ => exact bot_ne_top (hvi ▸ hi)
  | ⊤ => exact false_of_ne (hvi ▸ hv i)
  | (_ : F) => exact EF.coe_neq_top _ (hvi ▸ hi)

end dotProd_EF_properties

section matrix_EF_properties

lemma Matrix.EF_neg_zero : -(0 : Matrix I J (F∞)) = 0 := by
  ext
  apply neg_zero

lemma Matrix.EF_neg_neg (M : Matrix I J (F∞)) : -(-M) = M := by
  ext
  apply neg_neg

lemma Matrix.zero_mulWeig (v : J → { a : F // 0 ≤ a }) : (0 : Matrix I J (F∞)) ₘ* v = 0 := by
  ext
  simp [Matrix.mulWeig, Matrix.dotProd]

lemma Matrix.mulWeig_add (M : Matrix I J (F∞)) (v w : J → { a : F // 0 ≤ a }) :
    M ₘ* (v + w) = M ₘ* v + M ₘ* w := by
  ext
  apply Matrix.dotProd_add

lemma Matrix.mulWeig_smul {k : { a : F // 0 ≤ a }} (hk : 0 < k) (M : Matrix I J (F∞)) (v : J → { a : F // 0 ≤ a }) :
    M ₘ* (k • v) = k • (M ₘ* v) := by
  ext
  apply Matrix.dotProd_smul hk

end matrix_EF_properties

section extended_LP_properties

lemma ExtendedLP.IsUnbounded.iff (P : ExtendedLP I J F) :
    P.IsUnbounded ↔ ∀ r : F, ∃ p : F∞, P.Reaches p ∧ p < r := by
  simp [ExtendedLP.IsUnbounded, ExtendedLP.IsBoundedBy]

lemma ExtendedLP.unbounded_of_reaches_le {P : ExtendedLP I J F} (hP : ∀ r : F, ∃ p : F∞, P.Reaches p ∧ p ≤ r) :
    P.IsUnbounded := by
  rw [ExtendedLP.IsUnbounded.iff]
  intro r
  obtain ⟨p, hPp, hpr⟩ := hP (r-1)
  exact ⟨p, hPp, hpr.trans_lt (EF.coe_lt_coe_iff.mpr (sub_one_lt r))⟩

lemma ExtendedLP.dualize_dualize (P : ExtendedLP I J F) : P = P.dualize.dualize := by
  obtain ⟨_, _, _⟩ := P
  simp [ExtendedLP.dualize, ←Matrix.ext_iff]

variable [DecidableEq I] [DecidableEq J]

lemma ExtendedLP.infeasible_of_unbounded {P : ExtendedLP I J F} (hP : P.IsUnbounded) :
    ¬P.dualize.IsFeasible := by
  intro ⟨q, hq⟩
  rw [ExtendedLP.IsUnbounded.iff] at hP
  obtain ⟨p, hp, hpq⟩ := hP (-q)
  have wd := P.weakDuality hp hq
  match p with
  | ⊥ => simp at wd
  | ⊤ => simp at hpq
  | (_ : F) =>
    rw [←EF.coe_add, ←EF.coe_zero, EF.coe_le_coe_iff] at wd
    rw [EF.coe_lt_coe_iff] at hpq
    linarith

lemma ExtendedLP.unbounded_of_feasible_of_neg {P : ExtendedLP I J F} (hP : P.IsFeasible)
    {x₀ : J → { a : F // 0 ≤ a }} (hx₀ : P.c ᵥ⬝ x₀ < 0) (hAx₀ : P.A ₘ* x₀ + (0 : { a : F // 0 ≤ a }) • (-P.b) ≤ 0) :
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
    | (d : F) =>
      rw [hcx₀] at hx₀
      have coef_pos : 0 < (s - e) / d
      · apply div_pos_of_neg_of_neg
        · rwa [sub_neg]
        · rwa [←EF.coe_neg']
      let k : { a : F // 0 ≤ a } := ⟨((s - e) / d), coef_pos.le⟩
      let k_pos : 0 < k := coef_pos
      refine ⟨s, ⟨xₚ + k • x₀, ?_, ?_⟩, by rfl⟩
      · intro i
        match hi : P.b i with
        | ⊥ =>
          exfalso
          exact P.hbi ⟨i, hi⟩
        | ⊤ =>
          apply le_top
        | (bᵢ : F) =>
          specialize hAx₀ i
          rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hi] at hAx₀
          have zeros : (P.A ₘ* x₀) i + (0 : F∞) ≤ 0
          · convert hAx₀
            show 0 = 0 • -(toE bᵢ)
            rw [←EF.coe_neg, EF.zero_smul_coe]
          rw [add_zero] at zeros
          rw [Matrix.mulWeig_add, Matrix.mulWeig_smul k_pos, Pi.add_apply]
          apply add_le_of_le_of_nonpos
          · convert_to (P.A ₘ* xₚ) i ≤ P.b i
            · exact hi.symm
            exact hxₚ i
          · exact EF.smul_nonpos zeros k
      · rw [Matrix.dotProd_add, he, Matrix.dotProd_smul k_pos, hcx₀]
        show toE (e + ((s - e) / d) * d) = toE s
        rw [EF.coe_eq_coe_iff, div_mul_cancel_of_imp]
        exact add_sub_cancel e s
        intro d_eq_0
        exfalso
        rw [d_eq_0] at hx₀
        exact hx₀.false

lemma ExtendedLP.strongDuality_aux {P : ExtendedLP I J F}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ p q : F, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 := by
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
    set x := X ∘ Sum.inl
    set y := X ∘ Sum.inr
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
        exact (hxy.trans_lt EF.zero_lt_top).false
      | (_ : F) =>
        rw [hcx, hby] at hxy
        exact (hxy.trans_lt EF.zero_lt_top).false
    | (p : F) =>
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        exfalso
        apply P.hbi
        exact Matrix.dotProd_eq_bot hby
      | ⊤ =>
        exfalso
        rw [hcx, hby] at hxy
        exact (hxy.trans_lt EF.zero_lt_top).false
      | (q : F) =>
        refine ⟨p, q, ⟨x, hx, hcx⟩, ⟨y, hy, hby⟩, ?_⟩
        rw [←EF.coe_le_coe_iff]
        rwa [hcx, hby] at hxy
  | inr case_Y =>
    obtain ⟨Y, hAY, hbc⟩ := case_Y
    rw [
      Matrix.transpose_fromRows, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero,
      Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.transpose_row, Matrix.fromColumns_neg,
      ←Sum.elim_comp_inl_inr Y, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.fromBlocks_neg, Matrix.EF_neg_neg, Matrix.EF_neg_zero, Matrix.EF_neg_zero,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig,
      ←Sum.elim_comp_inl_inr (Y ∘ Sum.inl), Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add,
    ] at hAY
    rw [←Sum.elim_comp_inl_inr Y, ←Sum.elim_comp_inl_inr (Y ∘ Sum.inl)] at hbc
    set x := (Y ∘ Sum.inl) ∘ Sum.inr
    set y := (Y ∘ Sum.inl) ∘ Sum.inl
    set z := (Y ∘ Sum.inr) 0
    have hAyx : Sum.elim (-P.Aᵀ ₘ* y) (P.A ₘ* x) + z • (-Sum.elim P.c P.b) ≤ 0
    · convert hAY
      ext
      simp [Matrix.col, Matrix.mulWeig, Matrix.dotProd, z]
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
        exact (hbc.trans EF.zero_lt_top).false
      | (_ : F) =>
        rw [hcx, hby] at hbc
        exact (hbc.trans EF.zero_lt_top).false
    | (p : F) =>
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        exfalso
        apply P.hbi
        exact Matrix.dotProd_eq_bot hby
      | ⊤ =>
        exfalso
        rw [hcx, hby] at hbc
        exact (hbc.trans EF.zero_lt_top).false
      | (q : F) =>
        have z_inv_pos : 0 < z⁻¹
        · exact inv_pos_of_pos z_pos
        sorry/-refine ⟨z⁻¹ • p, z⁻¹ • q, ⟨z⁻¹ • x, ?_, ?_⟩, ⟨z⁻¹ • y, ?_, ?_⟩, ?_⟩
        · rwa [
            ←EF.vec_smul_le_smul_left z_inv_pos, smul_zero,
            EF.smul_add_vec z_inv_pos, ←Matrix.mulWeig_smul z_inv_pos, ←EF.mul_smul_vec,
            inv_mul_cancel (ne_of_lt z_pos).symm, EF.one_smul_vec, EF.vec_sub_nonpos_iff
          ] at hx
        · rewrite [Matrix.dotProd_smul z_inv_pos, hcx]
          rfl
        · rwa [
            ←EF.vec_smul_le_smul_left z_inv_pos, smul_zero,
            EF.smul_add_vec z_inv_pos, ←Matrix.mulWeig_smul z_inv_pos, ←EF.mul_smul_vec,
            inv_mul_cancel (ne_of_lt z_pos).symm, EF.one_smul_vec, EF.vec_sub_nonpos_iff
          ] at hy
        · dsimp only [ExtendedLP.dualize]
          rewrite [Matrix.dotProd_smul z_inv_pos, hby]
          rfl
        rw [hcx, hby] at hbc
        show z⁻¹ * p + z⁻¹ * q ≤ 0
        rw [←mul_add]
        have hpq : p + q < 0
        · rw [←EF.coe_lt_coe_iff, add_comm]
          exact hbc
        exact Linarith.mul_nonpos hpq.le z_inv_pos-/

lemma ExtendedLP.strongDuality_of_both_feasible {P : ExtendedLP I J F}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : F, P.Reaches (toE (-r)) ∧ P.dualize.Reaches (toE r) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := P.strongDuality_aux hP hQ
  have h0pq : 0 ≤ p + q
  · rw [←EF.coe_le_coe_iff, EF.coe_add, EF.coe_zero]
    exact P.weakDuality hp hq
  have hqp : -q = p
  · rw [neg_eq_iff_add_eq_zero, add_comm]
    exact eq_of_le_of_le hpq h0pq
  exact ⟨q, hqp ▸ hp, hq⟩

lemma ExtendedLP.unbounded_of_feasible_of_infeasible {P : ExtendedLP I J F}
    (hP : P.IsFeasible) (hQ : ¬P.dualize.IsFeasible) :
    P.IsUnbounded := by
  let I' : Type _ := { i : I // P.b i ≠ ⊤ }
  let A' : Matrix I' J (F∞) := Matrix.of (fun i' : I' => P.A i'.val)
  let b' : I' → (F∞) := (fun i' : I' => P.b i'.val)
  cases or_of_neq (extendedFarkas (-A'ᵀ) P.c (by aeply P.hAj) (by aeply P.hAi) (by aeply P.hAc) (by aeply P.hcj)) with
  | inl caseI =>
    exfalso
    obtain ⟨y, hy⟩ := caseI
    match hby : b' ᵥ⬝ y with
    | ⊥ => exact Matrix.no_bot_dotProd_nneg (fun i hi => P.hbi ⟨i.val, hi⟩) y hby
    | ⊤ => exact Matrix.no_top_dotProd_nneg (·.property) y hby
    | (q : F) =>
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
          apply EF.zero_smul_nonbot
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
          apply EF.zero_smul_nonbot
          intro contr
          exact P.hbi ⟨i.val, contr⟩
        · change hby to b' ᵥ⬝ y = toE q
          rw [←Finset.sum_coe_sort_eq_attach, ←hby]
          apply Finset.subtype_univ_sum_eq_subtype_univ_sum
          · simp [Finset.mem_filter]
          · intros
            rfl
  | inr caseJ =>
    obtain ⟨x, hAx, hcx⟩ := caseJ
    apply ExtendedLP.unbounded_of_feasible_of_neg hP hcx
    rw [Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.EF_neg_neg] at hAx
    intro i
    match hbi : P.b i with
    | ⊥ =>
      exfalso
      exact P.hbi ⟨i, hbi⟩
    | ⊤ =>
      change hbi to P.b i = ⊤
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi, EF.neg_top, EF.smul_bot, EF.add_bot]
      apply bot_le
    | (q : F) =>
      change hbi to P.b i = toE q
      sorry/-have hq : toE (-q) ≠ (⊥ : F∞)
      · rw [←EF.coe_neg]
        apply EF.coe_neq_bot
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi, EF.zero_smul_nonbot hq, add_zero]
      exact hAx ⟨i, hbi ▸ EF.coe_neq_top q⟩-/

end extended_LP_properties

section extended_LP_optima

lemma ExtendedLP.optimum_unique {P : ExtendedLP I J F} {r s : F}
    (hPr : P.Reaches (toE r) ∧ P.IsBoundedBy r) (hPs : P.Reaches (toE s) ∧ P.IsBoundedBy s) :
    r = s := by
  rw [←EF.coe_eq_coe_iff]
  apply eq_of_le_of_le
  · apply hPr.right
    exact hPs.left
  · apply hPs.right
    exact hPr.left

lemma ExtendedLP.optimum_eq_of_reaches_bounded {P : ExtendedLP I J F} {r : F}
    (reaches : P.Reaches (toE r)) (bounded : P.IsBoundedBy r) :
    P.optimum = some r := by
  have hP : P.IsFeasible
  · obtain ⟨x, hx⟩ := reaches
    exact ⟨r, x, hx⟩
  have hPP : ∃ r : F, P.Reaches (toE r) ∧ P.IsBoundedBy r
  · use r
  have hPb : ¬P.IsUnbounded
  · exact (· ⟨r, bounded⟩)
  simp [ExtendedLP.optimum, hP, hPP, hPb]
  congr
  exact ExtendedLP.optimum_unique hPP.choose_spec ⟨reaches, bounded⟩

lemma oppositesOpt_comm (p q : Option (F∞)) : OppositesOpt p q ↔ OppositesOpt q p := by
  cases p with
  | none =>
    convert_to False ↔ False
    · simp [OppositesOpt]
    rfl
  | some r =>
    cases q with
    | none => trivial
    | some s =>
      if hrs : r = -s then
        convert_to True ↔ True
        · simpa [OppositesOpt]
        · simpa [OppositesOpt, neg_eq_iff_eq_neg] using hrs.symm
        rfl
      else
        convert_to False ↔ False
        · simpa [OppositesOpt]
        · simpa [OppositesOpt, neg_eq_iff_eq_neg] using Ne.symm hrs
        rfl

variable [DecidableEq I] [DecidableEq J]

lemma ExtendedLP.strongDuality_of_prim_feas {P : ExtendedLP I J F} (hP : P.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum := by
  if hQ : P.dualize.IsFeasible then
    obtain ⟨r, hPr, hQr⟩ := P.strongDuality_of_both_feasible hP hQ
    have hPopt : P.optimum = some (toE (-r))
    · apply ExtendedLP.optimum_eq_of_reaches_bounded hPr
      intro p hPp
      have Pwd := P.weakDuality hPp hQr
      match p with
      | ⊥ => simp at Pwd
      | ⊤ => apply le_top
      | (_ : F) =>
        rw [←EF.coe_add, ←EF.coe_zero] at Pwd
        rw [EF.coe_le_coe_iff] at Pwd ⊢
        rwa [neg_le_iff_add_nonneg]
    have hQopt : P.dualize.optimum = some (toE r)
    · apply ExtendedLP.optimum_eq_of_reaches_bounded hQr
      intro q hQq
      have Qwd := P.weakDuality hPr hQq
      match q with
      | ⊥ => simp at Qwd
      | ⊤ => apply le_top
      | (_ : F) =>
        rw [←EF.coe_add, ←EF.coe_zero, add_comm] at Qwd
        rw [EF.coe_le_coe_iff] at Qwd ⊢
        rwa [le_add_neg_iff_le] at Qwd
    rewrite [hPopt, hQopt]
    rfl
  else
    have hPopt : P.optimum = some (⊥ : F∞)
    · simp [ExtendedLP.optimum, hP, ExtendedLP.unbounded_of_feasible_of_infeasible hP hQ]
      rfl
    have hQopt : P.dualize.optimum = some (⊤ : F∞)
    · simp [ExtendedLP.optimum, hQ]
      sorry -- WTF ?????????????????????????????????????????????????????????????????????????????
    rw [hPopt, hQopt]
    apply EF.neg_top

theorem ExtendedLP.optimum_neq_none (P : ExtendedLP I J F) : P.optimum ≠ none := by
  if hP : P.IsFeasible then
    intro contr
    simpa [contr, OppositesOpt] using P.strongDuality_of_prim_feas hP
  else
    simp [ExtendedLP.optimum, hP]

lemma ExtendedLP.strongDuality_of_dual_feas {P : ExtendedLP I J F} (hQ : P.dualize.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum := by
  rw [oppositesOpt_comm]
  nth_rw 2 [P.dualize_dualize]
  exact P.dualize.strongDuality_of_prim_feas hQ

theorem ExtendedLP.strongDuality {P : ExtendedLP I J F} (feas : P.IsFeasible ∨ P.dualize.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum :=
  feas.casesOn
    (P.strongDuality_of_prim_feas ·)
    (P.strongDuality_of_dual_feas ·)

end extended_LP_optima

end strong_duality

#print axioms ExtendedLP.strongDuality
