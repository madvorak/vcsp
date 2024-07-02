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
  /-- No `⊤` in the right-hand-side vector. -/
  hbi : ¬∃ i : I, b i = ⊤
  /-- No `⊥` in the objective function coefficients. -/
  hcj : ¬∃ j : J, c j = ⊥
  /-- No `⊥` in the row where the right-hand-side vector has `⊥`. -/
  hAb : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥
  /-- No `⊤` in the column where the objective function has `⊤`. -/
  hAc : ¬∃ j : J, (∃ i : I, A i j = ⊤) ∧ c j = ⊤

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution (P : ExtendedLP I J) (x : J → ℚ) : Prop :=
  P.A ₘ* x ≤ P.b ∧ 0 ≤ x -- Do not refactor to `x : J → ℚ≥0` even tho it would look nicer here!

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

open scoped Classical in
/-- Extended notion of "optimum" of "maximization" LP. -/
noncomputable def ExtendedLP.optimum (P : ExtendedLP I J) : Option ℚ∞ :=
  if P.IsFeasible then
    if ∃ u : ℚ, P.IsBoundedBy u.toERat then
      if hr : ∃ r : ℚ, P.Reaches r.toERat ∧ P.IsBoundedBy r.toERat then
        some $ some $ some $ hr.choose -- the "maximum"
      else
        none -- invalid finite value (supremum is not attained; later, we prove it cannot happen)
    else
      some ⊤ -- unbounded
  else
    some ⊥ -- infeasible

lemma ExtendedLP.optimum_unique {P : ExtendedLP I J} {r s : ℚ}
    (hPr : P.Reaches r.toERat ∧ P.IsBoundedBy r.toERat) (hPs : P.Reaches s.toERat ∧ P.IsBoundedBy s.toERat) :
    r = s := by
  apply eq_of_le_of_le <;> rw [←ERat.coe_le_coe_iff]
  · apply hPs.right
    exact hPr.left
  · apply hPr.right
    exact hPs.left

lemma Matrix.dotProd_eq_bot {v : J → ℚ∞} {w : J → ℚ} (hw : 0 ≤ w) (hvw : v ᵥ⬝ w = ⊥) :
    ∃ j : J, v j = ⊥ := by
  by_contra! contr
  exact Matrix.no_bot_dotProd_nneg contr hw hvw

lemma ExtendedLP.cannot_reach_bot {P : ExtendedLP I J} (hP : P.Reaches ⊥) : False := by
  obtain ⟨p, ⟨-, hp⟩, contr⟩ := hP
  exact P.hcj (Matrix.dotProd_eq_bot hp contr)

lemma ExtendedLP.optimum_eq_of_reaches_bounded {P : ExtendedLP I J} {r : ℚ∞}
    (reaches : P.Reaches r) (bounded : P.IsBoundedBy r) :
    P.optimum = some r := by
  have hP : P.IsFeasible
  · obtain ⟨x, hx, -⟩ := reaches
    exact ⟨x, hx⟩
  match r with
  | ⊥ =>
    exfalso
    exact P.cannot_reach_bot reaches
  | ⊤ =>
    simp [ExtendedLP.optimum, hP]
    intro p hp
    exfalso
    simpa using hp ⊤ reaches
  | (p : ℚ) =>
    have hPu : ∃ u : ℚ, P.IsBoundedBy u.toERat
    · use p
    have hPP : ∃ r : ℚ, P.Reaches r.toERat ∧ P.IsBoundedBy r.toERat
    · use p
    simp [ExtendedLP.optimum, hP, hPu, hPP]
    congr
    exact ExtendedLP.optimum_unique hPP.choose_spec ⟨reaches, bounded⟩

/-- `Opposites p q` essentially says `p ≠ none ∧ q ≠ none ∧ p = -q`. -/
def Opposites : Option ℚ∞ → Option ℚ∞ → Prop
| (p : ℚ∞), (q : ℚ∞) => p = -q  -- includes `⊥ = -⊤` and `⊤ = -⊥`
| _       , _        => False   -- namely `none ≠ -none`

lemma opposites_of_neg_eq {r s : ℚ∞} (hrs : -r = s) : Opposites (some r) (some s) := by
  rwa [neg_eq_iff_eq_neg] at hrs

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

/-- Note that `ExtendedLP.dualize` is significantly different from `StandardLP.dualize`;
    here we keep maximizing in the dual problem but the sign is flipped;
    as a result, `ExtendedLP.dualize` is involution (good),
    but the strong LP duality can no longer be written as equality (bad);
    also, assumptions are bundled into the definition here. -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨ -P.Aᵀ
  , -P.c
  , -P.b
  , by
      intro ⟨j, hbot, htop⟩
      apply P.hAj
      use j
      constructor
      · convert htop using 2
        simp
      · convert hbot using 2
        simp
  , by
      intro ⟨i, hbot, htop⟩
      apply P.hAi
      use i
      constructor
      · convert htop using 2
        simp
      · convert hbot using 2
        simp
  , by
      intro ⟨j, hj⟩
      apply P.hcj
      use j
      simpa using hj
  , by
      intro ⟨i, hi⟩
      apply P.hbi
      use i
      simpa using hi
  , by
      intro ⟨j, hAj, hcj⟩
      apply P.hAc
      use j
      constructor
      · convert hAj using 2
        simp
      · simpa using hcj
  , by
      intro ⟨i, hAi, hbi⟩
      apply P.hAb
      use i
      constructor
      · convert hAi using 2
        simp
      · simpa using hbi
  ⟩

lemma ExtendedLP.dualize_dualize (P : ExtendedLP I J) : P.dualize.dualize = P := by
  obtain ⟨_, _, _⟩ := P
  simp [ExtendedLP.dualize, ←Matrix.ext_iff]

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
  --rw [eq_neg_iff_add_eq_zero]
  --rw [←Finset.sum_neg_distrib]
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

theorem ExtendedLP.weakDuality {P : ExtendedLP I J} {p : ℚ∞} (hP : P.Reaches p) {q : ℚ∞} (hQ : P.dualize.Reaches q) :
    p ≤ -q := by
  obtain ⟨x, ⟨hxb, h0x⟩, rfl⟩ := hP
  obtain ⟨y, ⟨hyc, h0y⟩, rfl⟩ := hQ
  have hyxx : -P.Aᵀ ₘ* y ᵥ⬝ x ≤ -P.c ᵥ⬝ x := Matrix.dotProd_le_dotProd_of_nneg_right hyc h0x
  rw [Matrix.neg_mulWeig, Matrix.neg_dotProd, Matrix.neg_dotProd, ERat.neg_le_neg_iff, Matrix.transpose_mulWeig_dotProd] at hyxx
  convert hyxx.trans (Matrix.dotProd_le_dotProd_of_nneg_right hxb h0y)
  convert neg_neg (P.b ᵥ⬝ y)
  exact Matrix.neg_dotProd P.b y

lemma unbounded_of_todo {P : ExtendedLP I J} (hP : P.IsFeasible) (hQ : ¬P.dualize.IsFeasible) {p : ℚ} -- WTF ???
    (hp : P.IsBoundedBy p.toERat) : False := by
  obtain ⟨x, hx⟩ := hP
  have hP' : P.Reaches (P.c ᵥ⬝ x)
  · use x
  match hp' : P.c ᵥ⬝ x with
  | ⊥ =>
    rw [hp'] at hP'
    exact ExtendedLP.cannot_reach_bot hP'
  | ⊤ =>
    sorry
  | (p' : ℚ) =>
    rw [hp'] at hP'
    specialize hp p' hP'
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

lemma ExtendedLP.strongDuality_of_both_feas {P : ExtendedLP I J}
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    Opposites P.optimum P.dualize.optimum := by
  cases
    or_of_neq
      (extendedFarkas
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.ro1 (Sum.elim (-P.c) P.b)))
        (Sum.elim (Sum.elim P.b (-P.c)) 0)
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              rw [Matrix.fromRows_apply_inl] at hks hkt
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
              rw [Matrix.fromRows_apply_inl] at hks hkt
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
          | inr =>
            rw [Matrix.fromRows_apply_inr] at hks hkt
            simp only [Matrix.row_apply] at hks hkt
            cases t with
            | inl jₜ =>
              rw [Sum.elim_inl, Pi.neg_apply, ERat.neg_eq_top_iff] at hkt
              apply P.hcj
              use jₜ
            | inr iₜ =>
              rw [Sum.elim_inr] at hkt
              apply P.hbi
              use iₜ
        )
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl j =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ =>
                rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₁₁] at hks
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ =>
                    rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₁₁] at hkt
                    exact P.hAj ⟨j, ⟨⟨iₛ, hks⟩, ⟨iₜ, hkt⟩⟩⟩
                  | inr jₜ =>
                    simp at hkt
                | inr =>
                  apply P.hcj
                  use j
                  simpa using hkt
              | inr jₛ =>
                rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₂₁] at hks
                simp at hks
            | inr =>
              cases t with
              | inl t' =>
                cases t' with
                | inl iₜ =>
                  rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₁₁] at hkt
                  exact P.hAc ⟨j, ⟨⟨iₜ, hkt⟩, by simpa using hks⟩⟩
                | inr jₜ =>
                  simp at hkt
              | inr =>
                apply P.hcj
                use j
                simpa using hkt
          | inr i =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ =>
                rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₁₂] at hks
                simp at hks
              | inr jₛ =>
                rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₂₂] at hks
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ =>
                    rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₁₂] at hkt
                    simp at hkt
                  | inr jₜ =>
                    rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₂₂] at hkt
                    apply P.hAi
                    use i
                    constructor
                    · use jₜ
                      simpa using hkt
                    · use jₛ
                      simpa using hks
                | inr =>
                  apply P.hbi
                  use i
                  simpa using hkt
            | inr =>
              rw [Matrix.fromRows_apply_inr] at hks
              cases t with
              | inl t' =>
                cases t' with
                | inl iₜ =>
                  rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₁₂] at hkt
                  simp at hkt
                | inr jₜ =>
                  rw [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₂₂] at hkt
                  exact P.hAb ⟨i, ⟨jₜ, by simpa using hkt⟩, hks⟩
              | inr =>
                apply P.hbi
                use i
                simpa using hkt
        )
        (by
          intro ⟨k, ⟨t, hkt⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i => exact P.hbi ⟨i, hk⟩
            | inr j => exact P.hcj ⟨j, by simpa using hk⟩
          | inr => simp at hk
        )
        (by
          intro ⟨k, ⟨s, hks⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ => exact P.hAb ⟨i, ⟨⟨jₛ, by simpa using hks⟩, hk⟩⟩
              | inr iₛ => simp at hks
            | inr j =>
              cases s with
              | inl jₛ => simp at hks
              | inr iₛ => exact P.hAc ⟨j, ⟨⟨iₛ, by simpa using hks⟩, by simpa using hk⟩⟩
          | inr => simp at hk
        )
      ) with
  | inl case_x =>
    obtain ⟨x, hx, hAx⟩ := case_x
    rw [
      Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
      ←Sum.elim_comp_inl_inr x, Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add
    ] at hAx
    have hPx : P.Reaches (P.c ᵥ⬝ x ∘ Sum.inl)
    · exact ⟨x ∘ Sum.inl, ⟨hAx.left.left, nneg_comp hx Sum.inl⟩, rfl⟩
    have hQx : P.dualize.Reaches (-(P.b ᵥ⬝ x ∘ Sum.inr))
    · exact ⟨x ∘ Sum.inr, ⟨hAx.left.right, nneg_comp hx Sum.inr⟩, Matrix.neg_dotProd P.b (x ∘ Sum.inr)⟩
    have equal_neg : P.c ᵥ⬝ x ∘ Sum.inl = -(-(P.b ᵥ⬝ x ∘ Sum.inr))
    · apply eq_of_le_of_le
      · exact ExtendedLP.weakDuality hPx hQx
      · have main_ineq : Sum.elim (-P.c) P.b ᵥ⬝ x ≤ 0
        · simpa using hAx.right 0
        rw [neg_neg]
        rwa [Matrix.sumElim_dotProd, Matrix.neg_dotProd, add_comm, ERat.sub_nonpos_iff'] at main_ineq
    have hPopt : P.optimum = some (P.c ᵥ⬝ x ∘ Sum.inl)
    · apply ExtendedLP.optimum_eq_of_reaches_bounded hPx
      intro r hr
      rw [equal_neg]
      exact P.weakDuality hr hQx
    have hQopt : P.dualize.optimum = some (-(P.b ᵥ⬝ x ∘ Sum.inr))
    · apply ExtendedLP.optimum_eq_of_reaches_bounded hQx
      intro r hr
      apply ExtendedLP.weakDuality hr
      rw [neg_neg] at equal_neg
      rw [ExtendedLP.dualize_dualize, ←equal_neg]
      exact hPx
    rw [hPopt, hQopt]
    exact equal_neg
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
    have hcb : Matrix.col (Fin 1) (Sum.elim (-P.c) P.b) ₘ* y ∘ Sum.inr = -(Sum.elim (y (Sum.inr 0) • P.c) (y (Sum.inr 0) • -P.b))
    · ext k
      cases k <;> simp [Matrix.mulWeig, Matrix.dotProd, mul_comm, ERat.pos_smul_neg y_last_pos]
    rw [
      ←Sum.elim_comp_inl_inr y, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.fromBlocks_neg, Matrix.ERat_neg_neg, Matrix.ERat_neg_zero, Matrix.ERat_neg_zero, Matrix.neg_mulWeig,
      ←Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulWeig,
      ←Sum.elim_comp_inl_inr (y ∘ Sum.inl), Matrix.fromColumns_mulWeig_sumElim, Matrix.fromColumns_mulWeig_sumElim,
      Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add,
      hcb, neg_neg, ←Sum.elim_add_add, Sum.elim_nonpos_iff
    ] at hAy
    obtain ⟨hAyb, hAyc⟩ := hAy
    rw [Matrix.neg_mulWeig, add_comm, ERat.vec_sub_nonpos_iff'] at hAyb
    rw [
      ←Sum.elim_comp_inl_inr y, ←Sum.elim_comp_inl_inr (y ∘ Sum.inl),
      Matrix.sumElim_dotProd_sumElim, Matrix.zero_dotProd, add_zero, Matrix.sumElim_dotProd_sumElim,
      Matrix.neg_dotProd, ERat.add_neg_lt_zero_iff
    ] at hbcy
    swap
    · right
      apply Matrix.no_bot_dotProd_nneg
      · intro j contr
        exact P.hcj ⟨j, contr⟩
      · apply nneg_comp hy
    swap
    · left
      apply Matrix.no_top_dotProd_nneg
      · intro i contr
        exact P.hbi ⟨i, contr⟩
      · apply nneg_comp hy
    have hbcy' : (y (Sum.inr 0) • P.b) ᵥ⬝ (y ∘ Sum.inl) ∘ Sum.inl < (y (Sum.inr 0) • P.c) ᵥ⬝ (y ∘ Sum.inl) ∘ Sum.inr
    · rw [←ERat.smul_lt_smul_left y_last_pos] at hbcy
      convert hbcy <;> simp [Matrix.ERat_smul_dotProd]
    have hAyb' : y (Sum.inr 0) • P.c ᵥ⬝ (y ∘ Sum.inl) ∘ Sum.inr ≤ P.Aᵀ ₘ* (y ∘ Sum.inl) ∘ Sum.inl ᵥ⬝ (y ∘ Sum.inl) ∘ Sum.inr
    · exact Matrix.dotProd_le_dotProd_of_nneg_right hAyb (nneg_comp hy _)
    have hAyc' : P.A ₘ* (y ∘ Sum.inl) ∘ Sum.inr ᵥ⬝ (y ∘ Sum.inl) ∘ Sum.inl ≤ y (Sum.inr 0) • P.b ᵥ⬝ (y ∘ Sum.inl) ∘ Sum.inl
    · rw [ERat.pos_smul_neg_vec y_last_pos, ERat.vec_sub_nonpos_iff'] at hAyc
      exact Matrix.dotProd_le_dotProd_of_nneg_right hAyc (nneg_comp hy _)
    rw [Matrix.transpose_mulWeig_dotProd] at hAyb'
    exact ((hbcy'.trans_le hAyb').trans_le hAyc').false

theorem ExtendedLP.strongDuality_of_prim_feas {P : ExtendedLP I J} (hP : P.IsFeasible) :
    Opposites P.optimum P.dualize.optimum := by
  if hQ : P.dualize.IsFeasible then
    exact P.strongDuality_of_both_feas hP hQ
  else
    have hPopt : P.optimum = some ⊤
    · simp [ExtendedLP.optimum, hP]
      intro p hp
      exfalso
      exact unbounded_of_todo hP hQ hp
    have hQopt : P.dualize.optimum = some ⊥
    · simp [ExtendedLP.optimum, hQ]
    rw [hPopt, hQopt]
    exact ERat.neg_bot.symm

theorem ExtendedLP.strongDuality_of_dual_feas {P : ExtendedLP I J} (hQ : P.dualize.IsFeasible) :
    Opposites P.optimum P.dualize.optimum := by
  have result := P.dualize_dualize ▸ P.dualize.strongDuality_of_prim_feas hQ
  rwa [opposites_comm]

theorem ExtendedLP.strongDuality {P : ExtendedLP I J} (hP : P.IsFeasible ∨ P.dualize.IsFeasible) :
    Opposites P.optimum P.dualize.optimum :=
  hP.casesOn
    (fun primFeas => P.strongDuality_of_prim_feas primFeas)
    (fun dualFeas => P.strongDuality_of_dual_feas dualFeas)
