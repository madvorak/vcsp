import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Finset.Pointwise
import VCSP.Basic
import VCSP.ExtendedRationals


section typeclasses

class AlmostOrderedSMul (R M : Type*) [OrderedSemiring R] [OrderedAddCommMonoid M] [SMulZeroClass R M] : Prop where
  /-- Scalar multiplication by nonnegative elements preserves the order. -/
  smul_le_smul_of_le_of_nng : ∀ a b : M, ∀ c : R, a ≤ b → 0 ≤ c → c • a ≤ c • b
  /-- Scalar multiplication by positive elements preserves the strict order. -/
  smul_lt_smul_of_lt_of_pos : ∀ a b : M, ∀ c : R, a < b → 0 < c → c • a < c • b
  /-- And the opposite direction also holds. -/
  lt_of_smul_lt_smul_of_pos : ∀ a b : M, ∀ c : R, c • a < c • b → 0 < c → a < b

end typeclasses


open scoped Matrix
variable {I J : Type} [Fintype I] [Fintype J]


section basicFarkas

lemma easyFarkas {R : Type*} [OrderedCommRing R] (A : Matrix I J R) (b : I → R) :
    (∃ x : J → R, 0 ≤ x ∧ A *ᵥ x ≤ b) ∧ (∃ y : I → R, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) →
      False := by
  intro ⟨⟨x, hx, hAx⟩, ⟨y, hy, hAy, hby⟩⟩
  have hAy' : 0 ≤ y ᵥ* A
  · rwa [Matrix.neg_mulVec, Matrix.mulVec_transpose, neg_nonpos] at hAy
  exfalso
  rw [← lt_self_iff_false (0 : R)]
  calc 0 = 0 ⬝ᵥ x := (Matrix.zero_dotProduct x).symm
    _ ≤ (y ᵥ* A) ⬝ᵥ x := Matrix.dotProduct_le_dotProduct_of_nonneg_right hAy' hx
    _ = y ⬝ᵥ (A *ᵥ x) := (Matrix.dotProduct_mulVec y A x).symm
    _ ≤ y ⬝ᵥ b := Matrix.dotProduct_le_dotProduct_of_nonneg_left hAx hy
    _ = b ⬝ᵥ y := Matrix.dotProduct_comm y b
    _ < 0 := hby

axiom standardFarkas (A : Matrix I J ℚ) (b : I → ℚ) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → ℚ, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0)

example (A : Matrix I J ℚ) (b : I → ℚ) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A *ᵥ x ≤ b) ∧ (∃ y : I → ℚ, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) →
      False := by
  intro ⟨hx, hy⟩
  simpa [hx, hy] using standardFarkas A b

end basicFarkas


section instERat

notation "ℚ∞" => ERat

instance : SMulZeroClass ℚ ℚ∞ where
  smul (c : ℚ) (a : ℚ∞) := c.toERat * a
  smul_zero (c : ℚ) := by
    show (c * 0).toERat = (0 : ℚ∞)
    rewrite [mul_zero]
    rfl

lemma smul_toERat_eq_mul_toERat (c a : ℚ) : c • a.toERat = (c * a).toERat := rfl

lemma zero_smul_ERat_neq_bot {a : ℚ∞} (ha : a ≠ ⊥) : (0 : ℚ) • a = 0 := ERat.zero_mul ha

instance : AlmostOrderedSMul ℚ ℚ∞ where
  smul_le_smul_of_le_of_nng (a b : ℚ∞) (c : ℚ) (hab : a ≤ b) (hc : 0 ≤ c) := by
    match ha : a with
    | ⊤ =>
      match b with
      | ⊤ => rfl
      | ⊥ => exact (hab.trans_lt bot_lt_top).false.elim
      | (_ : ℚ) => simp [top_le_iff] at hab
    | ⊥ =>
      show c.toERat * ⊥ ≤ c.toERat * b
      rw [ERat.coe_mul_bot_of_nng hc]
      apply bot_le
    | (p : ℚ) =>
    match hb : b with
    | ⊤ =>
      show (c * p).toERat ≤ c.toERat * ⊤
      if c_pos : 0 < c then
        rw [ERat.coe_mul_top_of_pos c_pos]
        apply le_top
      else
        rewrite [←eq_of_le_of_not_lt hc c_pos, zero_mul]
        rfl
    | ⊥ =>
      exfalso
      rw [le_bot_iff] at hab
      cases hab
    | (q : ℚ) =>
      show (c * p).toERat ≤ (c * q).toERat
      rw [ERat.coe_le_coe_iff] at hab ⊢
      exact mul_le_mul_of_nonneg_left hab hc
  smul_lt_smul_of_lt_of_pos (a b : ℚ∞) (c : ℚ) (hab : a < b) (hc : 0 < c) := by
    show c.toERat * a < c.toERat * b
    match ha : a with
    | ⊤ =>
      exfalso
      exact not_top_lt hab
    | ⊥ =>
      convert_to ⊥ < c.toERat * b
      · exact ERat.coe_mul_bot_of_nng hc.le
      rw [bot_lt_iff_ne_bot] at hab ⊢
      match b with
      | ⊤ => rwa [ERat.coe_mul_top_of_pos hc]
      | ⊥ => exact False.elim (hab rfl)
      | (_ : ℚ) => tauto
    | (p : ℚ) =>
    match hb : b with
    | ⊤ =>
      convert_to c.toERat * p.toERat < ⊤
      · exact ERat.coe_mul_top_of_pos hc
      rw [lt_top_iff_ne_top] at hab ⊢
      exact ne_of_beq_false rfl
    | ⊥ =>
      exfalso
      exact not_lt_bot hab
    | (q : ℚ) =>
      show (c * p).toERat < (c * q).toERat
      rw [ERat.coe_lt_coe_iff] at hab ⊢
      rwa [mul_lt_mul_left hc]
  lt_of_smul_lt_smul_of_pos (a b : ℚ∞) (c : ℚ) (hab : c • a < c • b) (hc : 0 < c) := by
    match ha : a with
    | ⊤ =>
      exfalso
      change hab to c.toERat * ⊤ < c.toERat * b
      rw [ERat.coe_mul_top_of_pos hc] at hab
      exact not_top_lt hab
    | ⊥ =>
      rw [bot_lt_iff_ne_bot]
      by_contra contr
      rw [contr] at hab
      exact hab.false
    | (p : ℚ) =>
    match hb : b with
    | ⊤ =>
      simp
    | ⊥ =>
      exfalso
      change hab to c.toERat * p.toERat < c.toERat * ⊥
      rw [ERat.coe_mul_bot_of_nng hc.le] at hab
      exact not_lt_bot hab
    | (q : ℚ) =>
      change hab to (c * p).toERat < (c * q).toERat
      rw [ERat.coe_lt_coe_iff] at hab ⊢
      rwa [mul_lt_mul_left hc] at hab

lemma Function.neg_le_zero_ERat (x : J → ℚ∞) : -x ≤ 0 ↔ 0 ≤ x := by
  constructor <;> intro hx i <;> specialize hx i
  · rw [Pi.neg_apply] at hx
    rw [Pi.zero_apply] at *
    match hxi : x i with
    | ⊤ => exact ERat.zero_lt_top.le
    | ⊥ =>
      exfalso
      rw [hxi] at hx
      exact (hx.trans_lt ERat.zero_lt_top).false
    | (q : ℚ) =>
      rw [hxi] at hx
      if hq : 0 ≤ q then
        rwa [←ERat.coe_nonneg] at hq
      else
        exfalso
        have : -q ≤ 0
        · exact ERat.coe_nonpos.mp hx
        rw [neg_le, neg_zero] at this -- TODO refactor
        exact hq this
  · rw [Pi.neg_apply]
    rw [Pi.zero_apply] at *
    match hxi : x i with
    | ⊤ => exact ERat.bot_lt_zero.le
    | ⊥ =>
      exfalso
      rw [hxi] at hx
      exact (hx.trans_lt ERat.bot_lt_zero).false
    | (q : ℚ) =>
      rw [hxi] at hx
      rw [ERat.neg_le, neg_zero]
      exact hx

lemma Finset.sum_toERat {ι : Type*} [Fintype ι] (f : ι → ℚ) (s : Finset ι) :
    (s.sum f).toERat = s.sum (fun i : ι => (f i).toERat) := by
  sorry

end instERat


section heteroMatrixProducts

variable {α γ : Type*}

/-- `Matrix.dotProd v w` is the sum of the element-wise products `w i • v i`
    (mnemonic: "vector times weights"). -/
def Matrix.dotProd [AddCommMonoid α] [SMul γ α] (v : I → α) (w : I → γ) : α :=
  Finset.univ.sum (fun i : I => w i • v i)

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`
   and ` ₘ* ` for `Matrix.mulWeig` (both have precedence of 73)
   so that `a • v ᵥ⬝ c • w` is parsed as `(a • v) ᵥ⬝ (c • w)` and
   that `A ₘ* v ᵥ⬝ w` is parsed as `(A ₘ* v) ᵥ⬝ w` and
   that `v ᵥ⬝ C *ᵥ w` is parsed as `v ᵥ⬝ (C *ᵥ w)` and
   that `v ᵥ⬝ w ᵥ* C` is parsed as `v ᵥ⬝ (w ᵥ* C)` here. -/
infixl:72 " ᵥ⬝ " => Matrix.dotProd

def Matrix.mulWeig [AddCommMonoid α] [SMul γ α] (M : Matrix I J α) (w : J → γ) (i : I) : α :=
  (fun j : J => M i j) ᵥ⬝ w
infixr:73 " ₘ* " => Matrix.mulWeig


lemma Matrix.zero_dotProd [AddCommMonoid α] [SMulZeroClass γ α] (w : I → γ) :
    (0 : I → α) ᵥ⬝ w = (0 : α) := by
  apply Finset.sum_eq_zero
  intro i _
  exact smul_zero (w i)

lemma Matrix.no_bot_dotProd_zero {v : I → ℚ∞} (hv : ∀ i, v i ≠ ⊥) :
    v ᵥ⬝ (0 : I → ℚ) = (0 : ℚ∞) := by
  apply Finset.sum_eq_zero
  intro i _
  rw [Pi.zero_apply]
  match hvi : v i with
  | ⊤ => rfl
  | ⊥ => exact False.elim (hv i hvi)
  | (q : ℚ) =>
    show (0 * q).toERat = (0 : ℚ∞)
    rewrite [zero_mul]
    rfl

lemma Matrix.has_bot_dotProd_nng {v : I → ℚ∞} {i : I} (hvi : v i = ⊥) {w : I → ℚ} (hw : 0 ≤ w) :
    v ᵥ⬝ w = (⊥ : ℚ∞) := by
  sorry

lemma Matrix.no_bot_dotProd_nng {v : I → ℚ∞} (hv : ∀ i, v i ≠ ⊥) {w : I → ℚ} (hw : 0 ≤ w) :
    v ᵥ⬝ w ≠ (⊥ : ℚ∞) := by
  sorry

lemma Matrix.no_bot_has_top_dotProd_le {v : I → ℚ∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    {w : I → ℚ} {q : ℚ} (hq : v ᵥ⬝ w ≤ q.toERat) :
    w i ≤ 0 := by
  -- ERat.top_mul_coe_of_pos
  sorry

lemma Matrix.no_bot_has_top_dotProd_nng_le {v : I → ℚ∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    {w : I → ℚ} (hw : 0 ≤ w) {q : ℚ} (hq : v ᵥ⬝ w ≤ q.toERat) :
    w i = 0 :=
  le_antisymm (Matrix.no_bot_has_top_dotProd_le hv hvi hq) (hw i)

lemma Matrix.dotProd_zero_le_zero (v : I → ℚ∞) :
    v ᵥ⬝ (0 : I → ℚ) ≤ (0 : ℚ∞) := by
  if hv : ∀ i, v i ≠ ⊥ then
    rw [Matrix.no_bot_dotProd_zero hv]
  else
    push_neg at hv
    rw [Matrix.has_bot_dotProd_nng]
    · apply bot_le
    · exact hv.choose_spec
    · rfl

lemma Matrix.dotProd_le_dotProd_of_nng_right [OrderedAddCommMonoid α] [OrderedSemiring γ] [SMulZeroClass γ α] [AlmostOrderedSMul γ α]
    {u v : J → α} (huv : u ≤ v) {w : J → γ} (hw : 0 ≤ w) :
    u ᵥ⬝ w ≤ v ᵥ⬝ w := by
  apply Finset.sum_le_sum
  intro i _
  apply AlmostOrderedSMul.smul_le_smul_of_le_of_nng
  · exact huv i
  · exact hw i

lemma Matrix.no_bot_mulWeig_zero {A : Matrix I J ℚ∞} (hA : ∀ i, ∀ j, A i j ≠ ⊥) :
    A ₘ* (0 : J → ℚ) = (0 : I → ℚ∞) := by
  ext
  apply Matrix.no_bot_dotProd_zero
  apply hA

lemma Matrix.mulWeig_zero_le_zero (A : Matrix I J ℚ∞) :
    A ₘ* (0 : J → ℚ) ≤ (0 : I → ℚ∞) := by
  intro i
  apply Matrix.dotProd_zero_le_zero

-- notation test

variable (v : Fin 3 → ℚ∞) (w : Fin 3 → ℚ) (a : ℚ∞) (c : ℚ)
  (A : Matrix (Fin 3) (Fin 3) ℚ∞) (C : Matrix (Fin 3) (Fin 3) ℚ)

example : a • v ᵥ⬝ c • w = (a • v) ᵥ⬝ (c • w) := rfl
example : v ᵥ⬝ C ₘ* w = v ᵥ⬝ (C ₘ* w) := rfl
example : v ᵥ⬝ w ᵥ* C = v ᵥ⬝ (w ᵥ* C) := rfl
example : v ᵥ⬝ C *ᵥ w = v ᵥ⬝ (C *ᵥ w) := rfl
example : A ₘ* v ᵥ⬝ w = (A ₘ* v) ᵥ⬝ w := rfl

end heteroMatrixProducts


section generalizedFarkas

def Matrix.Good (A : Matrix I J ℚ∞) : Prop :=
  ¬ (∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤))

def Matrix.Good' (A : Matrix I J ℚ∞) (b : I → ℚ∞) : Prop :=
  ¬ (∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥)

def Matrix.Good'' (A : Matrix I J ℚ∞) (b : I → ℚ∞) : Prop :=
  ¬ (∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤)

set_option maxHeartbeats 777777 in
theorem extendedFarkas {A : Matrix I J ℚ∞} {b : I → ℚ∞}
    (hA : A.Good) (hAT : Aᵀ.Good) (hAb' : A.Good' b) (hAb : A.Good'' b) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A ₘ* x ≤ b) ≠ (∃ y : I → ℚ, 0 ≤ y ∧ -Aᵀ ₘ* y ≤ 0 ∧ b ᵥ⬝ y < 0) := by
  -- filter rows and columns
  let I' : Type := { i : I // b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥ } -- non-tautological rows
  let J' : Type := { j : J // ∀ i' : I', A i'.val j ≠ ⊤ } -- columns that allow non-zero values
  let A' : Matrix I' J' ℚ := -- the new matrix
    Matrix.of (fun i' : I' => fun j' : J' =>
      match matcha : A i'.val j'.val with
      | (q : ℚ) => q
      | ⊥ => False.elim (i'.property.right j' matcha)
      | ⊤ => False.elim (j'.property i' matcha)
    )
  if hbot : ∃ i : I, b i = ⊥ then
    obtain ⟨i, hi⟩ := hbot
    if hi' : (∀ j : J, A i j ≠ ⊥) then
      convert false_ne_true
      · rw [iff_false, not_exists]
        intro x ⟨hx, hAxb⟩
        specialize hAxb i
        rw [hi, le_bot_iff] at hAxb
        refine Matrix.no_bot_dotProd_nng hi' hx hAxb
      · rw [iff_true]
        use 0
        constructor
        · rfl
        constructor
        · apply Matrix.mulWeig_zero_le_zero
        · rw [Matrix.has_bot_dotProd_nng hi (by rfl)]
          exact ERat.bot_lt_zero
    else
      push_neg at hi'
      exfalso
      apply hAb'
      exact ⟨i, hi', hi⟩
  else
    let b' : I' → ℚ := -- the new RHS
      fun i' : I' =>
        match hbi : b i'.val with
        | (q : ℚ) => q
        | ⊥ => False.elim (hbot ⟨i', hbi⟩)
        | ⊤ => False.elim (i'.property.left hbi)
    let J'' : Type := { j : J // ∀ i : I, A i j ≠ ⊤ } -- non-tautological columns
    let I'' : Type := { i : I // b i ≠ ⊤ ∧ ∀ j'' : J'', A i j''.val ≠ ⊥ } -- rows that allow non-zero values
    have hI (i : I) : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) ↔ (b i ≠ ⊤ ∧ ∀ j'' : J'', A i j''.val ≠ ⊥)
    · constructor <;> intro ⟨bi_neq_top, hi⟩
      · exact ⟨bi_neq_top, fun j'' : J'' => hi j''.val⟩
      · constructor
        · exact bi_neq_top
        · intro j
          if hI'' : (∀ i : I, A i j ≠ ⊤) then
            exact hi ⟨j, hI''⟩
          else
            push_neg at hI''
            intro Aij_neq_bot
            exact hAT ⟨j, ⟨i, Aij_neq_bot⟩, hI''⟩
    have hJ (j : J) : (∀ i' : I', A i'.val j ≠ ⊤) ↔ (∀ i : I, A i j ≠ ⊤)
    · constructor <;> intro hj
      · intro i Aij_eq_top
        if bi_top : b i = ⊤ then
          exact hAb ⟨i, ⟨j, Aij_eq_top⟩, bi_top⟩
        else if Ai_bot : (∃ j : J, A i j = ⊥) then
          exact hA ⟨i, Ai_bot, ⟨j, Aij_eq_top⟩⟩
        else
          push_neg at Ai_bot
          exact hj ⟨i, ⟨bi_top, Ai_bot⟩⟩ Aij_eq_top
      · intro i'
        exact hj i'.val
    let A'' : Matrix I'' J'' ℚ := -- matrix for simpler `y` part
      Matrix.of (fun i'' : I'' => fun j'' : J'' =>
        match matcha : A i''.val j''.val with
        | (q : ℚ) => q
        | ⊥ => False.elim (i''.property.right j'' matcha)
        | ⊤ => False.elim (j''.property i'' matcha)
      )
    let b'' : I'' → ℚ := -- the new RHS
      fun i'' : I'' =>
        match hbi : b i''.val with
        | (q : ℚ) => q
        | ⊥ => False.elim (hbot ⟨i''.val, hbi⟩)
        | ⊤ => False.elim (i''.property.left hbi)
    convert standardFarkas A'' b''
    · sorry
    /-convert standardFarkas A' b'
    · constructor <;> intro ⟨x, hx, ineqalities⟩
      · use (fun j' : J' => x j'.val)
        constructor
        · intro j'
          exact hx j'.val
        intro i'
        rw [← ERat.coe_le_coe_iff]
        convert ineqalities i'.val; swap
        · simp only [b']
          split <;> rename_i hbi <;> simp only [hbi]
          · rfl
          · exfalso
            apply hbot
            use i'
            exact hbi
          · exfalso
            apply i'.property.left
            exact hbi
        simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.mulWeig, Matrix.dotProd]
        rw [Finset.sum_toERat]
        show
          Finset.univ.sum (fun j' : J' => (A' i' j' * x j'.val).toERat) =
          Finset.univ.sum (fun j : J => (x j).toERat * A i'.val j)
        rw [Finset.univ_sum_of_zero_when_neg (fun j : J => ∀ i' : I', A i'.val j ≠ ⊤)]
        · congr
          ext j'
          rw [mul_comm]
          simp only [A', Matrix.of_apply, ERat.coe_mul]
          congr
          split <;> rename_i hAij <;> simp only [hAij]
          · rfl
          · exfalso
            apply i'.property.right
            exact hAij
          · exfalso
            apply j'.property
            exact hAij
        · intro j where_top
          push_neg at where_top
          obtain ⟨t, ht⟩ := where_top
          have hxj : x j = 0
          · obtain ⟨q, hq⟩ : ∃ q : ℚ, b t = q.toERat
            · match hbt : b t.val with
              | (q : ℚ) =>
                exact ⟨_, rfl⟩
              | ⊥ =>
                exfalso
                apply hbot
                use t
                exact hbt
              | ⊤ =>
                exfalso
                apply t.property.left
                exact hbt
            exact Matrix.no_bot_has_top_dotProd_nng_le (t.property.right) ht hx (hq ▸ ineqalities t.val)
          rw [hxj]
          apply ERat.zero_mul
          apply i'.property.right
      · use (fun j : J => if hj : (∀ i' : I', A i'.val j ≠ ⊤) then x ⟨j, hj⟩ else 0)
        constructor
        · intro j
          if hj : (∀ i' : I', A i'.val j ≠ ⊤) then
            convert hx ⟨j, hj⟩
            simp [hj]
          else
            aesop
        intro i
        if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then
          convert ERat.coe_le_coe_iff.mpr (ineqalities ⟨i, hi⟩)
          · unfold Matrix.mulVec Matrix.dotProduct Matrix.mulWeig Matrix.dotProd
            simp_rw [dite_smul]
            rw [Finset.sum_dite]
            convert add_zero _
            · apply Finset.sum_eq_zero
              intro j _
              apply zero_smul_ERat_neq_bot
              exact hi.right j.val
            · rw [←Finset.sum_coe_sort_eq_attach, Finset.sum_toERat]
              apply Finset.subtype_univ_sum_eq_subtype_univ_sum
              · simp [Finset.mem_filter]
              · intros
                rw [mul_comm, ERat.coe_mul]
                simp only [A', Matrix.of_apply]
                split <;> rename_i hAij <;> simp only [hAij]
                · rfl
                · exfalso
                  apply hi.right
                  exact hAij
                · exfalso
                  aesop
          · simp only [b']
            split <;> rename_i hbi <;> simp only [hbi]
            · rfl
            · exfalso
              apply hbot
              use ⟨i, hi⟩
              exact hbi
            · exfalso
              apply hi.left
              exact hbi
        else
          push_neg at hi
          if hbi : b i = ⊤ then
            rw [hbi]
            apply le_top
          else
            obtain ⟨j, hAij⟩ := hi hbi
            convert_to ⊥ ≤ b i
            · apply Matrix.has_bot_dotProd_nng hAij
              intro _
              aesop
            apply bot_le-/
    · constructor <;> intro ⟨y, hy, ineqalities, sharpine⟩
      · use (fun i'' : I'' => y i''.val)
        constructor
        · intro i''
          exact hy i''.val
        constructor
        · intro ⟨j, hj⟩
          rw [←ERat.coe_le_coe_iff]
          convert ineqalities j
          simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.mulWeig, Matrix.dotProd]
          rw [Finset.sum_toERat]
          show
            Finset.univ.sum (fun i'' : I'' => ((-A''ᵀ) ⟨j, hj⟩ i'' * y i''.val).toERat) =
            Finset.univ.sum (fun i : I => y i • (-Aᵀ) j i)
          rw [Finset.univ_sum_of_zero_when_neg (fun i : I => b i ≠ ⊤ ∧ ∀ j'' : J'', A i j''.val ≠ ⊥)]
          · congr
            ext i''
            rw [mul_comm]
            simp only [A'', Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply, ERat.coe_neg]
            congr
            split <;> rename_i q hAij <;> simp only [hAij]
            · rfl
            · exfalso
              exact i''.property.right ⟨j, hj⟩ hAij
            · exfalso
              apply hj
              exact hAij
          · intro i todo
            have hyi : y i = 0
            · sorry
            rw [hyi]
            apply ERat.zero_mul
            simp only [Matrix.neg_apply, Matrix.transpose_apply, ne_eq, ERat.neg_eq_bot_iff]
            apply hj
        · rw [←ERat.coe_lt_coe_iff]
          convert sharpine
          simp only [Matrix.dotProduct, Matrix.dotProd]
          rw [Finset.sum_toERat]
          rw [Finset.univ_sum_of_zero_when_neg (fun i : I => b i ≠ ⊤ ∧ ∀ j'' : J'', A i j''.val ≠ ⊥)]
          · congr
            ext i''
            simp [b'']
            split <;> rename_i q hbi <;> simp only [hbi]
            · sorry -- rw [mul_comm]
            · exfalso
              exact hbot ⟨i''.val, hbi⟩
            · exfalso
              exact i''.property.left hbi
          · intro i todo
            have hyi : y i = 0
            · sorry
            rw [hyi]
            apply ERat.zero_mul
            simp only [Matrix.neg_apply, Matrix.transpose_apply, ne_eq, ERat.neg_eq_bot_iff]
            intro bi_eq_bot
            exact hbot ⟨i, bi_eq_bot⟩
      · use (fun i : I => if hi : (b i ≠ ⊤ ∧ ∀ j'' : J'', A i j'' ≠ ⊥) then y ⟨i, hi⟩ else 0)
        constructor
        · intro i
          if hi : (b i ≠ ⊤ ∧ ∀ j'' : J'', A i j'' ≠ ⊥) then
            convert hy ⟨i, hi⟩
            simp [hi]
          else
            sorry --aesop
        constructor
        · sorry
        · sorry

end generalizedFarkas
