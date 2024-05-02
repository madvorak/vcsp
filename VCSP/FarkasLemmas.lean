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
variable {n m : Type} [Fintype n] [Fintype m]


section basicFarkas

lemma easyFarkas {R : Type*} [OrderedCommRing R] (A : Matrix m n R) (b : m → R) :
    (∃ x : n → R, 0 ≤ x ∧ A *ᵥ x ≤ b) ∧ (∃ y : m → R, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) →
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

axiom standardFarkas (A : Matrix m n ℚ) (b : m → ℚ) :
    (∃ x : n → ℚ, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : m → ℚ, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0)

example (A : Matrix m n ℚ) (b : m → ℚ) :
    (∃ x : n → ℚ, 0 ≤ x ∧ A *ᵥ x ≤ b) ∧ (∃ y : m → ℚ, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) →
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

lemma Function.neg_le_zero_ERat (x : n → ℚ∞) : -x ≤ 0 ↔ 0 ≤ x := by
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
def Matrix.dotProd [AddCommMonoid α] [SMul γ α] (v : m → α) (w : m → γ) : α :=
  Finset.univ.sum (fun i : m => w i • v i)

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`
   and ` ₘ* ` for `Matrix.mulWeig` (both have precedence of 73)
   so that `a • v ᵥ⬝ c • w` is parsed as `(a • v) ᵥ⬝ (c • w)` and
   that `A ₘ* v ᵥ⬝ w` is parsed as `(A ₘ* v) ᵥ⬝ w` and
   that `v ᵥ⬝ C *ᵥ w` is parsed as `v ᵥ⬝ (C *ᵥ w)` and
   that `v ᵥ⬝ w ᵥ* C` is parsed as `v ᵥ⬝ (w ᵥ* C)` here. -/
infixl:72 " ᵥ⬝ " => Matrix.dotProd

def Matrix.mulWeig [AddCommMonoid α] [SMul γ α] (M : Matrix m n α) (w : n → γ) (i : m) : α :=
  (fun j : n => M i j) ᵥ⬝ w
infixr:73 " ₘ* " => Matrix.mulWeig


lemma Matrix.zero_dotProd [AddCommMonoid α] [SMulZeroClass γ α] (w : m → γ) :
    (0 : m → α) ᵥ⬝ w = (0 : α) := by
  apply Finset.sum_eq_zero
  intro i _
  exact smul_zero (w i)

lemma Matrix.no_bot_dotProd_zero {v : m → ℚ∞} (hv : ∀ i, v i ≠ ⊥) :
    v ᵥ⬝ (0 : m → ℚ) = (0 : ℚ∞) := by
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

lemma Matrix.has_bot_dotProd_nng {v : m → ℚ∞} {i : m} (hvi : v i = ⊥) {w : m → ℚ} (hw : 0 ≤ w) :
    v ᵥ⬝ w = (⊥ : ℚ∞) := by
  sorry

lemma Matrix.no_bot_dotProd_nng {v : m → ℚ∞} (hv : ∀ i, v i ≠ ⊥) {w : m → ℚ} (hw : 0 ≤ w) :
    v ᵥ⬝ w ≠ (⊥ : ℚ∞) := by
  sorry

lemma Matrix.no_bot_has_top_dotProd_le {v : m → ℚ∞} (hv : ∀ a, v a ≠ ⊥) {i : m} (hvi : v i = ⊤)
    {w : m → ℚ} {q : ℚ} (hq : v ᵥ⬝ w ≤ q.toERat) :
    w i ≤ 0 := by
  -- ERat.top_mul_coe_of_pos
  sorry

lemma Matrix.no_bot_has_top_dotProd_nng_le {v : m → ℚ∞} (hv : ∀ a, v a ≠ ⊥) {i : m} (hvi : v i = ⊤)
    {w : m → ℚ} (hw : 0 ≤ w) {q : ℚ} (hq : v ᵥ⬝ w ≤ q.toERat) :
    w i = 0 :=
  le_antisymm (Matrix.no_bot_has_top_dotProd_le hv hvi hq) (hw i)

lemma Matrix.dotProd_zero_le_zero (v : m → ℚ∞) :
    v ᵥ⬝ (0 : m → ℚ) ≤ (0 : ℚ∞) := by
  if hv : ∀ i, v i ≠ ⊥ then
    rw [Matrix.no_bot_dotProd_zero hv]
  else
    push_neg at hv
    rw [Matrix.has_bot_dotProd_nng]
    · apply bot_le
    · exact hv.choose_spec
    · rfl

lemma Matrix.dotProd_le_dotProd_of_nng_right [OrderedAddCommMonoid α] [OrderedSemiring γ] [SMulZeroClass γ α] [AlmostOrderedSMul γ α]
    {u v : n → α} (huv : u ≤ v) {w : n → γ} (hw : 0 ≤ w) :
    u ᵥ⬝ w ≤ v ᵥ⬝ w := by
  apply Finset.sum_le_sum
  intro i _
  apply AlmostOrderedSMul.smul_le_smul_of_le_of_nng
  · exact huv i
  · exact hw i

lemma Matrix.no_bot_mulWeig_zero {A : Matrix m n ℚ∞} (hA : ∀ i, ∀ j, A i j ≠ ⊥) :
    A ₘ* (0 : n → ℚ) = (0 : m → ℚ∞) := by
  ext
  apply Matrix.no_bot_dotProd_zero
  apply hA

lemma Matrix.mulWeig_zero_le_zero (A : Matrix m n ℚ∞) :
    A ₘ* (0 : n → ℚ) ≤ (0 : m → ℚ∞) := by
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

def Matrix.Good (A : Matrix m n ℚ∞) : Prop :=
  ¬ (∃ i : m, (∃ j : n, A i j = ⊥) ∧ (∃ j : n, A i j = ⊤))

def Matrix.Good' (A : Matrix m n ℚ∞) (b : m → ℚ∞) : Prop :=
  ¬ (∃ i : m, (∃ j : n, A i j = ⊥) ∧ b i = ⊥)

set_option maxHeartbeats 666666 in
theorem extendedFarkas {A : Matrix m n ℚ∞} {b : m → ℚ∞} (hA : A.Good) (hAb : A.Good' b) :
    (∃ x : n → ℚ, 0 ≤ x ∧ A ₘ* x ≤ b) ≠ (∃ y : m → ℚ, 0 ≤ y ∧ -Aᵀ ₘ* y ≤ 0 ∧ b ᵥ⬝ y < 0) := by
  -- filter rows and columns
  let m' : Type := { i : m // b i ≠ ⊤ ∧ ∀ j : n, A i j ≠ ⊥ } -- non-tautological rows
  let n' : Type := { j : n // ∀ i' : m', A i'.val j ≠ ⊤ } -- columns that allow non-zero values
  let A' : Matrix m' n' ℚ := -- the new matrix
    Matrix.of (fun i' : m' => fun j' : n' =>
      match matcha : A i'.val j'.val with
      | (q : ℚ) => q
      | ⊥ => False.elim (i'.property.right j' matcha)
      | ⊤ => False.elim (j'.property i' matcha)
    )
  if hbot : ∃ i' : m', b i'.val = ⊥ then
    obtain ⟨i', hi'⟩ := hbot
    convert false_ne_true
    · rw [iff_false, not_exists]
      intro x ⟨hx, hAxb⟩
      specialize hAxb i'.val
      rw [hi', le_bot_iff] at hAxb
      exact Matrix.no_bot_dotProd_nng i'.property.right hx hAxb
    · rw [iff_true]
      use 0
      constructor
      · rfl
      constructor
      · apply Matrix.mulWeig_zero_le_zero
      · rw [Matrix.has_bot_dotProd_nng hi' (by rfl)]
        exact ERat.bot_lt_zero
  else
    let b' : m' → ℚ := -- the new RHS
      fun i' : m' =>
        match hbi : b i'.val with
        | (q : ℚ) => q
        | ⊥ => False.elim (hbot ⟨i', hbi⟩)
        | ⊤ => False.elim (i'.property.left hbi)
    convert standardFarkas A' b'
    · constructor <;> intro ⟨x, hx, ineqalities⟩
      · use (fun j' : n' => x j'.val)
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
          Finset.univ.sum (fun j' : n' => (A' i' j' * x j'.val).toERat) =
          Finset.univ.sum (fun j : n => (x j).toERat * A i'.val j)
        rw [Finset.univ_sum_split_of_zero (p := (fun j : n => ∀ i' : m', A i'.val j ≠ ⊤))]
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
      · use (fun j : n => if hj : (∀ i' : m', A i'.val j ≠ ⊤) then x ⟨j, hj⟩ else 0)
        constructor
        · intro j
          if hj : (∀ i' : m', A i'.val j ≠ ⊤) then
            convert hx ⟨j, hj⟩
            simp [hj]
          else
            aesop
        intro i
        if hi : (b i ≠ ⊤ ∧ ∀ j : n, A i j ≠ ⊥) then
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
            apply bot_le
    · constructor <;> intro ⟨y, hy, ineqalities, sharpine⟩
      · use (fun i' : m' => y i'.val)
        constructor
        · intro i'
          exact hy i'.val
        constructor
        · sorry
        · sorry
      · use (fun i : m => if hi : (b i ≠ ⊤ ∧ ∀ j : n, A i j ≠ ⊥) then y ⟨i, hi⟩ else 0)
        constructor
        · intro i
          if hi : (b i ≠ ⊤ ∧ ∀ j : n, A i j ≠ ⊥) then
            convert hy ⟨i, hi⟩
            simp [hi]
          else
            aesop
        constructor
        · sorry
        · sorry

end generalizedFarkas
