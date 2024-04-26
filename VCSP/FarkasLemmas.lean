import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Have
import VCSP.ExtendedRationals
import VCSP.Hardness


section typeclasses

class AlmostOrderedSMul (R M : Type*) [OrderedSemiring R] [OrderedAddCommMonoid M] [SMulZeroClass R M] : Prop where
  /-- Scalar multiplication by positive elements preserves the order. -/
  smul_lt_smul_of_pos : ∀ a b : M, ∀ c : R, a < b → 0 < c → c • a < c • b
  /-- And the opposite direction also holds. -/
  lt_of_smul_lt_smul_of_pos : ∀ a b : M, ∀ c : R, c • a < c • b → 0 < c → a < b

end typeclasses


open scoped Matrix
variable {n m : Type} [Fintype n] [Fintype m]


section basicFarkas

lemma easyFarkas {R : Type*} [OrderedCommRing R] (A : Matrix m n R) (b : m → R) :
    (∃ x : n → R, A *ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → R, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) →
      False := by
  intro ⟨⟨x, hAx, hx⟩, ⟨y, hAy, hby, hy⟩⟩
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
    (∃ x : n → ℚ, A *ᵥ x ≤ b ∧ 0 ≤ x) ≠ (∃ y : m → ℚ, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y)

example (A : Matrix m n ℚ) (b : m → ℚ) :
    (∃ x : n → ℚ, A *ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → ℚ, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) →
      False := by
  intro ⟨hx, hy⟩
  simpa [hx, hy] using standardFarkas A b

end basicFarkas


section instERat

notation "ℚ∞" => ERat

instance : SMulZeroClass ℚ ℚ∞ where
  smul (c : ℚ) (a : ℚ∞) := c.toERat * a
  smul_zero (c : ℚ) := by
    show (c * 0).toERat = 0
    rewrite [mul_zero]
    rfl

instance : AlmostOrderedSMul ℚ ℚ∞ where
  smul_lt_smul_of_pos (a b : ℚ∞) (c : ℚ) (hab : a < b) (hc : 0 < c) := by
    show c.toERat * a < c.toERat * b
    match ha : a with
    | ⊤ =>
      exfalso
      exact not_top_lt hab
    | ⊥ =>
      convert_to ⊥ < c.toERat * b
      · exact ERat.coe_mul_bot_of_pos hc.le
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
      rw [ERat.coe_mul_bot_of_pos hc.le] at hab
      exact not_lt_bot hab
    | (q : ℚ) =>
      change hab to (c * p).toERat < (c * q).toERat
      rw [ERat.coe_lt_coe_iff] at hab ⊢
      rwa [mul_lt_mul_left hc] at hab

lemma smul_toERat_eq_mul_toERat (c a : ℚ) : c • a.toERat = (c * a).toERat := rfl

lemma Function.neg_nonpos_ERat (x : n → ℚ∞) : -x ≤ 0 ↔ 0 ≤ x := by
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
        exact ERat.coe_nonneg.mpr hq
      else
        exfalso
        have : - q ≤ 0
        · exact ERat.coe_nonpos.mp hx
        linarith
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

end instERat


section heteroMatrixProducts

variable {α γ : Type*}

/-- `Matrix.dotProduct'' v w` is the sum of the element-wise products `w i • v i`
    (mnemonic: "vector times weights"). -/
def Matrix.dotProduct'' [AddCommMonoid α] [SMul γ α] (v : m → α) (w : m → γ) : α :=
  Finset.univ.sum (fun i : m => w i • v i)

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`
   and ` ₘ*ᵥ ` for `Matrix.mulVec''` (both have precedence of 73)
   so that `a • v ᵥ⬝ᵥ c • w` is parsed as `(a • v) ᵥ⬝ᵥ (c • w)` and
   that `A ₘ*ᵥ v ᵥ⬝ᵥ w` is parsed as `(A ₘ*ᵥ v) ᵥ⬝ᵥ w` and
   that `v ᵥ⬝ᵥ C *ᵥ w` is parsed as `v ᵥ⬝ᵥ (C *ᵥ w)` and
   that `v ᵥ⬝ᵥ w ᵥ* C` is parsed as `v ᵥ⬝ᵥ (w ᵥ* C)` here. -/
infixl:72 " ᵥ⬝ᵥ " => Matrix.dotProduct''

def Matrix.mulVec'' [AddCommMonoid α] [SMul γ α] (M : Matrix m n α) (w : n → γ) (i : m) : α :=
  (fun j : n => M i j) ᵥ⬝ᵥ w
infixr:73 " ₘ*ᵥ " => Matrix.mulVec''


lemma Matrix.neg_mulVec'' [AddCommMonoid α] [SMul γ α] [Neg α] [Neg γ] [Fintype m] (A : Matrix m n α) (x : n → γ) :
    (-A) ₘ*ᵥ x = - (A ₘ*ᵥ x) := by -- TODO require relationship between `[Neg α]` and `[Neg γ]`
  ext i
  unfold Matrix.mulVec'' Matrix.dotProduct''
  show
    Finset.univ.sum (fun j : n => x j • -(A i j)) =
    -(Finset.univ.sum (fun j : n => x j • A i j))
  --simp_rw [neg_smul] -- would require `Module` which we cannot have
  sorry

lemma Matrix.zero_dotProduct'' [AddCommMonoid α] [SMul γ α] [Zero γ] (v : m → α) : v ᵥ⬝ᵥ (0 : m → γ) = (0 : α) := by
  apply Finset.sum_eq_zero
  intro x _
  rw [Pi.zero_apply]
  --rw [zero_smul] -- TODO require `⊥ ∉ v`
  sorry

lemma Matrix.dotProduct_zero'' [AddCommMonoid α] [SMulZeroClass γ α] (w : m → γ) : (0 : m → α) ᵥ⬝ᵥ w = (0 : α) := by
  apply Finset.sum_eq_zero
  intro x _
  exact smul_zero (w x)

lemma Matrix.mulVec_zero'' [AddCommMonoid α] [SMul γ α] [Zero γ] (A : Matrix m n α) : A ₘ*ᵥ (0 : n → γ) = (0 : m → α) := by
  ext -- TODO require `⊥ ∉ A`
  apply Matrix.zero_dotProduct''

lemma Matrix.dotProduct_le_dotProduct_of_nonneg_left'' [OrderedAddCommMonoid α] [OrderedSemiring γ]
    [SMulZeroClass γ α] [AlmostOrderedSMul γ α]
    {u v : n → α} (huv : u ≤ v) {w : n → γ} (hw : 0 ≤ w) : -- TODO orderings respect something
    u ᵥ⬝ᵥ w ≤ v ᵥ⬝ᵥ w := by
  apply Finset.sum_le_sum
  intro i _
  if huvi : u i = v i then
    rw [huvi]
  else
    if hwi : w i = 0 then
      rw [hwi]
      sorry -- since we don't have `zero_smul`, we possibly need `≤` axioms in addition to `<` axioms
    else
      apply le_of_lt
      apply AlmostOrderedSMul.smul_lt_smul_of_pos
      · exact lt_of_le_of_ne (huv i) huvi
      · exact lt_of_le_of_ne (hw i) (Ne.symm hwi)

lemma Matrix.tranpose_mulVec_dotProduct'' [AddCommMonoid α] [SMul γ α] (A : Matrix m n α) (x : n → γ) (y : m → γ) :
    Aᵀ ₘ*ᵥ y ᵥ⬝ᵥ x = A ₘ*ᵥ x ᵥ⬝ᵥ y := by
  unfold Matrix.mulVec'' Matrix.dotProduct'' Matrix.transpose
  --simp_rw [←Finset.smul_sum]
  --rw [Finset.sum_comm]
  sorry

example (A : Matrix m n ℚ∞) (b : m → ℚ∞) :
    (∃ x : n → ℚ, A ₘ*ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → ℚ, -Aᵀ ₘ*ᵥ y ≤ 0 ∧ b ᵥ⬝ᵥ y < 0 ∧ 0 ≤ y) →
      False := by
  intro ⟨⟨x, hAx, hx⟩, ⟨y, hAy, hby, hy⟩⟩
  have hAy' : 0 ≤ Aᵀ ₘ*ᵥ y
  · rwa [Matrix.neg_mulVec'', Function.neg_nonpos_ERat] at hAy
  rw [← lt_self_iff_false (0 : ℚ∞)]
  calc 0 = 0 ᵥ⬝ᵥ x := (Matrix.dotProduct_zero'' x).symm
    _ ≤ (Aᵀ ₘ*ᵥ y) ᵥ⬝ᵥ x := Matrix.dotProduct_le_dotProduct_of_nonneg_left'' hAy' hx
    _ = (A ₘ*ᵥ x) ᵥ⬝ᵥ y := Matrix.tranpose_mulVec_dotProduct'' ..
    _ ≤ b ᵥ⬝ᵥ y := Matrix.dotProduct_le_dotProduct_of_nonneg_left'' hAx hy
    _ < 0 := hby

-- notation test

variable (v : Fin 3 → ℚ∞) (w : Fin 3 → ℚ) (a : ℚ∞) (c : ℚ)
  (A : Matrix (Fin 3) (Fin 3) ℚ∞) (C : Matrix (Fin 3) (Fin 3) ℚ)

example : a • v ᵥ⬝ᵥ c • w = (a • v) ᵥ⬝ᵥ (c • w) := rfl
example : v ᵥ⬝ᵥ C ₘ*ᵥ w = v ᵥ⬝ᵥ (C ₘ*ᵥ w) := rfl
example : v ᵥ⬝ᵥ w ᵥ* C = v ᵥ⬝ᵥ (w ᵥ* C) := rfl
example : v ᵥ⬝ᵥ C *ᵥ w = v ᵥ⬝ᵥ (C *ᵥ w) := rfl
example : A ₘ*ᵥ v ᵥ⬝ᵥ w = (A ₘ*ᵥ v) ᵥ⬝ᵥ w := rfl

end heteroMatrixProducts


section extendedFarkas

def Matrix.Good (A : Matrix m n ℚ∞) : Prop :=
  ¬ (∃ i : m, (∃ j : n, A i j = ⊤) ∧ (∃ j : n, A i j = ⊥))

lemma Matrix.Good.row {A : Matrix m n ℚ∞} (hA : A.Good) (i : m) :
    (∃ aᵢ : n → ℚ, ∀ j : n, A i j = some (some (aᵢ j))) ∨ (∃ j, A i j = ⊤) ∨ (∃ j, A i j = ⊥) := by
  sorry

theorem generalizedFarkas {A : Matrix m n ℚ∞} {b : m → ℚ∞} (hA : A.Good) (hAT : Aᵀ.Good) :
    (∃ x : n → ℚ, A ₘ*ᵥ x ≤ b ∧ 0 ≤ x) ≠ (∃ y : m → ℚ, -Aᵀ ₘ*ᵥ y ≤ 0 ∧ b ᵥ⬝ᵥ y < 0 ∧ 0 ≤ y) := by
  -- filter rows and columns
  let m' : Type := { i : m // b i ≠ ⊤ ∧ ∀ j : n, A i j ≠ ⊥ } -- non-tautological rows
  let n' : Type := { j : n // ∀ i : m', A i j ≠ ⊤ } -- columns that allow non-zero values
  let A' : Matrix m' n' ℚ := -- the new matrix
    Matrix.of (fun i : m' => fun j : n' =>
      match matcha : A i.val j.val with
      | (q : ℚ) => q
      | ⊥ => False.elim (i.property.right j matcha)
      | ⊤ => False.elim (j.property i matcha)
    )
  if hbot : ∃ i : m', b i.val = ⊥ then
    obtain ⟨i, hi⟩ := hbot
    convert false_ne_true
    · rw [iff_false, not_exists]
      intro x ⟨hAxb, hx⟩
      specialize hAxb i.val
      rw [hi] at hAxb
      -- the `i`th line does not contain `⊥` → contradiction with `hAxb`
      sorry
    · rw [iff_true]
      use 0
      constructor
      · rw [Matrix.mulVec_zero'']
      constructor
      · sorry -- `⊥ < 0` OK
      · rfl
  else
    let b' : m' → ℚ := -- the new RHS
      fun i : m' =>
        match hbi : b i.val with
        | (q : ℚ) => q
        | ⊥ => False.elim (hbot ⟨i, hbi⟩)
        | ⊤ => False.elim (i.property.left hbi)
    convert standardFarkas A' b'
    · constructor <;> intro ⟨x, ineqalities, hx⟩
      · sorry
      · use (fun j : n => if hj : (∀ i : m', A i j ≠ ⊤) then x ⟨j, hj⟩ else 0)
        constructor
        · intro i
          if hi : (b i ≠ ⊤ ∧ ∀ j : n, A i j ≠ ⊥) then
            have inequality := ineqalities ⟨i, hi⟩
            sorry
          else
            push_neg at hi
            if hbi : b i = ⊤ then
              rw [hbi]
              apply le_top
            else
              obtain ⟨j, hAij⟩ := hi hbi
              convert_to ⊥ ≤ b i
              · sorry
              apply bot_le
        · intro j
          if hj : (∀ i : m', A i j ≠ ⊤) then
            convert hx ⟨j, hj⟩
            simp [hj]
          else
            aesop
    · constructor <;> intro ⟨y, ineqalities, sharpine, hy⟩
      · sorry
      · sorry

end extendedFarkas
