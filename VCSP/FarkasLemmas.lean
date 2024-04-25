import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Have
import VCSP.ExtendedRationals

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


section instERatSMul

notation "ℚ∞" => ERat

instance : Module ℚ ℚ∞ where
  smul (c : ℚ) (a : ℚ∞) := c.toERat * a
  one_smul (a : ℚ∞) := by
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (q : ℚ) =>
      show ((1 : ℚ) * (q : ℚ)).toERat = q.toERat
      rw [one_mul]
  mul_smul (x y : ℚ) (a : ℚ∞) := by
    match a with
    | ⊥ => sorry -- broken because `(0 * (-1)) * ⊥ = ⊥` but `0 * ((-1) * ⊥) = 0`
    | ⊤ => sorry -- broken because `(0 * (-1)) * ⊤ = 0` but `0 * ((-1) * ⊤) = ⊥`
    | (q : ℚ) =>
      show (x * y * q).toERat = (x * (y * q)).toERat
      rw [mul_assoc]
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

example (c a : ℚ) : c • a.toERat = (c * a).toERat := rfl

lemma neg_nonpos'' (x : n → ℚ∞) : -x ≤ 0 ↔ 0 ≤ x := by
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

end instERatSMul


section heteroMatrixProducts

variable {α γ : Type*} [AddCommMonoid α] [SMul γ α]

/-- `Matrix.dotProduct'' v w` is the sum of the element-wise products `w i • v i`
    (mnemonic: "vector times weights"). -/
def Matrix.dotProduct'' (v : m → α) (w : m → γ) : α :=
  Finset.univ.sum (fun i : m => w i • v i)

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`
   and ` ₘ*ᵥ ` for `Matrix.mulVec''` and ` ᵥ*ₘ ` for `Matrix.vecMul''`
   so that `a • v ᵥ⬝ᵥ c • w` is parsed as `(a • v) ᵥ⬝ᵥ (c • w)` and
   that `A ₘ*ᵥ v ᵥ⬝ᵥ w` is parsed as `(A ₘ*ᵥ v) ᵥ⬝ᵥ w` and
   that `v ᵥ*ₘ A ᵥ⬝ᵥ w` is parsed as `(v ᵥ*ₘ A) ᵥ⬝ᵥ w` and
   that `v ᵥ⬝ᵥ C *ᵥ w` is parsed as `v ᵥ⬝ᵥ (C *ᵥ w)` and
   that `v ᵥ⬝ᵥ w ᵥ* C` is parsed as `v ᵥ⬝ᵥ (w ᵥ* C)` here. -/
infixl:72 " ᵥ⬝ᵥ " => Matrix.dotProduct''

def Matrix.mulVec'' (M : Matrix m n α) (v : n → γ) (i : m) : α :=
  (fun j : n => M i j) ᵥ⬝ᵥ v
infixr:73 " ₘ*ᵥ " => Matrix.mulVec''

def Matrix.vecMul'' (v : m → γ) (M : Matrix m n α) (j : n) : α :=
  (fun i : m => M i j) ᵥ⬝ᵥ v
infixl:73 " ᵥ*ₘ " => Matrix.vecMul''
-- TODO deprecate ` ᵥ*ₘ `

lemma Matrix.mulVec_transpose'' [Fintype m] (A : Matrix m n α) (x : m → γ) :
    Aᵀ ₘ*ᵥ x = x ᵥ*ₘ A :=
  rfl

lemma Matrix.neg_mulVec'' [Neg α] [Neg γ] [Fintype m] (A : Matrix m n α) (x : n → γ) :
    (-A) ₘ*ᵥ x = - (A ₘ*ᵥ x) := by -- TODO require relationship between `[Neg α]` and `[Neg γ]`
  ext i
  sorry

lemma Matrix.zero_dotProduct'' [Zero γ] (v : m → α) : v ᵥ⬝ᵥ (0 : m → γ) = (0 : α) := by
  sorry

lemma Matrix.dotProduct_zero'' (w : m → γ) : (0 : m → α) ᵥ⬝ᵥ w = (0 : α) := by
  sorry

lemma Matrix.mulVec_zero'' [Zero γ] (A : Matrix m n α) : A ₘ*ᵥ (0 : n → γ) = (0 : m → α) := by
  ext
  apply Matrix.zero_dotProduct''

lemma Matrix.dotProduct_le_dotProduct_of_nonneg_right'' [PartialOrder α] [PartialOrder γ]
    {u : n → α} (hu : 0 ≤ u) {v w : n → γ} (hvw : v ≤ w) : -- TODO orderings respect something
    u ᵥ⬝ᵥ v ≤ u ᵥ⬝ᵥ w := by
  sorry

lemma Matrix.dotProduct_le_dotProduct_of_nonneg_left'' [PartialOrder α] [NonUnitalNonAssocSemiring γ] [PartialOrder γ]
    {u v : n → α} (huv : u ≤ v) {w : n → γ} (hw : 0 ≤ w) : -- TODO orderings respect something
    u ᵥ⬝ᵥ w ≤ v ᵥ⬝ᵥ w := by
  sorry

example (A : Matrix m n ℚ∞) (b : m → ℚ∞) :
    (∃ x : n → ℚ, A ₘ*ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → ℚ, -Aᵀ ₘ*ᵥ y ≤ 0 ∧ b ᵥ⬝ᵥ y < 0 ∧ 0 ≤ y) →
      False := by
  intro ⟨⟨x, hAx, hx⟩, ⟨y, hAy, hby, hy⟩⟩
  have hAy' : 0 ≤ y ᵥ*ₘ A
  · rwa [Matrix.neg_mulVec'', Matrix.mulVec_transpose'', neg_nonpos''] at hAy
  exfalso
  rw [← lt_self_iff_false (0 : ℚ∞)]
  calc 0 = 0 ᵥ⬝ᵥ x := sorry
    _ ≤ (y ᵥ*ₘ A) ᵥ⬝ᵥ x := sorry
    _ = (A ₘ*ᵥ x) ᵥ⬝ᵥ y := sorry
    _ ≤ b ᵥ⬝ᵥ y := sorry
    _ < 0 := hby

-- notation test

variable (v : Fin 3 → ℚ∞) (w : Fin 3 → ℚ) (a : ℚ∞) (c : ℚ)
  (A : Matrix (Fin 3) (Fin 3) ℚ∞) (C : Matrix (Fin 3) (Fin 3) ℚ)

example : a • v ᵥ⬝ᵥ c • w = (a • v) ᵥ⬝ᵥ (c • w) := rfl
example : A ₘ*ᵥ v ᵥ⬝ᵥ w = (A ₘ*ᵥ v) ᵥ⬝ᵥ w := rfl
example : v ᵥ*ₘ A ᵥ⬝ᵥ w = (v ᵥ*ₘ A) ᵥ⬝ᵥ w := rfl
example : v ᵥ⬝ᵥ C ₘ*ᵥ w = v ᵥ⬝ᵥ (C ₘ*ᵥ w) := rfl
example : v ᵥ⬝ᵥ w ᵥ*ₘ C = v ᵥ⬝ᵥ (w ᵥ*ₘ C) := rfl
example : v ᵥ⬝ᵥ w ᵥ* C = v ᵥ⬝ᵥ (w ᵥ*ₘ C) := rfl
example : v ᵥ⬝ᵥ w ᵥ*ₘ C = v ᵥ⬝ᵥ (w ᵥ* C) := rfl
example : v ᵥ⬝ᵥ w ᵥ* C = v ᵥ⬝ᵥ (w ᵥ* C) := rfl
example : v ᵥ⬝ᵥ C *ᵥ w = v ᵥ⬝ᵥ (C *ᵥ w) := rfl

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
