import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Have
import VCSP.ExtendedRationals

open scoped Matrix

variable {n m : Type} [Fintype n] [Fintype m]


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

axiom FarkasLemma (A : Matrix m n ℚ) (b : m → ℚ) :
    (∃ x : n → ℚ, A *ᵥ x ≤ b ∧ 0 ≤ x) ≠ (∃ y : m → ℚ, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y)

example (A : Matrix m n ℚ) (b : m → ℚ) :
    (∃ x : n → ℚ, A *ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → ℚ, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) →
      False := by
  intro ⟨hx, hy⟩
  simpa [hx, hy] using FarkasLemma A b


def Matrix.mulVec'' {α : Type} [Mul α] [AddCommMonoid α] (M : Matrix m n α) (v : n → α) : m → α
  | i => (fun j => M i j) ⬝ᵥ v
infixr:73 " ₘ*ᵥ " => Matrix.mulVec''

def Matrix.vecMul'' {α : Type} [Mul α] [AddCommMonoid α] [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
  | j => v ⬝ᵥ fun i => M i j
infixl:73 " ᵥ*ₘ " => Matrix.vecMul''

lemma Matrix.mulVec_transpose'' {α : Type} [Mul α] [AddCommMonoid α] [Fintype m] (A : Matrix m n α) (x : m → α) :
    Aᵀ ₘ*ᵥ x = x ᵥ*ₘ A :=
  sorry

lemma Matrix.neg_mulVec'' {α : Type} [Mul α] [AddCommMonoid α] [Neg α] [Fintype m] (A : Matrix m n α) (x : n → α) :
    (-A) ₘ*ᵥ x = - (A ₘ*ᵥ x) :=
  sorry

lemma Matrix.zero_dotProduct'' {α : Type} [Mul α] [AddCommMonoid α] (x : m → α) : 0 ⬝ᵥ x = 0 :=
  sorry -- TODO `x` cannot contain `⊥`

lemma Matrix.dotProduct_zero'' {α : Type} [Mul α] [AddCommMonoid α] (x : m → α) : x ⬝ᵥ 0 = 0 :=
  sorry -- TODO `x` cannot contain `⊥`

-- In fact `x ⬝ᵥ 0 = (if ∃ j, x j = ⊥ then ⊥ else 0) = 0 ⬝ᵥ x` TODO!

lemma Matrix.mulVec_zero'' {α : Type} [Mul α] [AddCommMonoid α] (A : Matrix m n α) : A ₘ*ᵥ 0 = 0 := by
  ext -- TODO `A` cannot contain `⊥`
  apply Matrix.dotProduct_zero''

lemma Matrix.dotProduct_mulVec'' {α : Type} [Mul α] [AddCommMonoid α]
    (v : m → α) (A : Matrix m n α) (w : n → α) : v ⬝ᵥ A ₘ*ᵥ w = v ᵥ*ₘ A ⬝ᵥ w :=
  sorry

lemma Matrix.dotProduct_le_dotProduct_of_nonneg_right'' {α : Type} [Mul α] [OrderedAddCommMonoid α] {u v w : n → α}
    (huv : u ≤ v) (hw : 0 ≤ w) :
    u ⬝ᵥ w ≤ v ⬝ᵥ w :=
  sorry

lemma Matrix.dotProduct_le_dotProduct_of_nonneg_left'' {α : Type} [Mul α] [OrderedAddCommMonoid α] {u v w : n → α}
    (huv : u ≤ v) (hw : 0 ≤ w) :
    w ⬝ᵥ u ≤ w ⬝ᵥ v :=
  sorry

-- TODO require commutative multiplication, like `[CommSemigroup α]`
lemma Matrix.dotProduct_comm'' {α : Type} [Mul α] [OrderedAddCommMonoid α] (v w : n → α) :
    v ⬝ᵥ w = w ⬝ᵥ v :=
  sorry

lemma neg_nonpos'' (x : n → ERat) : -x ≤ 0 ↔ 0 ≤ x := by
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

example (A : Matrix m n ERat) (b : m → ERat) :
    (∃ x : n → ERat, A ₘ*ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → ERat, -Aᵀ ₘ*ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) →
      False := by
  intro ⟨⟨x, hAx, hx⟩, ⟨y, hAy, hby, hy⟩⟩
  have hAy' : 0 ≤ y ᵥ*ₘ A
  · rwa [Matrix.neg_mulVec'', Matrix.mulVec_transpose'', neg_nonpos''] at hAy
  exfalso
  rw [← lt_self_iff_false (0 : ERat)]
  calc 0 = 0 ⬝ᵥ x := (Matrix.zero_dotProduct'' x).symm
    _ ≤ (y ᵥ*ₘ A) ⬝ᵥ x := Matrix.dotProduct_le_dotProduct_of_nonneg_right'' hAy' hx
    _ = y ⬝ᵥ (A ₘ*ᵥ x) := (Matrix.dotProduct_mulVec'' y A x).symm
    _ ≤ y ⬝ᵥ b := Matrix.dotProduct_le_dotProduct_of_nonneg_left'' hAx hy
    _ = b ⬝ᵥ y := Matrix.dotProduct_comm'' y b
    _ < 0 := hby

def Matrix.Good (A : Matrix m n ERat) : Prop :=
  ¬ (∃ i : m, (∃ j : n, A i j = ⊤) ∧ (∃ j : n, A i j = ⊥))

lemma Matrix.Good.row {A : Matrix m n ERat} (hA : A.Good) (i : m) :
    (∃ aᵢ : n → ℚ, ∀ j : n, A i j = some (some (aᵢ j))) ∨ (∃ j, A i j = ⊤) ∨ (∃ j, A i j = ⊥) := by
  sorry

theorem generalizedFarkas {A : Matrix m n ERat} {b : m → ERat} (hA : A.Good) (hAT : Aᵀ.Good) :
    -- TODO should probably talk about `x : n → ℚ` and `y : m → ℚ` instead
    (∃ x : n → ERat, A ₘ*ᵥ x ≤ b ∧ 0 ≤ x) ≠ (∃ y : m → ERat, -Aᵀ ₘ*ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) := by
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
    convert FarkasLemma A' b'
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
