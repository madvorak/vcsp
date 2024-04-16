import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Have
import VCSP.ExtendedRationals

open scoped Matrix

variable {n m : Type*} [Fintype n] [Fintype m]


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
  sorry

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

/-
The following should hold since we have changed the definition of `*` on `ERat` so that `⊥ * 0 = ⊥`.
-/
theorem generalizedFarkas (A : Matrix m n ERat) (b : m → ERat) :
    (∃ x : n → ERat, A ₘ*ᵥ x ≤ b ∧ 0 ≤ x) ≠ (∃ y : m → ERat, -Aᵀ ₘ*ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) := by
  sorry
