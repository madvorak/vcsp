import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.EReal
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Have

open scoped Matrix

variable {n m : Type*} [Fintype n] [Fintype m]


lemma easyFarkas {R : Type*} [OrderedCommSemiring R] (A : Matrix m n R) (b : m → R) :
    (∃ x : n → R, A *ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → R, 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) →
      False := by
  intro ⟨⟨x, hAx, hx⟩, ⟨y, hAy, hby, hy⟩⟩
  have hAy' : 0 ≤ y ᵥ* A
  · rwa [Matrix.mulVec_transpose] at hAy
  exfalso
  rw [← lt_self_iff_false (0 : R)]
  calc 0 = 0 ⬝ᵥ x := (Matrix.zero_dotProduct x).symm
    _ ≤ (y ᵥ* A) ⬝ᵥ x := Matrix.dotProduct_le_dotProduct_of_nonneg_right hAy' hx
    _ = y ⬝ᵥ (A *ᵥ x) := (Matrix.dotProduct_mulVec y A x).symm
    _ ≤ y ⬝ᵥ b := Matrix.dotProduct_le_dotProduct_of_nonneg_left hAx hy
    _ = b ⬝ᵥ y := Matrix.dotProduct_comm y b
    _ < 0 := hby

axiom FarkasLemma (A : Matrix m n ℚ) (b : m → ℚ) :
    (∃ x : n → ℚ, A *ᵥ x ≤ b ∧ 0 ≤ x) ≠ (∃ y : m → ℚ, 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y)

example (A : Matrix m n ℚ) (b : m → ℚ) :
    (∃ x : n → ℚ, A *ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → ℚ, 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) →
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

lemma Matrix.zero_dotProduct'' {α : Type} [Mul α] [AddCommMonoid α] (v : m → α) : 0 ⬝ᵥ v = 0 :=
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

example (A : Matrix m n EReal) (b : m → EReal) :
    (∃ x : n → EReal, A ₘ*ᵥ x ≤ b ∧ 0 ≤ x) ∧ (∃ y : m → EReal, 0 ≤ Aᵀ ₘ*ᵥ y ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) →
      False := by
  intro ⟨⟨x, hAx, hx⟩, ⟨y, hAy, hby, hy⟩⟩
  have hAy' : 0 ≤ y ᵥ*ₘ A
  · rwa [Matrix.mulVec_transpose''] at hAy
  exfalso
  rw [← lt_self_iff_false (0 : EReal)]
  calc 0 = 0 ⬝ᵥ x := (Matrix.zero_dotProduct'' x).symm
    _ ≤ (y ᵥ*ₘ A) ⬝ᵥ x := Matrix.dotProduct_le_dotProduct_of_nonneg_right'' hAy' hx
    _ = y ⬝ᵥ (A ₘ*ᵥ x) := (Matrix.dotProduct_mulVec'' y A x).symm
    _ ≤ y ⬝ᵥ b := Matrix.dotProduct_le_dotProduct_of_nonneg_left'' hAx hy
    _ = b ⬝ᵥ y := Matrix.dotProduct_comm y b
    _ < 0 := hby

theorem generalizedFarkas (A : Matrix m n EReal) (b : m → EReal) :
    (∃ x : n → EReal, A ₘ*ᵥ x ≤ b ∧ 0 ≤ x) ≠ (∃ y : m → EReal, 0 ≤ Aᵀ ₘ*ᵥ y ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) := by
  sorry
/-

Does not work!
Counterexample:

A := ![ ![⊤], ![⊥] ]
b := ![ 3, -2 ]

⊤ * x ≤ 3
⊥ * x ≤ -2
x ≥ 0
... not satisfiable

⊤ * y + ⊥ * y' ≥ 0
3 * y - 2 * y' < 0
y, y' ≥ 0
... not satisfiable


Does not even work when ⊥ is forbidden!
Counterexample:

A := ![ ![⊤, -1], ![-1, 0] ]
b := ![ 0, -1 ]

⊤ * p + (-1) * q ≤ 0         ... ⊤ * p ≤ q    →  ⊤ ≤ q
(-1) * p + 0 * q ≤ -1        ... p ≥ 1
p, q ≥ 0
... not satisfiable

⊤ * r + (-1) * s ≥ 0         ... ⊤ * r ≥ s              →  0 ≥ s  →  s = 0
(-1) * r + 0 * s ≥ 0         ... r ≤ 0        →  r = 0
0 * r + (-1) * s < 0         ... s > 0                                      → 0 > 0
r, s ≥ 0
... not satisfiable

-/
