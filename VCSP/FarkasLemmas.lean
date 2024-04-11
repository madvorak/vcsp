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

theorem generalizedFarkas [NonUnitalNonAssocSemiring EReal] (A : Matrix m n EReal) (b : m → EReal) :
    (∃ x : n → EReal, A *ᵥ x ≤ b ∧ 0 ≤ x) ≠ (∃ y : m → EReal, 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0 ∧ 0 ≤ y) := by
  sorry -- very very very cheating
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

-/
