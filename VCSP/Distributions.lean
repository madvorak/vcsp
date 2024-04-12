import Mathlib.Combinatorics.Optimization.ValuedCSP


/-
abbrev Function.evalOnDistribution {α β : Type*} [Fintype α] [DivisionSemiring β] (f : α → β) (w : α → ℕ) : β :=
  Finset.univ.sum (fun i : α => w i • f i) / Finset.univ.sum w

abbrev Function.evalOnDistribution {α β : Type*} [Fintype α] [AddCommMonoid β] [SMul ℚ β]
    (f : α → β) (w : α → ℚ) : β :=
  (Finset.univ.sum w)⁻¹ • Finset.univ.sum (fun i : α => w i • f i)
-/

abbrev Function.evalOnDistribution {α β : Type*} [Fintype α] [AddCommMonoid β] [SMul ℚ β]
    (f : α → β) (w : α → ℚ) : β :=
  Finset.univ.sum (fun i : α => (w i / Finset.univ.sum w) • f i)

infix:996 "˛" => Function.evalOnDistribution

private def f : Fin 4 → ℚ := ![1, -9.99, 2, 3.724]
private def w : Fin 4 → ℚ := ![3, 0, 1, 0]

example : f˛w = 1.25 := by
  rfl

abbrev Function.evalOnWeighted {α β : Type*} [Fintype α] [AddCommMonoid β] [SMul ℚ β]
    (f : α → β) (w : α → ℕ) : β :=
  f.evalOnDistribution (Nat.cast ∘ w)

infix:997 "˛" => Function.evalOnWeighted

abbrev Function.evalAveMultiset {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β] [SMul ℚ β]
    (f : α → β) (s : Multiset α) : β :=
  f˛ s.count

infix:998 "˛" => Function.evalAveMultiset

example : f˛{0, 2, 0, 0} = 1.25 := by
  rfl

example : f˛ ([0, 2, 0, 0] : List (Fin 4)) = 1.25 := by
  rfl

private inductive Label
| a : Label
| b : Label
| c : Label
deriving DecidableEq

private instance : Fintype Label :=
  Fintype.mk {.a, .b, .c} (fun x => by cases x <;> simp)

private def F : Label → ℚ
| .a => 3.1
| .b => 2.5
| .c => 0.8

example : F˛ {.a, .b, .c, .b, .a} = 2.4 := by
  rfl


abbrev Function.evalOnWeights {α β : Type*} [Fintype α] [AddCommMonoid β]
    (f : α → β) (w : α → ℕ) : β :=
  Finset.univ.sum (fun i : α => w i • f i)

def Functions_evalOnWeightsLE {α β : Type*} [Fintype α] [OrderedAddCommMonoid β]
    (f₁ f₂ : α → β) (w₁ w₂ : α → ℕ) : Prop :=
  Finset.univ.sum w₂ • f₁.evalOnWeights w₁ ≤ Finset.univ.sum w₁ • f₂.evalOnWeights w₂

example {α : Type*} [Fintype α] (f₁ f₂ : α → ℚ) (w₁ w₂ : α → ℕ)
    (hw₁ : ∃ i : α, w₁ i > 0) (hw₂ : ∃ i : α, w₂ i > 0) :
    Functions_evalOnWeightsLE f₁ f₂ w₁ w₂ ↔ f₁˛w₁ ≤ f₂˛w₂ := by
  simp only [
    Functions_evalOnWeightsLE, Function.evalOnWeights, Function.evalOnWeighted, Function.evalOnDistribution,
    nsmul_eq_mul, Nat.cast_sum, Function.comp_apply, smul_eq_mul, div_eq_mul_inv]
  conv =>
    rhs
    congr
    · congr
      · rfl
      ext i
      left
      rw [mul_comm]
    · congr
      · rfl
      ext i
      left
      rw [mul_comm]
  conv =>
    rhs
    congr
    · congr
      · rfl
      ext i
      rw [mul_assoc]
    · congr
      · rfl
      ext i
      rw [mul_assoc]
  rw [←Finset.mul_sum, ←Finset.mul_sum]
  conv =>
    rhs
    congr <;> rw [mul_comm, ←div_eq_mul_inv]
  constructor <;> intro hyp
  · rw [div_le_div_iff]
    convert hyp using 1 <;> apply mul_comm
    · apply Finset.sum_pos' <;> aesop
    · apply Finset.sum_pos' <;> aesop
  · rw [div_le_div_iff] at hyp
    convert hyp using 1 <;> apply mul_comm
    · apply Finset.sum_pos' <;> aesop
    · apply Finset.sum_pos' <;> aesop
