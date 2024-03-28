import VCSP.LinearProgramming
import VCSP.ENNRationals
import Mathlib.Tactic.Qify

open scoped NNRat


structure CanonicalRationalSolution (α : Type*) where
  numerators : α → ℕ∞
  denominator : ℕ
  denom_pos : 0 < denominator

variable {α : Type*}

-- `@[pp_dot]` -- put back after the pretty-printer issue gets fixed
def CanonicalRationalSolution.toFunction (s : CanonicalRationalSolution α) : α → ℚ∞ :=
  fun a : α =>
    match s.numerators a with
    | ⊤ => ⊤
    | some n => some ((n : ℚ≥0) / (s.denominator : ℚ≥0))

variable [Fintype α] [DecidableEq α]

@[pp_dot]
def Function.toCanonicalRationalSolution (x : α → ℚ∞) : CanonicalRationalSolution α :=
  CanonicalRationalSolution.mk
    (fun a : α => Finset.univ.prod
      (fun i : α =>
        if i = a then
          match x i with
          | ⊤ => ⊤
          | some q => some q.num
        else
          match x i with
          | ⊤ => 1
          | some q => q.den
      ))
    (Finset.univ.prod
      (fun i : α =>
        match x i with
        | ⊤ => 1
        | some q => q.den
      ))
    (Finset.prod_pos
      (fun i _ =>
        match x i with
        | ⊤ => zero_lt_one
        | some q => q.den_pos
      ))

lemma toCanonicalRationalSolution_toFunction {x : α → ℚ∞} (hx : 0 ≤ x) :
    x.toCanonicalRationalSolution.toFunction = x := by
  ext1 a
  unfold CanonicalRationalSolution.toFunction
  unfold Function.toCanonicalRationalSolution
  simp only [Nat.cast_prod]
  match x a with
  | ⊤ => sorry
  | some q => sorry

open scoped Matrix
variable {β : Type*} [Fintype β]

theorem CanonicalLP.IsSolution.toCanonicalRationalSolution {P : CanonicalLP α β ℚ∞} {x : α → ℚ∞} (hx : P.IsSolution x) :
    P.A *ᵥ x.toCanonicalRationalSolution.toFunction = P.b := by
  rw [toCanonicalRationalSolution_toFunction hx.right]
  exact hx.left
