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
def CanonicalRationalSolution.toFunction (s : CanonicalRationalSolution α) : α → ℚ≥0∞ :=
  fun a : α =>
    match s.numerators a with
    | ⊤ => ⊤
    | some n => some ((n : ℚ≥0) / (s.denominator : ℚ≥0))

variable [Fintype α] [DecidableEq α]

@[pp_dot]
def Function.toCanonicalRationalSolution (x : α → ℚ≥0∞) : CanonicalRationalSolution α :=
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
          | some q => some q.den
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

lemma toCanonicalRationalSolution_toFunction {x : α → ℚ≥0∞} (hx : 0 ≤ x) :
    x.toCanonicalRationalSolution.toFunction = x := by
  ext1 a
  unfold CanonicalRationalSolution.toFunction
  unfold Function.toCanonicalRationalSolution
  simp only [Nat.cast_prod]
  if hxa : x a = ⊤ then
    rw [hxa]
    have product_is_infinite :
      Finset.univ.prod
        (fun i : α =>
          if i = a then
            match x i with
            | ⊤ => (⊤ : ℕ∞)
            | some q => (some q.num : ℕ∞)
          else
            match x i with
            | ⊤ => (1 : ℕ∞)
            | some q => (some q.den : ℕ∞)
        ) = (⊤ : ℕ∞)
    · sorry
    simp [product_is_infinite]
  else
    sorry

open scoped Matrix
variable {β : Type*} [Fintype β]

theorem CanonicalLP.IsSolution.toCanonicalRationalSolution {P : CanonicalLP α β ℚ≥0∞} {x : α → ℚ≥0∞}
    (hx : P.IsSolution x) :
    P.A *ᵥ x.toCanonicalRationalSolution.toFunction = P.b := by
  rw [toCanonicalRationalSolution_toFunction hx.right]
  exact hx.left
