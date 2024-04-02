import VCSP.LinearProgramming
import VCSP.ExtendedRationals
import Mathlib.Tactic.Qify


structure CanonicalRationalSolution (α : Type*) where
  numerators : α → ℕ∞
  denominator : ℕ
  denom_pos : 0 < denominator

variable {α : Type*}

-- `@[pp_dot]` -- put back after the pretty-printer issue gets fixed
def CanonicalRationalSolution.toFunction (s : CanonicalRationalSolution α) : α → ERat :=
  fun a : α =>
    match s.numerators a with
    | ⊤ => ⊤
    | some n => some ((n : ℚ) / (s.denominator : ℚ))

variable [Fintype α] [DecidableEq α]

@[pp_dot]
def Function.toCanonicalRationalSolution (x : α → ERat) : CanonicalRationalSolution α :=
  CanonicalRationalSolution.mk
    (fun a : α => Finset.univ.prod
      (fun i : α =>
        if i = a then
          match x i with
          | ⊤ => ⊤
          | ⊥ => ⊥
          | some (some q) => some q.num.toNat
        else
          match x i with
          | ⊤ => 1
          | ⊥ => 1
          | some (some q) => some q.den
      ))
    (Finset.univ.prod
      (fun i : α =>
        match x i with
        | ⊤ => 1
        | ⊥ => 1
        | some (some q) => q.den
      ))
    (Finset.prod_pos
      (fun i _ =>
        match x i with
        | ⊤ => zero_lt_one
        | ⊥ => zero_lt_one
        | some (some q) => q.den_pos
      ))
