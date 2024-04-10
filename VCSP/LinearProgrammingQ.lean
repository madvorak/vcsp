import VCSP.LinearProgramming
import Mathlib.Tactic.Qify


structure CanonicalRationalSolution (α : Type*) where
  numerators : α → ℕ
  denominator : ℕ
  denom_pos : 0 < denominator

variable {α : Type*}

-- `@[pp_dot]` -- put back after the pretty-printer issue gets fixed
def CanonicalRationalSolution.toFunction (s : CanonicalRationalSolution α) : α → ℚ :=
  fun a : α => (s.numerators a : ℚ) / (s.denominator : ℚ)

variable [Fintype α] [DecidableEq α]

@[pp_dot]
def Function.toCanonicalRationalSolution (x : α → ℚ) : CanonicalRationalSolution α :=
  CanonicalRationalSolution.mk
    (fun a : α => Finset.univ.prod (fun i : α => if i = a then (x i).num.toNat else (x i).den))
    (Finset.univ.prod (fun i : α => (x i).den))
    (Finset.prod_pos (fun i _ => Rat.pos (x i)))


lemma Finset.univ.prod_single_hit (g : α → ℚ) (a : α) :
    Finset.univ.prod (fun i : α => if a = i then g i else 1) = g a := by
  simp_rw [Finset.prod_ite_eq, Finset.mem_univ, if_true]

lemma Finset.univ.prod_mul_single_hit (f g : α → ℚ) (a : α) :
    Finset.univ.prod (fun i : α => f i * if a = i then g i else 1) = Finset.univ.prod f * g a := by
  rw [Finset.prod_mul_distrib, Finset.univ.prod_single_hit]

lemma Finset.univ.prod_with_one_exception {f g : α → ℚ} {a : α} (hfg : f a = 0 → g a = 0) :
    Finset.univ.prod (fun i : α => if a = i then g i else f i) = Finset.univ.prod f * g a / f a := by
  if hf : ∀ i : α, f i ≠ 0 then
    convert Finset.univ.prod_mul_single_hit f (fun i => g i / f i) a using 1
    · apply congr_arg
      ext1 i
      rw [mul_ite, mul_one, mul_div_cancel']
      exact hf i
    · apply mul_div_assoc
  else
    push_neg at hf
    obtain ⟨z, hz⟩ := hf
    convert_to (0 : ℚ) = (0 : ℚ)
    · rw [Finset.prod_eq_zero_iff]
      use z
      exact ⟨Finset.mem_univ z, by aesop⟩
    · rw [mul_div_assoc]
      convert zero_mul _
      rw [Finset.prod_eq_zero_iff]
      use z
      exact ⟨Finset.mem_univ z, hz⟩
    rfl

lemma Finset.univ.prod_with_one_exception' {f g : α → ℚ} {a : α} (hfg : f a = 0 → g a = 0) :
    Finset.univ.prod (fun i : α => if i = a then g i else f i) = Finset.univ.prod f * g a / f a := by
  convert Finset.univ.prod_with_one_exception hfg using 3
  apply eq_comm

lemma nat_cast_eq_int_cast_of_nneg {a : ℤ} (ha : 0 ≤ a) : @Nat.cast ℚ _ (Int.toNat a) = @Int.cast ℚ _ a :=
  Rat.ext (Int.toNat_of_nonneg ha) rfl

lemma toCanonicalRationalSolution_toFunction {x : α → ℚ} (hx : 0 ≤ x) :
    x.toCanonicalRationalSolution.toFunction = x := by
  ext1 a
  convert_to
    Finset.univ.prod (fun i => if i = a then ((x i).num.toNat : ℚ) else ((x i).den : ℚ)) /
      Finset.univ.prod (fun i => ((x i).den : ℚ)) = x a
  · simp [CanonicalRationalSolution.toFunction, Function.toCanonicalRationalSolution]
  rw [Finset.univ.prod_with_one_exception', mul_div_assoc, mul_comm, mul_div_assoc]
  nth_rw 3 [←Rat.num_div_den (x a)]
  convert mul_one _
  apply div_self
  intro contr
  rw [Finset.prod_eq_zero_iff] at contr
  obtain ⟨i, hi⟩ := contr
  have hxinz : ((x i).den : ℚ) ≠ (0 : ℚ)
  · intro impos
    rw [Nat.cast_eq_zero] at impos
    exact (x i).den_nz impos
  exact hxinz hi.right
  · symm
    apply nat_cast_eq_int_cast_of_nneg
    rw [Rat.num_nonneg]
    exact hx a
  · intro imposs
    exfalso
    rw [Nat.cast_eq_zero] at imposs
    exact (x a).den_nz imposs

open scoped Matrix
variable {β : Type*} [Fintype β]

theorem CanonicalLP.IsSolution.toCanonicalRationalSolution {P : CanonicalLP α β ℚ} {x : α → ℚ} (hx : P.IsSolution x) :
    P.A *ᵥ x.toCanonicalRationalSolution.toFunction = P.b := by
  rw [toCanonicalRationalSolution_toFunction hx.right]
  exact hx.left
