import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Pi
import VCSP.AlgebraC


variable {D C : Type*}

/-- Partial evaluation of a `Γ` instance `I` for given partial solution `x` waiting for rest. -/
def ValuedCsp.Instance.evalPartial [OrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : (μ → D) → C :=
  fun r => I.evalSolution (Sum.elim x r)

variable [Nonempty D] [Fintype D] [OrderedAddCommMonoidWithInfima C]

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, minimizing over the rest. -/
def ValuedCsp.Instance.evalMinimize {Γ : ValuedCsp D C} {ι μ : Type*} [DecidableEq μ] [Fintype μ]
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : C :=
  Finset.univ.inf' Finset.univ_nonempty (I.evalPartial x)

/-- A new VCSP template made of all functions expressible by `Γ`. -/
def ValuedCsp.expressivePower (Γ : ValuedCsp D C) : ValuedCsp D C :=
  { ⟨n, I.evalMinimize⟩ | (n : ℕ) (m : ℕ) (I : Γ.Instance (Fin n ⊕ Fin m)) }

/-- Expressive power of a VCSP template subsumes the template. -/
lemma ValuedCsp.subset_expressivePower (Γ : ValuedCsp D C) :
    Γ ⊆ Γ.expressivePower := by
  rintro ⟨n, f⟩ hfΓ
  unfold ValuedCsp.expressivePower
  rw [Set.mem_setOf_eq]
  use n, 0
  unfold ValuedCsp.Instance
  use { ValuedCsp.Term.mk n f hfΓ Sum.inl }
  unfold ValuedCsp.Instance.evalMinimize
  unfold ValuedCsp.Instance.evalPartial
  rw [Sigma.mk.inj_iff, heq_eq_eq]
  constructor
  · rfl
  simp only [ValuedCsp.Instance.evalSolution, Multiset.map_singleton, Multiset.sum_singleton,
    Finset.univ_unique, Finset.inf'_singleton]
  rfl

/-- Expressive power is an idempotent operation on VCSP templates. -/
lemma ValuedCsp.expressivePower_expressivePower (Γ : ValuedCsp D C) :
    Γ.expressivePower = Γ.expressivePower.expressivePower := by
  apply Set.eq_of_subset_of_subset
  · apply ValuedCsp.subset_expressivePower
  rintro ⟨n, f⟩ hnf
  sorry
