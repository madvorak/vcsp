import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Pi
import VCSP.AlgebraC


variable {D C : Type*}

/-- Partial evaluation of a `Γ` instance `I` for given partial solution `x` waiting for rest. -/
def ValuedCSP.Instance.evalPartial [OrderedAddCommMonoid C] {Γ : ValuedCSP D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : (μ → D) → C :=
  fun r => I.evalSolution (Sum.elim x r)

variable [Dne : Nonempty D] [Fintype D] [LinearOrderedAddCommMonoid C]

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, minimizing over the rest. -/
def ValuedCSP.Instance.evalMinimize {Γ : ValuedCSP D C} {ι μ : Type*} [DecidableEq μ] [Fintype μ]
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : C :=
  Finset.univ.inf' Finset.univ_nonempty (I.evalPartial x)

/-- A new VCSP template made of all functions expressible by `Γ`. -/
def ValuedCSP.expressivePower (Γ : ValuedCSP D C) : ValuedCSP D C :=
  { ⟨n, I.evalMinimize⟩ | (n : ℕ) (m : ℕ) (I : Γ.Instance (Fin n ⊕ Fin m)) }

/-- Expressive power of a VCSP template subsumes the template. -/
lemma ValuedCSP.subset_expressivePower (Γ : ValuedCSP D C) :
    Γ ⊆ Γ.expressivePower := by
  rintro ⟨n, f⟩ hfΓ
  unfold ValuedCSP.expressivePower
  rw [Set.mem_setOf_eq]
  use n, 0
  unfold ValuedCSP.Instance
  use { ValuedCSP.Term.mk n f hfΓ Sum.inl }
  unfold ValuedCSP.Instance.evalMinimize
  unfold ValuedCSP.Instance.evalPartial
  rw [Sigma.mk.inj_iff, heq_eq_eq]
  constructor
  · rfl
  simp only [ValuedCSP.Instance.evalSolution, Multiset.map_singleton, Multiset.sum_singleton,
    Finset.univ_unique, Finset.inf'_singleton]
  rfl

/-- Expressive power is an idempotent operation on VCSP templates. -/
lemma ValuedCSP.expressivePower_expressivePower (Γ : ValuedCSP D C) :
    Γ.expressivePower = Γ.expressivePower.expressivePower := by
  apply Set.eq_of_subset_of_subset
  · apply ValuedCSP.subset_expressivePower
  rintro ⟨n, f⟩ hnf
  sorry
