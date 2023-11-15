import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Order.ConditionallyCompleteLattice.Basic


variable {D C : Type*} [OrderedAddCommMonoid C]

/-- Partial evaluation of a `Γ` instance `I` for given partial solution `x` waiting for rest. -/
def ValuedCsp.Instance.evalPartial {Γ : ValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : (μ → D) → C :=
  fun r => I.evalSolution (Sum.elim x r)

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, minimizing over the rest. -/
def ValuedCsp.Instance.evalMinimize [CompleteLattice C] {Γ : ValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : C :=
  sInf { z | ∃ y : μ → D, I.evalPartial x y = z }

/-- Function expressed by a `Γ` instance `I` exposing `m` free variables. -/
def ValuedCsp.Instance.expresses [CompleteLattice C] {Γ : ValuedCsp D C} {m : ℕ} {μ : Type*}
    (I : Γ.Instance (Fin m ⊕ μ)) : Σ (n : ℕ), (Fin n → D) → C :=
  ⟨m, I.evalMinimize⟩

/-- A new VCSP template made of all functions expressible by `Γ`. -/
def ValuedCsp.expressivePower [CompleteLattice C]
    (Γ : ValuedCsp D C) : ValuedCsp D C :=
  { f : Σ (n : ℕ), (Fin n → D) → C | ∃ m : ℕ, ∃ μ : Type, ∃ I : Γ.Instance (Fin m ⊕ μ), I.expresses = f }

/-- Expressive power of a VCSP template subsumes the template. -/
lemma ValuedCsp.subset_expressivePower [CompleteLattice C]
    (Γ : ValuedCsp D C) : Γ ⊆ Γ.expressivePower := by
  rintro ⟨n, f⟩ hfΓ
  unfold ValuedCsp.expressivePower
  rw [Set.mem_setOf_eq]
  use n, Empty
  use {ValuedCsp.Term.mk n f hfΓ Sum.inl}
  unfold ValuedCsp.Instance.expresses
  simp [ValuedCsp.Instance.evalMinimize, ValuedCsp.Instance.evalPartial]
  ext x
  unfold ValuedCsp.Instance.evalSolution
  simp_rw [Multiset.map_singleton, Multiset.sum_singleton]
  let e : Empty → D := fun _ => (by contradiction)
  convert_to sInf { z | ValuedCsp.Term.evalSolution ⟨n, f, hfΓ, Sum.inl⟩ (Sum.elim x e) = z } = f x
  · rw [Set.setOf_eq_eq_singleton']
    apply congr_arg
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, eq_c⟩
      rw [← eq_c]
      simp [ValuedCsp.Term.evalSolution]
    · intro c_is
      use e
      rw [c_is]
  simp [ValuedCsp.Term.evalSolution]

/-- Expressive power is an idempotent operation on VCSP templates. -/
lemma ValuedCsp.expressivePower_expressivePower [CompleteLattice C]
    (Γ : ValuedCsp D C) : Γ.expressivePower.expressivePower = Γ.expressivePower := by
  sorry
