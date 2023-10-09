import VCSP.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic


/-- Partial evaluation of a `Γ` instance `I` for given partial solution `x` waiting for rest. -/
def ValuedCspInstance.evalPartial {D C : Type} [Nonempty D] [OrderedAddCommMonoid C]
    {Γ : ValuedCspTemplate D C} {ι : Type} {μ : Type}
    (I : ValuedCspInstance Γ (ι ⊕ μ)) (x : ι → D) :
    (μ → D) → C :=
  fun r => I.evalSolution (Sum.elim x r)

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, minimizing over the rest. -/
def ValuedCspInstance.evalMinimize {D C : Type} [Nonempty D] [OrderedAddCommMonoid C] [InfSet C]
    {Γ : ValuedCspTemplate D C} {ι : Type} {μ : Type}
    (I : ValuedCspInstance Γ (ι ⊕ μ)) (x : ι → D) : C :=
  sInf { z | ∃ m : μ → D, I.evalPartial x m = z }

-- Problem: `[InfSet C]` is not guaranteed to respect `≤` given by `[OrderedAddCommMonoid C]`
-- Eric Wieser suggests: `[CompleteLattice C] [AddCommMonoid C] [CovariantClass C C (· + ·) (· ≤ ·)]`

/-- Function expressed by a `Γ` instance `I` exposing `n` free variables. -/
def ValuedCspInstance.expresses {D C : Type} [Nonempty D] [OrderedAddCommMonoid C] [InfSet C]
    {Γ : ValuedCspTemplate D C} {n : ℕ} {μ : Type} (I : ValuedCspInstance Γ (Fin n ⊕ μ)) :
    Σ (k : ℕ), (Fin k → D) → C :=
  ⟨n, I.evalMinimize⟩

/-- A new VCSP template made of all functions expressible by `Γ`. -/
def ValuedCspTemplate.expressivePower {D C : Type} [Nonempty D] [OrderedAddCommMonoid C] [InfSet C]
    (Γ : ValuedCspTemplate D C) : ValuedCspTemplate D C :=
  { f : Σ (k : ℕ), (Fin k → D) → C | ∃ k : ℕ, ∃ μ : Type, ∃ I : ValuedCspInstance Γ (Fin k ⊕ μ), I.expresses = f }

/-- Expressive power of a VCSP template subsumes the template. -/
lemma ValuedCspTemplate.subset_expressivePower_self {D C : Type}
    [Nonempty D] [OrderedAddCommMonoid C] [CompleteLattice C]
    (Γ : ValuedCspTemplate D C) : Γ ⊆ Γ.expressivePower := by
  rintro ⟨k, f⟩ fin
  unfold ValuedCspTemplate.expressivePower
  rw [Set.mem_setOf_eq]
  use k, Empty
  use [ValuedCspTerm.mk k f fin Sum.inl]
  unfold ValuedCspInstance.expresses
  simp [ValuedCspInstance.evalMinimize, ValuedCspInstance.evalPartial]
  ext x
  unfold ValuedCspInstance.evalSolution
  simp_rw [List.map_singleton, List.sum_singleton]
  let e : Empty → D := fun _ => (by contradiction)
  convert_to sInf {z | ValuedCspTerm.evalSolution ⟨k, f, fin, Sum.inl⟩ (Sum.elim x e) = z} = f x
  · rw [Set.setOf_eq_eq_singleton']
    apply congr_arg
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, eq_c⟩
      rw [←eq_c]
      simp [ValuedCspTerm.evalSolution]
    · intro c_is
      use e
      rw [c_is]
  simp [ValuedCspTerm.evalSolution] -- works with `CompleteLinearOrder` or `CompleteLattice`
  -- but not with `InfSet` or `CompleteSemilatticeInf`

/-- Expressive power is an idempotent operation on VCSP templates. -/
lemma ValuedCspTemplate.expressivePower_expressivePower {D C : Type}
    [Nonempty D] [OrderedAddCommMonoid C] [CompleteLattice C]
    (Γ : ValuedCspTemplate D C) : Γ.expressivePower.expressivePower = Γ.expressivePower := by
  sorry
