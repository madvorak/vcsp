import VCSP.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic


/-- Partial evaluation of a `Γ` instance `I` for given partial solution `m` waiting for rest. -/
def ValuedCspInstance.evalPartial {C : Type} [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCspTemplate C} {μ : Type} {ι : Type}
    (I : ValuedCspInstance Γ (μ ⊕ ι)) (m : μ → Γ.D) :
    (ι → Γ.D) → C :=
  fun x => I.evalSolution (Sum.elim m x)

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, minimizing over the rest. -/
def ValuedCspInstance.evalMinimize {C : Type} [LinearOrderedAddCommMonoid C] [CompleteLattice C]
    {Γ : ValuedCspTemplate C} {μ : Type} {ι : Type}
    (I : ValuedCspInstance Γ (μ ⊕ ι)) (x : ι → Γ.D) : C :=
  sInf { z | ∃ m : μ → Γ.D, I.evalPartial m x = z }

/-- Function expressed by a `Γ` instance `I` exposing `n` free variables via bijection `θ`. -/
def ValuedCspInstance.expresses {C : Type} [LinearOrderedAddCommMonoid C] [CompleteLattice C]
    {Γ : ValuedCspTemplate C} {μ : Type} {n : ℕ}
    (I : ValuedCspInstance Γ (μ ⊕ Fin n)) :
    Σ (k : ℕ), (Fin k → Γ.D) → C :=
  ⟨n, I.evalMinimize⟩

/-- Set of functions expressible by `Γ`. -/
def ValuedCspTemplate.canExpress {C : Type} [LinearOrderedAddCommMonoid C] [CompleteLattice C]
    (Γ : ValuedCspTemplate C) : Set (Σ (k : ℕ), (Fin k → Γ.D) → C) :=
  { f | ∃ μ : Type, ∃ n : ℕ, ∃ I : ValuedCspInstance Γ (μ ⊕ Fin n), I.expresses = f }

/-- Closure of a valued CSP template `Γ` under expressibility. -/
def ValuedCspTemplate.closure {C : Type} [LinearOrderedAddCommMonoid C] [CompleteLattice C]
    (Γ : ValuedCspTemplate C) : ValuedCspTemplate C :=
  ⟨Γ.D, Γ.canExpress⟩

lemma ValuedCspTemplate.closure_ok {C : Type} [LinearOrderedAddCommMonoid C] [CompleteLattice C]
    (Γ : ValuedCspTemplate C) : Γ.F ⊆ (Γ.closure).F := by
  rintro ⟨k, f⟩ fin
  unfold ValuedCspTemplate.closure
  unfold ValuedCspTemplate.canExpress
  rw [Set.mem_setOf_eq]
  use Empty, k
  use [ValuedCspTerm.mk k f fin Sum.inr]
  unfold ValuedCspInstance.expresses
  simp [ValuedCspInstance.evalMinimize, ValuedCspInstance.evalPartial]
  ext x
  unfold ValuedCspInstance.evalSolution
  simp_rw [List.map_singleton, List.sum_singleton]
  let e : Empty → Γ.D := fun _ => (by contradiction)
  convert_to sInf {z | ValuedCspTerm.evalSolution ⟨k, f, fin, Sum.inr⟩ (Sum.elim e x) = z} = f x
  · rw [Set.setOf_eq_eq_singleton']
    apply congr_arg
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, eq_c⟩
      rw [←eq_c]
      apply congr_arg
      apply congr_fun
      apply congr_arg
      rw [eq_iff_true_of_subsingleton]
      exact trivial
    · intro c_is
      use e
      rw [c_is]
  rw [Set.setOf_eq_eq_singleton', sInf_singleton]
  rfl

lemma ValuedCspTemplate.closure_closure {C : Type} [LinearOrderedAddCommMonoid C] [CompleteLinearOrder C]
    (Γ : ValuedCspTemplate C) : Γ.closure.closure = Γ.closure := by
  simp [ValuedCspTemplate.closure]
  sorry
