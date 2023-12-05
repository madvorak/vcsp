import Mathlib.Combinatorics.Optimization.ValuedCSP
import VCSP.AlgebraC


variable {D C : Type*}

/-- Partial evaluation of a `Γ` instance `I` for given partial solution `x` waiting for rest. -/
def ValuedCsp.Instance.evalPartial [OrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : (μ → D) → C :=
  fun r => I.evalSolution (Sum.elim x r)

variable [OrderedAddCommMonoidWithInfima C]

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, minimizing over the rest. -/
def ValuedCsp.Instance.evalMinimize {Γ : ValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : C :=
  sInf { I.evalPartial x y | y : μ → D }

/-- Function expressed by a `Γ` instance `I` exposing `m` free variables. -/
def ValuedCsp.Instance.expresses {Γ : ValuedCsp D C} {m : ℕ} {μ : Type*} (I : Γ.Instance (Fin m ⊕ μ)) :
    Σ (n : ℕ), (Fin n → D) → C :=
  ⟨m, I.evalMinimize⟩

/-- A new VCSP template made of all functions expressible by `Γ`. -/
def ValuedCsp.expressivePower (Γ : ValuedCsp D C) : ValuedCsp D C :=
  { ValuedCsp.Instance.expresses I | (m : ℕ) (μ : Type) (I : Γ.Instance (Fin m ⊕ μ)) }

/-- Expressive power of a VCSP template subsumes the template. -/
lemma ValuedCsp.subset_expressivePower (Γ : ValuedCsp D C) :
    Γ ⊆ Γ.expressivePower := by
  rintro ⟨n, f⟩ hfΓ
  unfold ValuedCsp.expressivePower
  rw [Set.mem_setOf_eq]
  use n, Empty
  unfold ValuedCsp.Instance
  use {ValuedCsp.Term.mk n f hfΓ Sum.inl}
  unfold ValuedCsp.Instance.expresses
  unfold ValuedCsp.Instance.evalMinimize
  unfold ValuedCsp.Instance.evalPartial
  rw [Sigma.mk.inj_iff, heq_eq_eq]
  constructor
  · rfl
  ext x
  unfold ValuedCsp.Instance.evalSolution
  simp_rw [Multiset.map_singleton, Multiset.sum_singleton]
  convert sInf_singleton
  apply Set.eq_of_subset_of_subset
  · simp [ValuedCsp.Term.evalSolution]
  · intro c c_is
    rw [Set.mem_singleton_iff] at c_is
    rw [c_is]
    exact ⟨fun _ => by contradiction, rfl⟩

/-- Expressive power is an idempotent operation on VCSP templates. -/
lemma ValuedCsp.expressivePower_expressivePower (Γ : ValuedCsp D C) :
    Γ.expressivePower = Γ.expressivePower.expressivePower := by
  apply Set.eq_of_subset_of_subset
  · apply ValuedCsp.subset_expressivePower
  rintro ⟨n, f⟩ hnf
  show
    ∃ m : ℕ, ∃ μ : Type, ∃ I : Γ.Instance                 (Fin m ⊕ μ), I.expresses = ⟨n, f⟩
  obtain ⟨mₑ, μₑ, Iₑ, hyp⟩ :
    ∃ m : ℕ, ∃ μ : Type, ∃ I : Γ.expressivePower.Instance (Fin m ⊕ μ), I.expresses = ⟨n, f⟩
    := hnf
  sorry
