import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Notation


variable {D C : Type*}

/-- Partial evaluation of a `Γ` instance `I` for given partial solution `x` waiting for rest. -/
def ValuedCSP.Instance.evalPartial [OrderedAddCommMonoid C] {Γ : ValuedCSP D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : (μ → D) → C :=
  fun r => I.evalSolution (Sum.elim x r)

variable [Nonempty D] [Fintype D] [LinearOrderedAddCommMonoid C]

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, minimizing over the rest. -/
def ValuedCSP.Instance.evalMinimize {Γ : ValuedCSP D C} {ι μ : Type*} [DecidableEq μ] [Fintype μ]
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : C :=
  Finset.univ.inf' Finset.univ_nonempty (I.evalPartial x)

/-- Unfolding `ValuedCSP.Instance.evalMinimize` and `ValuedCSP.Instance.evalPartial` in a single step. -/
def ValuedCSP.Instance.evalMinimize_def {Γ : ValuedCSP D C} {ι μ : Type*} [DecidableEq μ] [Fintype μ]
    (I : Γ.Instance (ι ⊕ μ)):
    I.evalMinimize = (fun x => Finset.univ.inf' Finset.univ_nonempty (fun r => I.evalSolution (Sum.elim x r))) :=
  rfl

/-- A new VCSP template made of all functions expressible by `Γ`. -/
def ValuedCSP.expressivePower (Γ : ValuedCSP D C) : ValuedCSP D C :=
  { ⟨n, I.evalMinimize⟩ | (n : ℕ) (μ : Type) (_ : DecidableEq μ) (_ : Fintype μ) (I : Γ.Instance (Fin n ⊕ μ)) }

inductive ValuedCSP.expresses (Γ : ValuedCSP D C) : ValuedCSP D C
| single (n : ℕ) (f : (Fin n → D) → C) (hf : ⟨n, f⟩ ∈ Γ) : Γ.expresses ⟨n, f⟩
| double (n : ℕ) (f g : (Fin n → D) → C) (hf : Γ.expresses ⟨n, f⟩) (hg : Γ.expresses ⟨n, g⟩) :
    Γ.expresses ⟨n, f+g⟩
| minimiz (n : ℕ) (f : (Fin n.succ → D) → C) (hf : Γ.expresses ⟨n.succ, f⟩) :
    Γ.expresses ⟨n, fun x : Fin n → D => Finset.univ.inf' Finset.univ_nonempty (fun z : D => f (Matrix.vecCons z x))⟩
| remap (n m : ℕ) (f : (Fin n → D) → C) (hf : Γ.expresses ⟨n, f⟩) (τ : Fin n → Fin m) :
    Γ.expresses ⟨m, fun x : Fin m → D => f (x ∘ τ)⟩

/-- Expressive power of a VCSP template subsumes the template. NEW! -/
lemma ValuedCSP.subset_expresses (Γ : ValuedCSP D C) :
    Γ ⊆ Γ.expresses := by
  intro F hF
  apply ValuedCSP.expresses.single
  exact hF

/-- Expressive power is an idempotent operation on VCSP templates. NEW! -/
lemma ValuedCSP.expresses_expresses (Γ : ValuedCSP D C) :
    Γ.expresses = Γ.expresses.expresses := by
  apply Set.eq_of_subset_of_subset
  · apply ValuedCSP.subset_expresses
  intro F hF
  induction hF with
  | single n f hf =>
    exact hf
  | double n f g hf hg ihf ihg =>
    apply ValuedCSP.expresses.double
    · exact ihf
    · exact ihg
  | minimiz n f hf ih =>
    apply ValuedCSP.expresses.minimiz
    exact ih
  | remap n m f hf τ ih =>
    apply ValuedCSP.expresses.remap
    exact ih

/-- Expressive power of a VCSP template subsumes the template. -/
lemma ValuedCSP.subset_expressivePower (Γ : ValuedCSP D C) :
    Γ ⊆ Γ.expressivePower := by
  rintro ⟨n, f⟩ hfΓ
  unfold ValuedCSP.expressivePower
  rw [Set.mem_setOf_eq]
  use n, Empty, inferInstance, inferInstance, { ValuedCSP.Term.mk n f hfΓ Sum.inl }
  simp [ValuedCSP.Instance.evalMinimize_def, ValuedCSP.Instance.evalSolution, Term.evalSolution]

/-- Expressive power is an idempotent operation on VCSP templates. -/
lemma ValuedCSP.expressivePower_expressivePower (Γ : ValuedCSP D C) :
    Γ.expressivePower = Γ.expressivePower.expressivePower := by
  apply Set.eq_of_subset_of_subset
  · apply ValuedCSP.subset_expressivePower
  rintro ⟨n, f⟩ hnf
  simp [ValuedCSP.expressivePower] at *
  obtain ⟨μ₁, μ₁DecEq, μ₁Fintype, I₁, hI₁⟩ := hnf
  convert_to
    ∃ μ₀ : Type, ∃ μ₀DecEq : DecidableEq μ₀, ∃ μ₀Fintype : Fintype μ₀, ∃ I₀ : Instance Γ (Fin n ⊕ μ₀),
      I₀.evalMinimize = I₁.evalMinimize
  · rw [hI₁]
  clear hI₁ f
  -- `I₁` is of type `{ ⟨n, I.evalMinimize⟩ | (n' : ℕ) (μ' : Type) [...] (I : Instance Γ (Fin n' ⊕ μ')) }.Instance (Fin n ⊕ μ₁)`
  -- where `n = n'` must hold?
  sorry
