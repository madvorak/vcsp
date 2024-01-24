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

inductive ValuedCSP.expresses (Γ : ValuedCSP D C) : (Σ α : Type, (α → D) → C) → Prop
| single (n : ℕ) (f : (Fin n → D) → C) (hf : ⟨n, f⟩ ∈ Γ) : Γ.expresses ⟨Fin n, f⟩
| double (α : Type) (f g : (α → D) → C) (hf : Γ.expresses ⟨α, f⟩) (hg : Γ.expresses ⟨α, g⟩) :
    Γ.expresses ⟨α, f + g⟩
| minimi (α β : Type) [Fintype β] [DecidableEq β] (f : (α ⊕ β → D) → C) (hf : Γ.expresses ⟨α ⊕ β, f⟩) :
    Γ.expresses ⟨α, fun x : α → D => Finset.univ.inf' Finset.univ_nonempty (fun z : β → D => f (Sum.elim x z))⟩
| remap (α ι : Type) (f : (α → D) → C) (hf : Γ.expresses ⟨α, f⟩) (τ : α → ι) :
    Γ.expresses ⟨ι, fun x : ι → D => f (x ∘ τ)⟩

def ValuedCSP.expressesPower (Γ : ValuedCSP D C) : ValuedCSP D C :=
  { f : Σ (n : ℕ), (Fin n → D) → C | Γ.expresses ⟨Fin f.fst, f.snd⟩ }

/-- Expressive power of a VCSP template subsumes the template. NEW! -/
lemma ValuedCSP.subset_expressesPower (Γ : ValuedCSP D C) :
    Γ ⊆ Γ.expressesPower := by
  rintro ⟨n, f⟩ hfΓ
  apply ValuedCSP.expresses.single
  exact hfΓ

/-- Expressive power is an idempotent operation on VCSP templates. NEW! -/
lemma ValuedCSP.expressesPower_expressesPower (Γ : ValuedCSP D C) :
    Γ.expressesPower = Γ.expressesPower.expressesPower := by
  apply Set.eq_of_subset_of_subset
  · apply ValuedCSP.subset_expressesPower
  rintro ⟨n, f⟩ hnf
  sorry  /-
  simp only [ValuedCSP.expressesPower, Set.mem_setOf_eq] at hnf
  induction hnf with
  | single n f hf => sorry
  | double α f g hf hg hf_ih hg_ih => sorry
  | minimi α β f hf ih => sorry
  | remap α ι f hf τ ih => sorry
  -/

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
