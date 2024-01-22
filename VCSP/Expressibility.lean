import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Prod.TProd


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
  let types : Multiset Type := I₁.map (fun t => by
      obtain ⟨t_n, t_f, t_inΓ, t_app⟩ := t
      rw [Set.mem_setOf_eq] at t_inΓ
      simp_rw [Sigma.mk.inj_iff] at t_inΓ
      simp_rw [exists_and_left] at t_inΓ
      rw [exists_eq_left] at t_inΓ
      exact Classical.choose t_inΓ
    )
  use types.toList.TProd id, Classical.decEq (types.toList.TProd id), sorry
  use Multiset.join (I₁.map (fun t => by
    let _n := t.n
    let _f := t.f
    let _G := t.inΓ
    let _a := t.app
    simp at _G
    let _μ := Classical.choose _G
    let _μDecEq := Classical.choose <| Classical.choose_spec _G
    let _μFintype := Classical.choose <| Classical.choose_spec <| Classical.choose_spec _G
    let _I := Classical.choose <| Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec _G
    let _ht := Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec _G
    refine _I.map ?_
    intro __t
    constructor
    · exact __t.inΓ
    refine ?_ ∘ __t.app
    sorry))
  sorry
