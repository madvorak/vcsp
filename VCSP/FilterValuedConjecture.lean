import VCSP.FilterValued
import VCSP.Hardness

attribute [pp_dot]
  FilterValuedCsp.Term.f FilterValuedCsp.Term.n FilterValuedCsp.Term.app FilterValuedCsp.Term.evalSolution
  FilterValuedCsp.Instance.evalSolution FilterValuedCsp.Instance.evalPartial FilterValuedCsp.Instance.evalMinimize
  Function.AdmitsFilterFractional FilterValuedCsp.expressivePower FilterValuedCsp.closure


variable {D C : Type*} [CanonicallyOrderedAddCancelCommMonoid C]

/-- Expressive power of a filter-valued CSP template subsumes the template. -/
lemma FilterValuedCsp.subset_expressivePower (Γ : FilterValuedCsp D C) :
    Γ ⊆ Γ.expressivePower := by
  rintro ⟨n, f⟩ hfΓ
  unfold FilterValuedCsp.expressivePower
  rw [Set.mem_setOf_eq]
  use n, 0, { FilterValuedCsp.Term.mk n f hfΓ Sum.inl }
  unfold FilterValuedCsp.Instance.evalMinimize
  unfold FilterValuedCsp.Instance.evalPartial
  unfold FilterValuedCsp.Instance.evalSolution
  sorry

/-- Expressive power is an idempotent operation on filter-valued CSP templates. -/
lemma FilterValuedCsp.expressivePower_expressivePower (Γ : FilterValuedCsp D C) :
    Γ.expressivePower = Γ.expressivePower.expressivePower := by
  apply Set.eq_of_subset_of_subset
  · apply FilterValuedCsp.subset_expressivePower
  rintro ⟨n, f⟩ hnf
  sorry

lemma todo (Γ : FilterValuedCsp D C) :
    Γ.expressivePower.allFractionalPolymorphisms = Γ.allFractionalPolymorphisms := by
  apply Set.eq_of_subset_of_subset <;> intro ⟨m, ω⟩ hyp <;>
      rw [FilterValuedCsp.allFractionalPolymorphisms_mem] at hyp ⊢ <;> intro f fin
  · apply FilterValuedCsp.subset_expressivePower at fin
    exact hyp f fin
  sorry

theorem conjectureFEP (Γ : FilterValuedCsp D C) : Γ.closure = Γ.expressivePower := by
  sorry
