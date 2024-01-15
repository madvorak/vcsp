import VCSP.FilterValued
import VCSP.Hardness

attribute [pp_dot]
  FilterValuedCSP.Term.f FilterValuedCSP.Term.n FilterValuedCSP.Term.app FilterValuedCSP.Term.evalSolution
  FilterValuedCSP.Instance.evalSolution FilterValuedCSP.Instance.evalPartial FilterValuedCSP.Instance.evalMinimize
  Function.AdmitsFilterFractional FilterValuedCSP.expressivePower FilterValuedCSP.closure


variable {D C : Type*} [CanonicallyOrderedAddCancelCommMonoid C]

/-- Expressive power of a filter-valued CSP template subsumes the template. -/
lemma FilterValuedCSP.subset_expressivePower (Γ : FilterValuedCSP D C) :
    Γ ⊆ Γ.expressivePower := by
  rintro ⟨n, f⟩ hfΓ
  unfold FilterValuedCSP.expressivePower
  rw [Set.mem_setOf_eq]
  use n, 0, { FilterValuedCSP.Term.mk n f hfΓ Sum.inl }
  unfold FilterValuedCSP.Instance.evalMinimize
  unfold FilterValuedCSP.Instance.evalPartial
  unfold FilterValuedCSP.Instance.evalSolution
  sorry

/-- Expressive power is an idempotent operation on filter-valued CSP templates. -/
lemma FilterValuedCSP.expressivePower_expressivePower (Γ : FilterValuedCSP D C) :
    Γ.expressivePower = Γ.expressivePower.expressivePower := by
  apply Set.eq_of_subset_of_subset
  · apply FilterValuedCSP.subset_expressivePower
  rintro ⟨n, f⟩ hnf
  sorry

lemma todo (Γ : FilterValuedCSP D C) :
    Γ.expressivePower.allFractionalPolymorphisms = Γ.allFractionalPolymorphisms := by
  apply Set.eq_of_subset_of_subset <;> intro ⟨m, ω⟩ hyp <;>
      rw [FilterValuedCSP.allFractionalPolymorphisms_mem] at hyp ⊢ <;> intro f fin
  · apply FilterValuedCSP.subset_expressivePower at fin
    exact hyp f fin
  sorry

theorem conjectureFEP (Γ : FilterValuedCSP D C) : Γ.closure = Γ.expressivePower := by
  sorry
