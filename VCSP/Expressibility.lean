import Mathlib.Combinatorics.Optimization.ValuedCSP


variable {D C : Type*} [Nonempty D] [Fintype D] [LinearOrderedAddCommMonoid C]

/-- Expressive power of a VCSP template. -/
inductive ValuedCSP.expresses (Γ : ValuedCSP D C) : ValuedCSP D C
| single {n : ℕ} {f : (Fin n → D) → C} (hf : ⟨n, f⟩ ∈ Γ) :
    Γ.expresses ⟨n, f⟩
| double {n : ℕ} {f g : (Fin n → D) → C} (hf : Γ.expresses ⟨n, f⟩) (hg : Γ.expresses ⟨n, g⟩) :
    Γ.expresses ⟨n, f+g⟩
| minimize {n : ℕ} {f : (Fin n.succ → D) → C} (hf : Γ.expresses ⟨n.succ, f⟩) :
    Γ.expresses ⟨n, fun x : Fin n → D => Finset.univ.inf' Finset.univ_nonempty (fun z : D => f (Matrix.vecCons z x))⟩
| remap {n m : ℕ} {f : (Fin n → D) → C} (hf : Γ.expresses ⟨n, f⟩) (τ : Fin n → Fin m) :
    Γ.expresses ⟨m, fun x : Fin m → D => f (x ∘ τ)⟩

/-- Expressive power of a VCSP template subsumes the template. -/
lemma ValuedCSP.subset_expresses (Γ : ValuedCSP D C) :
    Γ ⊆ Γ.expresses := by
  intro F hF
  exact ValuedCSP.expresses.single hF

/-- Expressive power is an idempotent operation on VCSP templates. -/
lemma ValuedCSP.expresses_expresses (Γ : ValuedCSP D C) :
    Γ.expresses = Γ.expresses.expresses := by
  apply Set.eq_of_subset_of_subset
  · apply ValuedCSP.subset_expresses
  intro F hF
  induction hF with
  | single hf => exact hf
  | double _ _ ihf ihg => exact ValuedCSP.expresses.double ihf ihg
  | minimize _ ih => exact ValuedCSP.expresses.minimize ih
  | remap _ τ ih => exact ValuedCSP.expresses.remap ih τ
