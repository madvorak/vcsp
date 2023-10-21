import VCSP.Expressibility
import VCSP.FractionalPolymorphisms

lemma fractionalPolymorphism_expressivePower {D C : Type} {m k : ℕ}
    [Nonempty D] [OrderedAddCommMonoid C] [CompleteLattice C]
    {ω : FractionalOperation D m k} {Γ : ValuedCspTemplate D C}
    (frop : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expressivePower := by
  intro f hf
  simp only [ValuedCspTemplate.expressivePower, Set.mem_setOf_eq] at hf
  rcases hf with ⟨q, μ, I, rfl⟩
  simp only [ValuedCspInstance.expresses, ValuedCspInstance.evalMinimize]
  intro x
  simp only [ValuedCspInstance.evalPartial, ValuedCspInstance.evalSolution]
  convert_to
      List.sum (List.map (m • ·)
        (List.map
          ((fun x => sInf {z | ∃ y, List.sum (List.map (fun t => ValuedCspTerm.evalSolution t (Sum.elim x y)) I) = z}) ∘
            FractionalOperation.tt ω x)
          (List.finRange k))) ≤
    k •
      List.sum
        (List.map
          ((fun x => sInf {z | ∃ y, List.sum (List.map (fun t => ValuedCspTerm.evalSolution t (Sum.elim x y)) I) = z}) ∘
            x)
          (List.finRange m))
  · sorry
  · sorry
  sorry

def Function.HasMaxCutPropertyAt {D C : Type} [OrderedAddCommMonoid C]
    (f : (Fin 2 → D) → C) (a b : D) : Prop := -- `argmin f` is exactly `{ ![a, b], ![b, a] }`
  f ![a, b] = f ![b, a] ∧ ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

def Function.HasMaxCutProperty {D C : Type} [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, f.HasMaxCutPropertyAt a b

theorem Function.HasMaxCutProperty.forbids_symmetric {D C : Type} [OrderedAddCommMonoid C]
    {m k : ℕ} {f : (Fin 2 → D) → C} {ω : FractionalOperation D m k}
    (mcf : f.HasMaxCutProperty) (omega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  sorry
