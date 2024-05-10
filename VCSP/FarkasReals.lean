import VCSP.FarkasLemmas
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation


open scoped Matrix
variable {I J : Type*} [Fintype I] [Fintype J]


lemma equalityFarkas [LocallyConvexSpace ℝ (I → ℝ)] (A : Matrix I J ℝ) (b : I → ℝ) :
    (∃ x : J → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ∨ (∃ y : I → ℝ, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  if hx : (∃ x : J → ℝ, 0 ≤ x ∧ A *ᵥ x = b) then
    left
    exact hx
  else
    let s := { A *ᵥ x | (x : J → ℝ) (xnn : 0 ≤ x) }
    have hsco : Convex ℝ s
    · intro p ⟨xₚ, hxₚ, hp⟩ r ⟨xᵣ, hxᵣ, hr⟩ c d hc hd hcd
      use c • xₚ + d • xᵣ
      constructor
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hp, Matrix.mulVec_smul, hr]
      · have hcxₚ : 0 ≤ c • xₚ
        · rw [←smul_zero c]
          exact smul_le_smul (by rfl) hxₚ hc hxₚ
        have hdxᵣ : 0 ≤ d • xᵣ
        · rw [←smul_zero d]
          exact smul_le_smul (by rfl) hxᵣ hd hxᵣ
        convert_to 0 + 0 ≤ c • xₚ + d • xᵣ
        · rw [add_zero]
        exact add_le_add hcxₚ hdxᵣ
    have hscl : IsClosed s
    · sorry
    have hbs : b ∉ s
    · intro contr
      apply hx
      simpa [s] using contr
    obtain ⟨f, u, hfs, hfb⟩ := geometric_hahn_banach_closed_point hsco hscl hbs
    right
    sorry

lemma hardFarkas (A : Matrix I J ℝ) (b : I → ℝ) :
    (∃ x : J → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ∨ (∃ y : I → ℝ, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  sorry

lemma one_holds {P Q : Prop} (hpos : P ∨ Q) (hneg : P ∧ Q → False) : P ≠ Q := by
  tauto

theorem realFarkas (A : Matrix I J ℝ) (b : I → ℝ) :
    (∃ x : J → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → ℝ, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) :=
  one_holds (hardFarkas A b) (easyFarkas A b)
