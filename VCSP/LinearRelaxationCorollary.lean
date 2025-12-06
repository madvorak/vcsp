import VCSP.LinearRelaxationAndSFP

variable {D : Type*} [Fintype D]
-- TODO refactor
variable [DecidableEq D] {ι : Type*} [Fintype ι] [DecidableEq ι] {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

lemma ValuedCSP.Instance.isOptimumSolution_of_relaxBLP_minimum (I : Γ.Instance ι)
    {x : ι → D} (hx : I.RelaxBLP.Minimum (I.evalSolution x)) :
    I.IsOptimumSolution x :=
  (hx.right _ <| I.relaxBLP_reaches ·)

lemma ValuedCSP.Instance.relaxBLP_minimum_of_allSymmetricFractionalPolymorphisms (I : Γ.Instance ι)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ)
    {x : ι → D} (hx : I.IsOptimumSolution x) :
    I.RelaxBLP.Minimum (I.evalSolution x) := by
  constructor
  · exact I.relaxBLP_reaches x
  · intro r hIr
    obtain ⟨y, hyr⟩ := I.relaxBLP_improved_of_allSymmetricFractionalPolymorphisms hΓ hIr
    by_contra! hxr
    exact (((hx y).trans hyr).trans_lt hxr).false

theorem ValuedCSP.Instance.isOptimumSolution_iff_of_allSymmetricFractionalPolymorphisms (I : Γ.Instance ι)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ)
    (x : ι → D) :
    I.IsOptimumSolution x ↔ I.RelaxBLP.Minimum (I.evalSolution x) :=
  ⟨I.relaxBLP_minimum_of_allSymmetricFractionalPolymorphisms hΓ, I.isOptimumSolution_of_relaxBLP_minimum⟩

#print axioms ValuedCSP.Instance.isOptimumSolution_iff_of_allSymmetricFractionalPolymorphisms
