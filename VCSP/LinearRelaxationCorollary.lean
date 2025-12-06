import VCSP.LinearRelaxationAndSFP


variable {D ι : Type*}

def ValuedCSP.Instance.Optimum {C : Type*} [OrderedAddCommMonoid C] {Γ : ValuedCSP D C}
    (I : Γ.Instance ι) (o : C) : Prop :=
  ∃ x : ι → D, I.IsOptimumSolution x ∧ I.evalSolution x = o

variable [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι] {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

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

theorem ValuedCSP.Instance.optimum_iff_relaxBLP_minimum_of_allSymmetricFractionalPolymorphisms (I : Γ.Instance ι)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ)
    (v : ℚ) :
    I.Optimum v ↔ I.RelaxBLP.Minimum v := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact I.relaxBLP_minimum_of_allSymmetricFractionalPolymorphisms hΓ hx
  · intro ⟨hIv, hv⟩
    obtain ⟨x, hx⟩ := I.relaxBLP_improved_of_allSymmetricFractionalPolymorphisms hΓ hIv
    exact ⟨x, (hx.trans ∘ hv _ <| I.relaxBLP_reaches ·), hx.antisymm (hv _ (I.relaxBLP_reaches x))⟩

#print axioms ValuedCSP.Instance.optimum_iff_relaxBLP_minimum_of_allSymmetricFractionalPolymorphisms
