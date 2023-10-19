import VCSP.Definition

variable {D C ι : Type} [Nonempty D] [LinearOrderedAddCommMonoid C] {Γ : ValuedCspTemplate D C}

lemma ValuedCspInstance.OptimalSolution.toOptimum {I : ValuedCspInstance Γ ι} {x : ι → D}
    (opt : I.OptimalSolution x) : I.OptimumSolution x := by
  intro y
  unfold ValuedCspInstance.OptimalSolution at opt
  push_neg at opt
  exact opt y

lemma optimalSolution_glueValuedCspInstances
    {I₁ I₂ : ValuedCspInstance Γ ι} {x : ι → D}
    (opt₁ : I₁.OptimalSolution x) (opt₂ : I₂.OptimalSolution x) :
    (glueValuedCspInstances I₁ I₂).OptimalSolution x := by
  apply ValuedCspInstance.OptimumSolution.toOptimal
  apply optimumSolution_glueValuedCspInstances
  · exact opt₁.toOptimum
  · exact opt₂.toOptimum
