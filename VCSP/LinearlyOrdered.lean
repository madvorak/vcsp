import VCSP.Glue


variable {D C : Type*} [Nonempty D] [LinearOrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι : Type*}

lemma ValuedCsp.Instance.IsOptimumSolution.toOptimal {I : Γ.Instance ι} {x : ι → D}
    (opt : I.IsOptimumSolution x) : I.IsOptimalSolution x := by
  rintro ⟨y, contr⟩
  apply (contr.trans_le (opt y)).ne
  rfl

lemma ValuedCsp.Instance.IsOptimalSolution.toOptimum {I : Γ.Instance ι} {x : ι → D}
    (opt : I.IsOptimalSolution x) : I.IsOptimumSolution x := by
  intro y
  unfold ValuedCsp.Instance.IsOptimalSolution at opt
  push_neg at opt
  exact opt y

lemma optimalSolution_glueValuedCspInstances {I₁ I₂ : Γ.Instance ι} {x : ι → D}
    (opt₁ : I₁.IsOptimalSolution x) (opt₂ : I₂.IsOptimalSolution x) :
    (glueValuedCspInstances I₁ I₂).IsOptimalSolution x := by
  apply ValuedCsp.Instance.IsOptimumSolution.toOptimal
  exact optimumSolution_glueValuedCspInstances opt₁.toOptimum opt₂.toOptimum
