import VCSP.Definition

variable {D C ι : Type} [Nonempty D] [LinearOrderedAddCommMonoid C] {Γ : ValuedCspTemplate D C}

lemma ValuedCspInstance.glue_optimalSolutions
    {I₁ I₂ : ValuedCspInstance Γ ι} {x : ι → D}
    (opt₁ : I₁.OptimalSolution x) (opt₂ : I₂.OptimalSolution x) :
    (glueValuedCspInstances I₁ I₂).OptimalSolution x := by
  rintro ⟨y, contr⟩
  unfold ValuedCspInstance.OptimalSolution at opt₁ opt₂
  push_neg at opt₁ opt₂
  specialize opt₁ y
  specialize opt₂ y
  push_neg at opt₁ opt₂
  unfold ValuedCspInstance.evalSolution at opt₁ opt₂ contr
  unfold glueValuedCspInstances at contr
  rw [List.map_append', List.sum_append] at contr
  rw [List.map_append', List.sum_append] at contr
  set a₁ := List.sum (List.map (fun t => ValuedCspTerm.evalSolution t y) I₁)
  set a₂ := List.sum (List.map (fun t => ValuedCspTerm.evalSolution t y) I₂)
  set b₁ := List.sum (List.map (fun t => ValuedCspTerm.evalSolution t x) I₁)
  set b₂ := List.sum (List.map (fun t => ValuedCspTerm.evalSolution t x) I₂)
  have half_there : a₁ + a₂ < a₁ + b₂
  · exact lt_add_of_lt_add_right contr opt₁ -- stupid approach
  have impossibru : a₁ + a₂ < a₁ + a₂
  · exact lt_add_of_lt_add_left half_there opt₂ -- stupid approach
  exact LT.lt.false impossibru

lemma ValuedCspInstance.OptimalSolution.toOptimum {I : ValuedCspInstance Γ ι} {x : ι → D}
    (opt : I.OptimalSolution x) : I.OptimumSolution x := by
  intro y
  unfold ValuedCspInstance.OptimalSolution at opt
  push_neg at opt
  exact opt y

lemma ValuedCspInstance.glue_optimalSolutions'
    {I₁ I₂ : ValuedCspInstance Γ ι} {x : ι → D}
    (opt₁ : I₁.OptimalSolution x) (opt₂ : I₂.OptimalSolution x) :
    (glueValuedCspInstances I₁ I₂).OptimalSolution x := by
  apply ValuedCspInstance.OptimumSolution.toOptimal
  apply ValuedCspInstance.glue_optimumSolutions
  · exact opt₁.toOptimum
  · exact opt₂.toOptimum
