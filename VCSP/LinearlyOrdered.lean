import Mathlib.Combinatorics.Optimization.ValuedCSP


variable {D C : Type*} [Nonempty D] [LinearOrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι : Type*}

-- linearity not needed here (temporary upstreaming artefact)
def glueValuedCspInstances (I₁ I₂ : Γ.Instance ι) : Γ.Instance ι :=
  (I₁ : Multiset (Γ.Term ι)) + (I₂ : Multiset (Γ.Term ι))

-- linearity not needed here (temporary upstreaming artefact)
lemma optimumSolution_glueValuedCspInstances
    {I₁ I₂ : Γ.Instance ι} {x : ι → D}
    (opt₁ : I₁.IsOptimumSolution x) (opt₂ : I₂.IsOptimumSolution x) :
    (glueValuedCspInstances I₁ I₂).IsOptimumSolution x := by
  intro y
  unfold ValuedCsp.Instance.evalSolution
  unfold glueValuedCspInstances
  rw [Multiset.map_add, Multiset.sum_add]
  rw [Multiset.map_add, Multiset.sum_add]
  exact add_le_add (opt₁ y) (opt₂ y)

/-- Condition for `x` being an optimal solution to given `Γ` instance `I` (nothing is below it).-/
def ValuedCsp.Instance.IsOptimalSolution (I : Γ.Instance ι) (x : ι → D) : Prop :=
  ¬ ∃ y : ι → D, I.evalSolution y < I.evalSolution x

lemma ValuedCsp.Instance.IsOptimumSolution.toOptimal {I : Γ.Instance ι} {x : ι → D}
    (opt : I.IsOptimumSolution x) : I.IsOptimalSolution x := by
  rintro ⟨y, contr⟩
  exact LT.lt.false (LT.lt.trans_le contr (opt y))

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
  apply optimumSolution_glueValuedCspInstances
  · exact opt₁.toOptimum
  · exact opt₂.toOptimum
