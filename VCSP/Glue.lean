import Mathlib.Combinatorics.Optimization.ValuedCSP


variable {D C : Type*} [OrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι : Type*}

def glueValuedCspInstances (I₁ I₂ : Γ.Instance ι) : Γ.Instance ι :=
  -- here `+` means the same as `∪` or `++` but for multisets instead of sets or lists
  ((I₁ : Multiset (Γ.Term ι)) + (I₂ : Multiset (Γ.Term ι)))

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

/-- Condition for `x` being an optimal solution to given `Γ` instance `I` (nothing is below it). -/
def ValuedCsp.Instance.IsOptimalSolution (I : Γ.Instance ι) (x : ι → D) : Prop :=
  ¬ ∃ y : ι → D, I.evalSolution y < I.evalSolution x
