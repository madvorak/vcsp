import VCSP.AlgebraInst
import VCSP.Hardness


theorem ValuedCsp.CanExpressMaxCut.forbids_commutativeFP' {D C : Type*}
    [OrderedCancelAddCommMonoidWithInfima C]
    {Γ : ValuedCsp D C} (expressMC : Γ.CanExpressMaxCut)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) :
    ¬ ω.IsSymmetricFractionalPolymorphismFor Γ := by
  intro _
  obtain ⟨f, -, a, b, hab, hfab, hyp⟩ := expressMC
  refine fuck ⟨f ![a, b], f ![a, a], ?less⟩
  obtain ⟨fable, fabne⟩ := hyp a a
  apply lt_of_le_of_ne fable
  intro contr
  cases fabne contr <;> tauto
