import Mathlib.Algebra.Order.Group.Finset
import VCSP.Basic
import VCSP.Expressibility


variable {D C : Type*} [Nonempty D] [Fintype D]

lemma FractionalOperation.IsFractionalPolymorphismFor.expressesVCSP [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCSP D C} {m : ℕ} {ω : FractionalOperation D m}
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expresses := by
  intro F hF
  induction hF with
  | single hf =>
    apply frpo
    exact hf
  | double _ _ ihf ihg =>
    intro x
    have summed := add_le_add (ihf x) (ihg x)
    rw [
      Finset.smul_sum, Finset.smul_sum, ←Finset.sum_add_distrib,
      Multiset.nsmul_summap, Multiset.nsmul_summap, ←Multiset.sum_map_add
    ] at summed
    rw [Finset.smul_sum, Multiset.nsmul_summap]
    convert summed using 2 <;> simp
  | @minimize n f _ ih =>
    intro x
    rw [Multiset.nsmul_summap, Finset.smul_sum]
    simp_rw [Finset.nsmul_inf']
    let z :=
      fun i : Fin m =>
        (Finset.exists_mem_eq_inf' Finset.univ_nonempty
          (fun d : D => ω.size • f (Matrix.vecCons d (x i)))
        ).choose
    specialize ih (fun i j => Matrix.vecCons (z i) (x i) j)
    rw [Multiset.nsmul_summap, Finset.smul_sum] at ih
    convert_to
      (ω.tt x).summap (fun yᵢ : Fin n → D =>
        Finset.univ.inf' Finset.univ_nonempty (fun zᵢ : D => m • f (Matrix.vecCons zᵢ yᵢ))) ≤
      Finset.univ.val.summap (fun i : Fin m =>
        ω.size • f (fun j : Fin n.succ => Matrix.vecCons (z i) (x i) j))
    · congr
      ext i
      exact (Finset.exists_mem_eq_inf' Finset.univ_nonempty _).choose_spec.right
    refine LE.le.trans ?_ ih
    simp_rw [Multiset.summap, FractionalOperation.tt, Multiset.map_map, Function.comp_apply]
    apply Multiset.summap_le_summap
    intro g _
    rw [←Finset.nsmul_inf']
    apply nsmul_le_nsmul_right
    simp only [Finset.inf'_le_iff, Finset.mem_univ, true_and]
    use g z
    apply le_of_eq
    apply congr_arg
    ext i
    match i with
    | 0 => rfl
    | ⟨i'+1, _⟩ => rfl
  | remap _ τ ih =>
    intro x
    specialize ih (fun i j => x i (τ j))
    convert ih using 3
    unfold FractionalOperation.tt
    rewrite [Multiset.map_map, Multiset.map_map]
    rfl

/-- VCSP template `Γ` can express Max Cut via summation and minimization. -/
def ValuedCSP.CanExpressMaxCut [LinearOrderedAddCommMonoid C] (Γ : ValuedCSP D C) : Prop :=
  ∃ f : (Fin 2 → D) → C, ⟨2, f⟩ ∈ Γ.expresses ∧ f.HasMaxCutProperty

theorem ValuedCSP.CanExpressMaxCut.forbids_commutativeFractionalPolymorphism
    [LinearOrderedCancelAddCommMonoid C]
    {Γ : ValuedCSP D C} (expressMC : Γ.CanExpressMaxCut)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) :
    ¬ ω.IsSymmetricFractionalPolymorphismFor Γ := by
  intro ⟨frpol, symme⟩
  obtain ⟨f, fin, fmc⟩ := expressMC
  apply fmc.forbids_commutativeFractionalPolymorphism valid symme
  exact frpol.expressesVCSP ⟨2, f⟩ fin

#print axioms ValuedCSP.CanExpressMaxCut.forbids_commutativeFractionalPolymorphism
