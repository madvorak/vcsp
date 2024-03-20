import VCSP.LinearRelaxation
import VCSP.LinearProgrammingQ


lemma Sum.elim_eq_left {α β γ : Type*} {u u' : α → γ} {v v' : β → γ}
    (huv : Sum.elim u v = Sum.elim u' v') :
    u = u' := by
  simp_all [Function.funext_iff]

lemma Sum.elim_eq_right {α β γ : Type*} {u u' : α → γ} {v v' : β → γ}
    (huv : Sum.elim u v = Sum.elim u' v') :
    v = v' := by
  simp_all [Function.funext_iff]

-- Yaël Dillies proved this lemma:
lemma Multiset.toList_map_sum {α β : Type*} (s : Multiset α) [AddCommMonoid β] (f : α → β) :
    (s.toList.map f).sum = (s.map f).sum := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]

lemma Finset.sum_of_sum_div_const_eq_one {α β : Type*} [Fintype α] [Semifield β] {f : α → β} {z : β}
    (hfz : Finset.univ.sum (fun a => f a / z) = (1 : β)) :
    Finset.univ.sum f = z := by
  if hz : z = 0 then
    exfalso
    simp_rw [hz, div_zero, Finset.sum_const_zero, zero_ne_one] at hfz
  else
    have mul_one_div_zet : Finset.univ.sum f * (1/z) = z * (1/z)
    · convert hfz
      · simp_rw [Finset.sum_mul, mul_one_div]
      · simp [hz]
    rw [mul_eq_mul_right_iff] at mul_one_div_zet
    cases mul_one_div_zet with
    | inl hyp => exact hyp
    | inr hyp =>
      exfalso
      rw [one_div, inv_eq_zero] at hyp
      exact hz hyp


variable {D : Type} [Fintype D]

private noncomputable abbrev buildColumn (r : D → ℕ) : List D :=
  (Finset.univ.val.toList.map (fun d : D => List.replicate (r d) d)).join

open scoped Matrix
variable [DecidableEq D] {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

lemma ValuedCSP.Instance.RelaxBLP_denominator_eq_height (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (x_solv : I.RelaxBLP.A *ᵥ x.toCanonicalRationalSolution.toFunction = I.RelaxBLP.b)
    (j : ι) :
    x.toCanonicalRationalSolution.denominator =
    (buildColumn (fun d : D => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨j, d⟩))).length := by
  rw [List.length_join, List.map_map, Function.comp]
  simp_rw [List.length_replicate, Multiset.toList_map_sum]
  qify
  rw [Multiset.map_map, Multiset.map_map]
  simp_rw [Function.comp_apply, Int.cast_ofNat, Finset.sum_map_val]
  have eqv := congr_fun x_solv (Sum.inr j)
  simp_rw [
    ValuedCSP.Instance.RelaxBLP, Sum.elim_inr,
    Matrix.fromBlocks_mulVec, Sum.elim_inr,
    Matrix.zero_mulVec, zero_add,
    Matrix.mulVec, Matrix.of_apply, Matrix.dotProduct,
    Function.comp_apply, ite_mul, one_mul, zero_mul, Fintype.sum_prod_type
  ] at eqv
  rw [Finset.sum_comm] at eqv -- must not be used in `simp_rw` (cycling forever)
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true] at eqv
  exact (Finset.sum_of_sum_div_const_eq_one eqv).symm

lemma ValuedCSP.Instance.RelaxBLP_improved_by_isSymmetricFractionalPolymorphism (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (x_solu : CanonicalLP.IsSolution I.RelaxBLP x) -- TODO probably delete and use `x_solv`
    (x_solv : I.RelaxBLP.A *ᵥ x.toCanonicalRationalSolution.toFunction = I.RelaxBLP.b)
    {ω : FractionalOperation D x.toCanonicalRationalSolution.denominator}
    (valid : FractionalOperation.IsValid ω)
    (sfp : FractionalOperation.IsSymmetricFractionalPolymorphismFor ω Γ) :
    (ω.tt (fun i : Fin _ => fun j : ι =>
        (buildColumn (fun d => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨j, d⟩))).get
          (Fin.cast (I.RelaxBLP_denominator_eq_height x_solv j) i)
      )).summap I.evalSolution ≤
    ω.size • (I.RelaxBLP.c ⬝ᵥ x) := by
  sorry

lemma ValuedCSP.Instance.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux
    (I : Γ.Instance ι) {o : ℚ} (ho : I.RelaxBLP.Reaches o)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ) :
    ∃ m : ℕ, ∃ ω : FractionalOperation D m,
      ω.IsValid ∧ ∃ X : Fin m → ι → D, (ω.tt X).summap I.evalSolution ≤ ω.size • o := by
  obtain ⟨x, x_solu, rfl⟩ := ho
  have x_solv := x_solu.toCanonicalRationalSolution
  use x.toCanonicalRationalSolution.denominator
  obtain ⟨ω, valid, sfp⟩ := hΓ x.toCanonicalRationalSolution.denominator
  exact ⟨ω, valid, _, I.RelaxBLP_improved_by_isSymmetricFractionalPolymorphism x_solu x_solv valid sfp⟩

theorem ValuedCSP.Instance.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms
    (I : Γ.Instance ι) {o : ℚ} (ho : I.RelaxBLP.Reaches o)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ) :
    ∃ x : ι → D, I.evalSolution x ≤ o := by
  by_contra! contr
  obtain ⟨m, ω, valid, X, result⟩ := I.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux ho hΓ
  have impos : (ω.tt X).summap I.evalSolution < (ω.tt X).summap I.evalSolution
  · apply result.trans_lt
    convert_to ((ω.tt X).map (fun _ => o)).sum < (ω.tt X).summap I.evalSolution
    · simp [FractionalOperation.tt]
    apply Multiset.summap_lt_summap valid.tt_nonempty
    simp [contr]
  exact impos.false
