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


variable
  {D : Type} [Fintype D] [DecidableEq D]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

private noncomputable abbrev buildColumn (δᵢ : D → ℕ) : List D :=
  (Finset.univ.val.toList.map (fun d : D => List.replicate (δᵢ d) d)).join

open scoped Matrix

lemma ValuedCSP.Instance.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux
    (I : Γ.Instance ι) {o : ℚ} (ho : I.RelaxBLP.Reaches o)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ) :
    ∃ m : ℕ, ∃ ω : FractionalOperation D m,
      ω.IsValid ∧ ∃ X : Fin m → ι → D, (ω.tt X).summap I.evalSolution ≤ ω.size • o := by
  obtain ⟨x, x_solu, x_cost⟩ := ho
  have x_solv := x_solu.toCanonicalRationalSolution
  use x.toCanonicalRationalSolution.denominator
  obtain ⟨ω, valid, frpol, symmega⟩ := hΓ x.toCanonicalRationalSolution.denominator
  use ω, valid
  let δ : ι → D → ℕ := fun j : ι => fun d : D => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨j, d⟩)
  use fun i : Fin _ => fun j : ι => (buildColumn (δ j)).get (Fin.cast ?_ i)
  · sorry
  rw [List.length_join, List.map_map]
  have d_lengths : List.length ∘ (fun d => List.replicate (δ j d) d) = δ j
  · ext d
    rw [Function.comp_apply, List.length_replicate]
  rw [d_lengths]
  simp only
  convert_to
    x.toCanonicalRationalSolution.denominator =
      Finset.univ.sum (fun d : D => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨j, d⟩))
  · sorry
  qify
  unfold CanonicalRationalSolution.toFunction at x_solv
  have equ := congr_fun x_solv (Sum.inr j)
  simp_rw [ValuedCSP.Instance.RelaxBLP, Sum.elim_inr, Function.toCanonicalRationalSolution] at equ
  sorry

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
