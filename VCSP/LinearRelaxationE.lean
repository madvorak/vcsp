import VCSP.LinearRelaxation
import VCSP.LinearProgrammingCE


variable
  {D : Type*} [Fintype D] [DecidableEq D]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : Type*} [LinearOrderedField F]
  {Γ : ValuedCSP D F∞} [DecidableEq (Γ.Term ι)]

instance deceqInstanceE (I : Γ.Instance ι) : DecidableEq I :=
  inferInstanceAs (DecidableEq (Σ t : Γ.Term ι, Fin (I.count t)))

noncomputable def ValuedCSP.Instance.RelaxBLPE (I : Γ.Instance ι) :
    CanonicalELP
      ((Σ t : I, (Fin t.fst.n × D)) ⊕ (ι ⊕ I)) -- equalities
      ((Σ t : I, (Fin t.fst.n → D)) ⊕ (ι × D)) -- variables
      F :=
  CanonicalELP.mk
    (Matrix.fromBlocks
      (Matrix.of fun ⟨cₜ, cₙ, cₐ⟩ => fun ⟨t, v⟩ =>
        if ht : cₜ = t
        then
          if v (@Fin.cast cₜ.fst.n t.fst.n (congr_arg (ValuedCSP.Term.n ∘ Sigma.fst) ht) cₙ) = cₐ
          then 1
          else 0
        else 0)
      (Matrix.of fun ⟨⟨cₜ, _⟩, cₙ, cₐ⟩ => fun ⟨i, a⟩ => if cₜ.app cₙ = i ∧ cₐ = a then -1 else 0)
      (Matrix.fromRows
        0
        (Matrix.of fun cₜ : I => fun ⟨t, _⟩ => if cₜ = t then 1 else 0))
      (Matrix.fromRows
        (Matrix.of fun cᵢ : ι => fun ⟨i, _⟩ => if cᵢ = i then 1 else 0)
        0))
    (Sum.elim
      (fun _ : (Σ t : I, (Fin t.fst.n × D)) => 0)
      (fun _ : ι ⊕ I => 1))
    (Sum.elim
      (fun ⟨⟨t, _⟩, v⟩ => t.f v)
      (fun _ => 0))

abbrev ValuedCSP.Instance.solutionVCSPtoBLPE (I : Γ.Instance ι) (x : ι → D) :
    ((Σ t : I, (Fin t.fst.n → D)) ⊕ (ι × D)) → F≥0 :=
  Sum.elim
    (fun ⟨⟨t, _⟩, (v : (Fin t.n → D))⟩ => if ∀ i : Fin t.n, v i = x (t.app i) then 1 else 0)
    (fun ⟨i, d⟩ => if x i = d then 1 else 0)

set_option linter.unusedSectionVars false

lemma ValuedCSP.Instance.solutionVCSPtoBLPE_nneg (I : Γ.Instance ι) (x : ι → D) :
    0 ≤ I.solutionVCSPtoBLPE x := by
  unfold Pi.hasLe
  aesop

example {α γ : Type*} [SMul γ α] [AddCommMonoid α] (f : D → γ) (g : D → α) :
    Finset.univ.sum (fun a : D × Fin 7 => (match a with | ⟨d, _⟩ => f d) • (match a with | ⟨d, _⟩ => g d)) =
    Finset.univ.sum (fun a : D × Fin 7 => (match a with | ⟨d, _⟩ => f d • g d)) := by
  rfl

lemma ValuedCSP.Instance.solutionVCSPtoBLPE_cost (I : Γ.Instance ι) (x : ι → D) :
    I.RelaxBLPE.c ᵥ⬝ I.solutionVCSPtoBLPE x = I.evalSolution x := by
  unfold Matrix.dotProd
  rw [Fintype.sum_sum_type]
  unfold ValuedCSP.Instance.RelaxBLPE
  simp_rw [Sum.elim_inl, Sum.elim_inr, ite_smul, smul_zero, ite_self]
  rw [Finset.sum_const_zero, add_zero]
  sorry

lemma ValuedCSP.Instance.RelaxBLPE_solutionVCSPtoBLPE_top_right_of_hit (I : Γ.Instance ι)
    {cₜ : Σ t : Γ.Term ι, Fin (I.count t)} {cₙ : Fin cₜ.fst.n} {cₐ : D} {x : ι → D}
    (hit : x (cₜ.fst.app cₙ) = cₐ) :
    (fun ⟨i, a⟩ => ((if cₜ.fst.app cₙ = i ∧ cₐ = a then -1 else 0) : F∞)) ᵥ⬝ (I.solutionVCSPtoBLPE x ∘ Sum.inr) = -1 := by
  rw [Sum.elim_comp_inr, Matrix.dotProd]
  simp_rw [smul_ite, ite_smul, smul_zero, EF.one_smul, EF.zero_smul_nonbot (show (-1 : F∞) ≠ ⊥ from ne_of_beq_false rfl), ite_self]
  rw [←neg_eq_iff_eq_neg, Fintype.sum_prod_type]
  sorry

lemma ValuedCSP.Instance.RelaxBLPE_solutionVCSPtoBLPE_top_right_of_miss (I : Γ.Instance ι)
    {cₜ : Σ t : Γ.Term ι, Fin (I.count t)} {cₙ : Fin cₜ.fst.n} {cₐ : D} {x : ι → D}
    (miss : x (cₜ.fst.app cₙ) ≠ cₐ) :
    (fun ⟨i, a⟩ => ((if cₜ.fst.app cₙ = i ∧ cₐ = a then -1 else 0) : F∞)) ᵥ⬝ (I.solutionVCSPtoBLPE x ∘ Sum.inr) = -0 := by
  rw [Sum.elim_comp_inr, Matrix.dotProd]
  simp_rw [smul_ite, ite_smul, smul_zero, EF.one_smul, EF.zero_smul_nonbot (show (-1 : F∞) ≠ ⊥ from ne_of_beq_false rfl), ite_self]
  rw [←neg_eq_iff_eq_neg, Fintype.sum_prod_type]
  sorry

lemma ValuedCSP.Instance.RelaxBLPE_solutionVCSPtoBLPE_bottom_right (I : Γ.Instance ι)
    (cᵢ : ι) (x : ι → D) :
    (fun ⟨i, _⟩ => ((if cᵢ = i then 1 else 0) : F∞)) ᵥ⬝ (I.solutionVCSPtoBLPE x ∘ Sum.inr) = 1 := by
  rw [Sum.elim_comp_inr, Matrix.dotProd]
  simp_rw [smul_ite, ite_smul, smul_zero, EF.one_smul, EF.zero_smul_nonbot (show (1 : F∞) ≠ ⊥ from ne_of_beq_false rfl), ite_self]
  sorry

lemma ValuedCSP.Instance.RelaxBLPE_solutionVCSPtoBLPE_bottom_left (I : Γ.Instance ι)
    (cₜ : I) (x : ι → D) :
    (fun ⟨t, _⟩ => ((if cₜ = t then 1 else 0) : F∞)) ᵥ⬝ (I.solutionVCSPtoBLPE x ∘ Sum.inl) = 1 := by
  sorry

theorem ValuedCSP.Instance.RelaxBLPE_reaches (I : Γ.Instance ι) (x : ι → D) :
    I.RelaxBLPE.Reaches (I.evalSolution x) := by
  refine ⟨I.solutionVCSPtoBLPE x, ?_, I.solutionVCSPtoBLPE_cost x⟩
  simp only [CanonicalELP.IsSolution, ValuedCSP.Instance.RelaxBLPE]
  ext j
  sorry
