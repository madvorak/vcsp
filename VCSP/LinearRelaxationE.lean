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
  rw [Fintype.sum_prod_type]

set_option maxHeartbeats 333333 in
lemma ValuedCSP.Instance.solutionVCSPtoBLPE_cost (I : Γ.Instance ι) (x : ι → D) :
    I.RelaxBLPE.c ᵥ⬝ I.solutionVCSPtoBLPE x = I.evalSolution x := by
  unfold Matrix.dotProd
  rw [Fintype.sum_sum_type]
  unfold ValuedCSP.Instance.RelaxBLPE
  simp_rw [Sum.elim_inl, Sum.elim_inr, ite_smul, smul_zero, ite_self]
  rw [Finset.sum_const_zero, add_zero]
  sorry
