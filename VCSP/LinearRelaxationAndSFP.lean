import VCSP.LinearRelaxation
import VCSP.LinearProgrammingQ


-- Std4 desperately needs such lemma:
lemma Sum.elim_eq_left {α β γ : Type*} {u u' : α → γ} {v v' : β → γ}
    (huv : Sum.elim u v = Sum.elim u' v') :
    u = u' := by
  simp_all [Function.funext_iff]

-- Std4 desperately needs such lemma:
lemma Sum.elim_eq_right {α β γ : Type*} {u u' : α → γ} {v v' : β → γ}
    (huv : Sum.elim u v = Sum.elim u' v') :
    v = v' := by
  simp_all [Function.funext_iff]

-- Yaël Dillies proved this lemma:
lemma Multiset.toList_map_sum {α β : Type*} (s : Multiset α) [AddCommMonoid β] (f : α → β) :
    (s.toList.map f).sum = (s.map f).sum := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]

-- Damiano Testa proved this lemma:
lemma Finset.univ_sum_multisetToType {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s : Multiset α) (f : α → β) :
    Finset.univ.sum (fun a : s.ToType => f a.fst) = s.summap f := by
  rw [Finset.sum, Multiset.map_univ]

lemma nsmul_div {β : Type*} [DivisionSemiring β] (n : ℕ) (x y : β) : n • (x / y) = (n • x) / y := by
  rw [←mul_one_div x y, ←mul_one_div (n • x) y, smul_mul_assoc]

lemma Finset.sum_of_sum_div_const_eq_one {α β : Type*} [Fintype α] [Semifield β] {f : α → β} {z : β}
    (hfz : Finset.univ.sum (fun a => f a / z) = (1 : β)) :
    z = Finset.univ.sum f := by
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
    | inl hyp => exact hyp.symm
    | inr hyp =>
      exfalso
      rw [one_div, inv_eq_zero] at hyp
      exact hz hyp


variable {D : Type} [Fintype D]

private noncomputable abbrev buildVertically (p : D → ℕ) : List D :=
  (Finset.univ.val.toList.map (fun d : D => List.replicate (p d) d)).join

open scoped Matrix
variable [DecidableEq D] {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

lemma ValuedCSP.Instance.RelaxBLP_denominator_eq_height_marginal (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (x_solv : I.RelaxBLP.A *ᵥ x.toCanonicalRationalSolution.toFunction = I.RelaxBLP.b)
    (j : ι) :
    x.toCanonicalRationalSolution.denominator =
    (buildVertically (fun d : D => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨j, d⟩))).length := by
  rw [List.length_join, List.map_map, Function.comp]
  simp_rw [List.length_replicate]
  rw [Multiset.toList_map_sum]
  qify
  rw [Multiset.map_map, Multiset.map_map]
  have eqv := congr_fun x_solv (Sum.inr (Sum.inl j))
  simp_rw [
    ValuedCSP.Instance.RelaxBLP, Sum.elim_inr,
    Matrix.fromBlocks_mulVec, Sum.elim_inr,
    Matrix.fromRows_mulVec, Matrix.zero_mulVec, Pi.add_apply, Sum.elim_inl,
    Pi.zero_apply, zero_add,
    Matrix.mulVec, Matrix.of_apply, Matrix.dotProduct,
    Function.comp_apply, ite_mul, one_mul, zero_mul, Fintype.sum_prod_type
  ] at eqv
  rw [Finset.sum_comm] at eqv -- must not be used in `simp_rw` (cycling forever)
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true] at eqv
  exact Finset.sum_of_sum_div_const_eq_one eqv

lemma ValuedCSP.Instance.RelaxBLP_denominator_eq_height_joint (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (x_solv : I.RelaxBLP.A *ᵥ x.toCanonicalRationalSolution.toFunction = I.RelaxBLP.b)
    (t : I) :
    x.toCanonicalRationalSolution.denominator =
    (buildVertically
      (fun v : Fin t.fst.n → D =>
        x.toCanonicalRationalSolution.numerators (Sum.inl ⟨t, v⟩)
      )).length := by
  rw [List.length_join, List.map_map, Function.comp]
  simp_rw [List.length_replicate, Multiset.toList_map_sum]
  qify
  rw [Multiset.map_map, Multiset.map_map]
  show
    (x.toCanonicalRationalSolution.denominator : ℚ) =
    Finset.univ.sum (fun v : Fin t.fst.n → D =>
      (x.toCanonicalRationalSolution.numerators (Sum.inl ⟨t, v⟩) : ℚ))
  have eqv := congr_fun x_solv (Sum.inr (Sum.inr t))
  simp_rw [
    ValuedCSP.Instance.RelaxBLP, Sum.elim_inr,
    Matrix.fromBlocks_mulVec, Sum.elim_inr,
    Matrix.fromRows_mulVec, Matrix.zero_mulVec, Pi.add_apply, Sum.elim_inr,
    Pi.zero_apply, add_zero,
    Matrix.mulVec, Matrix.of_apply, Matrix.dotProduct,
    Function.comp_apply, ite_mul, one_mul, zero_mul
  ] at eqv
  change eqv to
    (Finset.univ.sigma (fun _ => Finset.univ)).sum (fun tᵥ =>
      if t = tᵥ.fst then x.toCanonicalRationalSolution.toFunction (Sum.inl tᵥ) else 0) =
    1
  rw [Finset.sum_sigma] at eqv
  have eqv' :
    Finset.univ.sum (fun cₜ : I =>
        if t = cₜ then
          Finset.univ.sum (fun v : Fin cₜ.fst.n → D =>
            x.toCanonicalRationalSolution.toFunction (Sum.inl ⟨cₜ, v⟩))
        else 0
      ) = 1
  · convert eqv
    simp
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true] at eqv'
  exact Finset.sum_of_sum_div_const_eq_one eqv'

open scoped List in
lemma Multiset.ToType.cost_improved_by_isSymmetricFractionalPolymorphism {I : Γ.Instance ι} (t : I)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (x_solu : CanonicalLP.IsSolution I.RelaxBLP x)
    (x_solv : I.RelaxBLP.A *ᵥ x.toCanonicalRationalSolution.toFunction = I.RelaxBLP.b)
    {ω : FractionalOperation D x.toCanonicalRationalSolution.denominator}
    (valid : ω.IsValid)
    (sfp : FractionalOperation.IsSymmetricFractionalPolymorphismFor ω Γ) :
    (ω.tt (fun i : Fin _ => fun j : ι =>
        (buildVertically (fun d => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨j, d⟩))).get
          (Fin.cast (I.RelaxBLP_denominator_eq_height_marginal x_solv j) i)
      )).summap t.fst.evalSolution ≤
    ω.size • Finset.univ.sum (fun v => t.fst.f v * x (Sum.inl ⟨t, v⟩)) := by
  have hxdQ : 0 < (x.toCanonicalRationalSolution.denominator : ℚ)
  · rw [Nat.cast_pos]
    exact x.toCanonicalRationalSolution.denom_pos
  let Z : Fin x.toCanonicalRationalSolution.denominator → Fin t.fst.n → D := fun i : Fin _ =>
    (buildVertically (fun v : Fin t.fst.n → D => x.toCanonicalRationalSolution.numerators (Sum.inl ⟨t, v⟩))).get
      (Fin.cast (I.RelaxBLP_denominator_eq_height_joint x_solv t) i)
  have hZ :
    Finset.univ.sum (fun v : Fin t.fst.n → D => t.fst.f v * x (Sum.inl ⟨t, v⟩)) =
    Finset.univ.sum (fun i : Fin x.toCanonicalRationalSolution.denominator => t.fst.f (Z i)) /
      (x.toCanonicalRationalSolution.denominator : ℚ)
  · convert_to
      Finset.univ.sum (fun v : Fin t.fst.n → D => t.fst.f v * (
          (x.toCanonicalRationalSolution.numerators (Sum.inl ⟨t, v⟩) : ℚ) /
          (x.toCanonicalRationalSolution.denominator : ℚ)
        )) =
      Finset.univ.sum (fun i : Fin x.toCanonicalRationalSolution.denominator => t.fst.f (Z i)) /
        (x.toCanonicalRationalSolution.denominator : ℚ)
    · apply congr_arg
      ext v
      congr
      nth_rewrite 1 [← toCanonicalRationalSolution_toFunction x_solu.right]
      rfl
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    show
      Finset.univ.sum (fun v : Fin t.fst.n → D =>
        t.fst.f v * (x.toCanonicalRationalSolution.numerators (Sum.inl ⟨t, v⟩) : ℚ)) =
      Finset.univ.sum (fun i : Fin x.toCanonicalRationalSolution.denominator =>
        t.fst.f (
          (List.join (Finset.univ.val.toList.map (fun v : Fin t.fst.n → D =>
              List.replicate (x.toCanonicalRationalSolution.numerators (Sum.inl ⟨t, v⟩)) v
            ))).get (Fin.cast (I.RelaxBLP_denominator_eq_height_joint x_solv t) i)))
    sorry -- should be easy
  rw [hZ, nsmul_div, le_div_iff hxdQ]
  refine le_trans ?_ (sfp.left ⟨t.fst.n, t.fst.f⟩ t.fst.inΓ Z)
  rw [mul_comm, nsmul_eq_mul, mul_le_mul_left hxdQ]
  apply le_of_eq
  show
    (ω.tt (fun i : Fin _ => fun j : ι =>
        (buildVertically (fun d => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨j, d⟩))).get
          (Fin.cast (I.RelaxBLP_denominator_eq_height_marginal x_solv j) i)
      )).summap (fun x : ι → D => t.fst.f (x ∘ t.fst.app)) =
    (ω.tt Z).summap t.fst.f
  convert_to
    (ω.tt (fun i : Fin _ => fun k : Fin t.fst.n =>
        (buildVertically (fun d => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨t.fst.app k, d⟩))).get
          (Fin.cast (I.RelaxBLP_denominator_eq_height_marginal x_solv (t.fst.app k)) i)
      )).summap t.fst.f =
    (ω.tt (fun i : Fin _ =>
      (buildVertically (fun v : Fin t.fst.n → D => x.toCanonicalRationalSolution.numerators (Sum.inl ⟨t, v⟩))).get
        (Fin.cast (I.RelaxBLP_denominator_eq_height_joint x_solv t) i)
      )).summap t.fst.f
  · unfold FractionalOperation.tt
    aesop
  refine congr_arg₂ _ ?_ rfl
  unfold FractionalOperation.tt
  rw [← Multiset.attach_map_val ω, Multiset.map_map, Multiset.map_map]
  refine congr_arg₂ _ ?_ rfl
  ext ⟨g, gin⟩ k
  refine sfp.right _ _ ?_ g gin
  show
    List.ofFn (fun i : Fin x.toCanonicalRationalSolution.denominator =>
      (buildVertically (fun d : D => x.toCanonicalRationalSolution.numerators (Sum.inr (t.fst.app k, d)))).get
        (Fin.cast (I.RelaxBLP_denominator_eq_height_marginal x_solv (t.fst.app k)) i)) ~
    List.ofFn (fun i : Fin x.toCanonicalRationalSolution.denominator =>
      (buildVertically (fun v : Fin t.fst.n → D => x.toCanonicalRationalSolution.numerators (Sum.inl ⟨t, v⟩))).get
        (Fin.cast (I.RelaxBLP_denominator_eq_height_joint x_solv t) i) k)
  sorry -- utilize `x_solv` to show relationship between marginal counts and joint counts

lemma ValuedCSP.Instance.RelaxBLP_improved_by_isSymmetricFractionalPolymorphism (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (x_solu : CanonicalLP.IsSolution I.RelaxBLP x)
    (x_solv : I.RelaxBLP.A *ᵥ x.toCanonicalRationalSolution.toFunction = I.RelaxBLP.b)
    {ω : FractionalOperation D x.toCanonicalRationalSolution.denominator}
    (valid : ω.IsValid)
    (sfp : FractionalOperation.IsSymmetricFractionalPolymorphismFor ω Γ) :
    (ω.tt (fun i : Fin _ => fun j : ι =>
        (buildVertically (fun d => x.toCanonicalRationalSolution.numerators (Sum.inr ⟨j, d⟩))).get
          (Fin.cast (I.RelaxBLP_denominator_eq_height_marginal x_solv j) i)
      )).summap I.evalSolution ≤
    ω.size • (I.RelaxBLP.c ⬝ᵥ x) := by
  -- LHS:
  unfold ValuedCSP.Instance.evalSolution
  rw [Multiset.summap_summap_swap]
  -- RHS:
  simp_rw [ValuedCSP.Instance.RelaxBLP, Matrix.dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
  show  _ ≤ ω.size • (Finset.univ.sigma (fun _ => Finset.univ)).sum (fun tᵥ => tᵥ.fst.fst.f tᵥ.snd * x (Sum.inl tᵥ))
  rw [Finset.sum_sigma, Finset.smul_sum]
  -- Conversion to per-term inequalities:
  rw [←Finset.univ_sum_multisetToType]
  apply Finset.sum_le_sum
  intro t _
  exact t.cost_improved_by_isSymmetricFractionalPolymorphism x_solu x_solv valid sfp

lemma ValuedCSP.Instance.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux
    (I : Γ.Instance ι) {o : ℚ} (ho : I.RelaxBLP.Reaches o)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ) :
    ∃ m : ℕ, ∃ ω : FractionalOperation D m,
      ω.IsValid ∧ ∃ X : Fin m → ι → D, (ω.tt X).summap I.evalSolution ≤ ω.size • o := by
  obtain ⟨x, x_sol, rfl⟩ := ho
  obtain ⟨ω, valid, sfp⟩ := hΓ x.toCanonicalRationalSolution.denominator
  exact ⟨x.toCanonicalRationalSolution.denominator, ω, valid, _,
    I.RelaxBLP_improved_by_isSymmetricFractionalPolymorphism
      x_sol x_sol.toCanonicalRationalSolution valid sfp⟩

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
