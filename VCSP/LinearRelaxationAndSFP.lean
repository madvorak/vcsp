import VCSP.LinearRelaxation
import Mathlib.Tactic.Qify


lemma Sum.elim_eq_left {α β γ : Type*} {u u' : α → γ} {v v' : β → γ}
    (huv : Sum.elim u v = Sum.elim u' v') :
    u = u' := by
  simp_all [Function.funext_iff]

lemma Sum.elim_eq_right {α β γ : Type*} {u u' : α → γ} {v v' : β → γ}
    (huv : Sum.elim u v = Sum.elim u' v') :
    v = v' := by
  simp_all [Function.funext_iff]

-- Yaël Dillies stated this lemma:
lemma Multiset.sum_coe {α : Type*} [AddCommMonoid α] (l : List α) : (l : Multiset α).sum = l.sum :=
  by simp

-- Yaël Dillies proved this lemma:
lemma Multiset.toList_map_sum {α β : Type*} (s : Multiset α) [AddCommMonoid β] (f : α → β) :
    (s.toList.map f).sum = (s.map f).sum := by
  rw [←Multiset.sum_coe, ←Multiset.coe_map, Multiset.coe_toList]

lemma Finset.univ.prod_single_hit {α : Type*} [Fintype α] [DecidableEq α] (g : α → ℚ) (a : α) :
    Finset.univ.prod (fun i : α => if a = i then g i else 1) = g a := by
  simp_rw [prod_ite_eq, mem_univ, if_true]

lemma Finset.univ.prod_mul_single_hit {α : Type*} [Fintype α] [DecidableEq α] (f g : α → ℚ) (a : α) :
    Finset.univ.prod (fun i : α => f i * if a = i then g i else 1) = Finset.univ.prod f * g a := by
  rw [Finset.prod_mul_distrib, Finset.univ.prod_single_hit]

lemma Finset.univ.prod_with_one_exception {α : Type*} [Fintype α] [DecidableEq α] {f g : α → ℚ} {a : α}
    (hfg : f a = 0 → g a = 0) :
    Finset.univ.prod (fun i : α => if a = i then g i else f i) = Finset.univ.prod f * g a / f a := by
  if hf : ∀ i : α, f i ≠ 0 then
    convert Finset.univ.prod_mul_single_hit f (fun i => g i / f i) a using 1
    · apply congr_arg
      ext1 i
      rw [mul_ite, mul_one, mul_div_cancel']
      exact hf i
    · apply mul_div_assoc
  else
    push_neg at hf
    obtain ⟨z, hz⟩ := hf
    convert_to (0 : ℚ) = (0 : ℚ)
    · rw [Finset.prod_eq_zero_iff]
      use z
      exact ⟨mem_univ z, by aesop⟩
    · rw [mul_div_assoc]
      convert zero_mul _
      rw [Finset.prod_eq_zero_iff]
      use z
      exact ⟨mem_univ z, hz⟩
    rfl

lemma Finset.univ.prod_with_one_exception_nested {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {f g : α → β → ℚ} {a : α} {b : β}
    (hfa : ∀ j : β, f a j ≠ 0) :
    Finset.univ.prod (fun i : α => Finset.univ.prod (fun j : β => if a = i ∧ b = j then g i j else f i j)) =
    Finset.univ.prod (fun i : α => Finset.univ.prod (fun j : β => f i j)) * g a b / f a b := by
  have apart_if :
    Finset.univ.prod (fun i : α => Finset.univ.prod (fun j : β => if a = i ∧ b = j then g i j else f i j)) =
    Finset.univ.prod (fun i : α => if a = i
      then Finset.univ.prod (fun j : β => if b = j then g i j else f i j)
      else Finset.univ.prod (fun j : β => f i j))
  · congr
    aesop
  have hfpa : Finset.univ.prod (fun j : β => f a j) ≠ 0
  · intro impos
    rw [Finset.prod_eq_zero_iff] at impos
    obtain ⟨k, hk⟩ := impos
    exact hfa k hk.right
  rw [apart_if, Finset.univ.prod_with_one_exception, Finset.univ.prod_with_one_exception,
      mul_div_assoc, mul_div_assoc, mul_div_assoc _ _ (f a b), mul_eq_mul_left_iff,
      mul_comm, mul_div_assoc, div_self hfpa, mul_one] <;> tauto

lemma nat_cast_eq_int_cast_of_nneg {a : ℤ} (ha : 0 ≤ a) : @Nat.cast ℚ _ (Int.toNat a) = @Int.cast ℚ _ a := by
  aesop


variable
  {D : Type} [Fintype D] [DecidableEq D]
  {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev convertWeight (δ : ι → D → ℚ) (i : ι) (a : D) : ℕ :=
  Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D =>
    if i = j ∧ a = b then (δ j b).num.toNat else (δ j b).den))

lemma prod_all_denoms_as_rat_eq_ith_sum_convertWeight {δ : ι → D → ℚ}
    (nonnegnum : ∀ i : ι, ∀ a : D, 0 ≤ (δ i a).num) (sumone : ∀ j : ι, Finset.univ.sum (δ j) = 1)
    (i : ι) :
    Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => ((δ j b).den : ℚ))) =
    (Finset.univ.val.toList.map (fun a : D => ((convertWeight δ i a) : ℚ))).sum := by
  convert_to
    Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => ((δ j b).den : ℚ))) =
    (Finset.univ.val.toList.map fun a =>
      Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => ((δ j b).den : ℚ))) *
        (Int.toNat (δ i a).num : ℚ) / ((δ i a).den : ℚ)).sum
  · congr
    ext1 a
    push_cast
    have denoms_nz : ∀ d : D, ((δ i d).den : ℚ) ≠ 0
    · intro j impos
      rw [Nat.cast_eq_zero] at impos
      exact (δ i j).den_nz impos
    exact Finset.univ.prod_with_one_exception_nested denoms_nz
  convert_to
    Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => ((δ j b).den : ℚ))) =
    Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => ((δ j b).den : ℚ))) *
      (Finset.univ.val.toList.map fun a => (Int.toNat (δ i a).num : ℚ) / ((δ i a).den : ℚ)).sum
  · simp_rw [mul_div_assoc]
    apply List.sum_map_mul_left
  convert (mul_one _).symm
  convert_to ((Multiset.toList Finset.univ.val).map fun a => (δ i a)).sum = (1 : ℚ)
  · congr
    ext1 a
    rw [nat_cast_eq_int_cast_of_nneg (nonnegnum i a)]
    exact Rat.num_div_den (δ i a)
  rw [Finset.univ.val.toList_map_sum]
  exact sumone i

noncomputable abbrev convertColumn (δ : ι → D → ℚ) (i : ι) : List D :=
  List.join (Finset.univ.val.toList.map (fun d : D => List.replicate (convertWeight δ i d) d))

lemma convertColumn_height {δ : ι → D → ℚ} (nonneg : 0 ≤ δ) (sumone : ∀ j : ι, Finset.univ.sum (δ j) = 1) (i : ι) :
    Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => (δ j b).den)) = (convertColumn δ i).length := by
  have nonnegnum : ∀ i : ι, ∀ a : D, 0 ≤ (δ i a).num
  · intro i a
    rw [Rat.num_nonneg_iff_zero_le]
    exact nonneg i a
  rw [List.length_join, List.map_map]
  have d_lengths : List.length ∘ (fun d : D => List.replicate (convertWeight δ i d) d) = convertWeight δ i
  · ext d
    rw [Function.comp_apply, List.length_replicate]
  rw [d_lengths]
  qify
  have prod_all_denoms_as_rat_aux := prod_all_denoms_as_rat_eq_ith_sum_convertWeight nonnegnum sumone i
  simp_rw [Nat.cast_prod, Nat.cast_ite, nat_cast_eq_int_cast_of_nneg (nonnegnum _ _)] at prod_all_denoms_as_rat_aux
  convert prod_all_denoms_as_rat_aux
  simp_rw [List.map_map]
  congr
  ext1 a
  simp_rw [Function.comp_apply, Nat.cast_prod, Nat.cast_ite, Int.cast_prod, Int.cast_ite, Int.cast_ofNat]
  congr
  ext1 j
  congr
  ext1 b
  have : @Nat.cast ℚ _ (Int.toNat (δ j b).num) = @Int.cast ℚ _ (δ j b).num
  · apply nat_cast_eq_int_cast_of_nneg
    apply nonnegnum
  aesop

noncomputable def convertDistribution {δ : ι → D → ℚ} (nonneg : 0 ≤ δ) (sumone : ∀ j : ι, Finset.univ.sum (δ j) = 1) :
    Σ m : ℕ, Fin m → ι → D :=
  ⟨Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => (δ j b).den)),
    fun n => fun i : ι => (convertColumn δ i).get (Fin.cast (convertColumn_height nonneg sumone i) n)⟩


variable {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]
open scoped Matrix

lemma ValuedCSP.Instance.right_sum_one_of_RelaxBLP_holds_aux (I : Γ.Instance ι)
    {xₜ : (Σ t : I, (Fin t.fst.n → D)) → ℚ} {xᵥ : (ι × D) → ℚ}
    (hx : I.RelaxBLP.A *ᵥ (Sum.elim xₜ xᵥ) = I.RelaxBLP.b) (j : ι) :
    Finset.univ.sum (fun d => (Sum.elim xₜ xᵥ) (Sum.inr ⟨j, d⟩)) = 1 := by
  simp_rw [Sum.elim_inr]
  simp only [ValuedCSP.Instance.RelaxBLP] at hx
  rw [Matrix.fromBlocks_mulVec_sumType, Matrix.zero_mulVec, zero_add] at hx
  have the_eq : (fun c : ι × D => if j = c.fst then 1 else 0) ⬝ᵥ xᵥ = 1
  · convert congr_fun (Sum.elim_eq_right hx) j
  convert_to Finset.sum Finset.univ (fun d : D => xᵥ ⟨j, d⟩) = (fun c : ι × D => if j = c.1 then 1 else 0) ⬝ᵥ xᵥ
  · rw [the_eq]
  clear * -
  simp_rw [Matrix.dotProduct, ite_mul, one_mul, zero_mul, Fintype.sum_prod_type]
  simp [Finset.sum_comm]

lemma ValuedCSP.Instance.right_sum_one_of_RelaxBLP_holds (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (hx : I.RelaxBLP.A *ᵥ x = I.RelaxBLP.b) (j : ι) :
    Finset.univ.sum (fun d => x (Sum.inr ⟨j, d⟩)) = 1 := by
  convert I.right_sum_one_of_RelaxBLP_holds_aux _ j
  · ext1 i
    cases i <;> rfl
  convert hx
  aesop

lemma ValuedCSP.Instance.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux
    (I : Γ.Instance ι) {o : ℚ} (ho : I.RelaxBLP.Reaches o)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ) :
    ∃ m : ℕ, ∃ ω : FractionalOperation D m,
      ω.IsValid ∧ ∃ X : Fin m → ι → D, (ω.tt X).summap I.evalSolution ≤ ω.size • o := by
  obtain ⟨x, ⟨x_equl, x_nneg⟩, x_cost⟩ := ho
  let δ : ι → D → ℚ := fun i d => x (Sum.inr ⟨i, d⟩)
  have non_neg : 0 ≤ δ := fun i : ι => fun d : D => x_nneg (Sum.inr ⟨i, d⟩)
  have sum_one (j : ι) : Finset.univ.sum (δ j) = 1 := I.right_sum_one_of_RelaxBLP_holds x_equl j
  obtain ⟨m, X⟩ := convertDistribution non_neg sum_one
  use m
  obtain ⟨ω, valid, frpol, symmega⟩ := hΓ m
  use ω
  constructor
  · exact valid
  use X
  rw [← x_cost]
  clear x_cost
  suffices : m • (ω.tt X).summap I.evalSolution ≤ m • ω.size • Matrix.dotProduct I.RelaxBLP.c x
  · have : 0 < m := sorry -- will come from API around `convertDistribution`
    simp_all
  apply (frpol.onInstance I X).trans
  rw [smul_comm]
  have zero_lt_size : 0 < ω.size := valid.size_pos
  simp_all
  simp_rw [← ValuedCSP.Instance.solutionVCSPtoBLP_cost]
  show
    Finset.univ.sum (fun i : Fin m => I.RelaxBLP.c ⬝ᵥ (I.solutionVCSPtoBLP (X i))) ≤
    m * I.RelaxBLP.c ⬝ᵥ x
  -- thanks to `symmega` we can replace a relationship between `X` and `x (Sum.inl ..)` by
  -- a relationship between `x (Sum.inr ..)` and `x (Sum.inl ..)` hopefully
  simp_rw [ValuedCSP.Instance.RelaxBLP, Matrix.sum_elim_dotProduct_sum_elim, Matrix.zero_dotProduct', add_zero,
    Matrix.dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
  show
    Finset.univ.sum (fun i : Fin m => Finset.univ.sum (fun tᵥ : (Σ t : I, (Fin t.fst.n → D)) =>
      tᵥ.fst.fst.f tᵥ.snd * if ∀ iₙ : Fin tᵥ.fst.fst.n, tᵥ.snd iₙ = X i (tᵥ.fst.fst.app iₙ) then 1 else 0)) ≤
    m * Finset.univ.sum (fun tᵥ : (Σ t : I, (Fin t.fst.n → D)) => tᵥ.fst.fst.f tᵥ.snd * x (Sum.inl tᵥ))
  convert_to
    Finset.univ.sum (fun i : Fin m => Finset.univ.sum (fun tᵥ : (Σ t : I, (Fin t.fst.n → D)) =>
      tᵥ.fst.fst.f tᵥ.snd * if ∀ iₙ : Fin tᵥ.fst.fst.n, tᵥ.snd iₙ = X i (tᵥ.fst.fst.app iₙ) then 1 else 0)) ≤
    Finset.univ.sum (fun tᵥ : (Σ t : I, (Fin t.fst.n → D)) =>
      m * (tᵥ.fst.fst.f tᵥ.snd * x (Sum.inl tᵥ)))
  · apply Finset.mul_sum
  convert_to
    Finset.univ.sum (fun tᵥ : (Σ t : I, (Fin t.fst.n → D)) => Finset.univ.sum (fun i : Fin m =>
      tᵥ.fst.fst.f tᵥ.snd * if ∀ iₙ : Fin tᵥ.fst.fst.n, tᵥ.snd iₙ = X i (tᵥ.fst.fst.app iₙ) then 1 else 0)) ≤
    Finset.univ.sum (fun tᵥ : (Σ t : I, (Fin t.fst.n → D)) =>
      m * (tᵥ.fst.fst.f tᵥ.snd * x (Sum.inl tᵥ)))
  · apply Finset.sum_comm
  apply Finset.sum_le_sum
  intro ⟨⟨t, iₜ⟩, vₜ⟩ tin
  clear tin
  simp_rw [mul_ite, mul_one, mul_zero]
  show
    Finset.univ.sum (fun iₘ : Fin m => if ∀ iₙ : Fin t.n, vₜ iₙ = X iₘ (t.app iₙ) then t.f vₜ else 0) ≤
    m * (t.f vₜ * x (Sum.inl ⟨⟨t, iₜ⟩, vₜ⟩))
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
