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

private abbrev convertWeight (δ : ι → D → ℚ) (i : ι) (a : D) : ℕ :=
  Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D =>
    if i = j ∧ a = b then (δ j b).num.toNat else (δ j b).den))

private lemma prod_all_denoms_as_rat_eq_ith_sum_convertWeight {δ : ι → D → ℚ}
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

private noncomputable abbrev convertColumn (δ : ι → D → ℚ) (i : ι) : List D :=
  List.join (Finset.univ.val.toList.map (fun d : D => List.replicate (convertWeight δ i d) d))

private lemma convertColumn_height {δ : ι → D → ℚ} (nonneg : 0 ≤ δ) (sumone : ∀ j : ι, Finset.univ.sum (δ j) = 1) (i : ι) :
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
    fun i => fun j : ι => (convertColumn δ j).get (Fin.cast (convertColumn_height nonneg sumone j) i)⟩


variable {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]
open scoped Matrix

lemma ValuedCSP.Instance.right_sum_one_of_RelaxBLP_holds_aux (I : Γ.Instance ι)
    {xₜ : (Σ t : I, (Fin t.fst.n → D)) → ℚ} {xᵥ : (ι × D) → ℚ}
    (hx : I.RelaxBLP.A *ᵥ (Sum.elim xₜ xᵥ) = I.RelaxBLP.b) (j : ι) :
    Finset.univ.sum (fun d => (Sum.elim xₜ xᵥ) (Sum.inr ⟨j, d⟩)) = 1 := by
  simp_rw [Sum.elim_inr]
  simp_rw [ValuedCSP.Instance.RelaxBLP] at hx
  rw [Matrix.fromBlocks_mulVec_sumType, Matrix.zero_mulVec, zero_add] at hx
  convert_to Finset.univ.sum (fun d : D => xᵥ ⟨j, d⟩) = (fun c : ι × D => if j = c.1 then 1 else 0) ⬝ᵥ xᵥ
  · convert congr_fun (Sum.elim_eq_right hx.symm) j
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
  have sum_one := I.right_sum_one_of_RelaxBLP_holds x_equl
  let X := convertDistribution non_neg sum_one
  use X.fst
  obtain ⟨ω, valid, frpol, symmega⟩ := hΓ X.fst
  use ω
  constructor
  · exact valid
  use X.snd
  rw [← x_cost]
  clear x_cost
  show (ω.tt X.snd).summap (fun y => I.summap (fun t => t.evalSolution y)) ≤ ω.size • (I.RelaxBLP.c ⬝ᵥ x)
  rw [Multiset.summap_summap_swap, Matrix.dotProduct, Finset.smul_sum]
  show
    I.summap (fun t => (ω.tt X.snd).summap (fun y => t.evalSolution y)) ≤
    Finset.univ.sum (fun v : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) => ω.size • (I.RelaxBLP.c v * x v))
  convert_to
    I.summap (fun t => (ω.tt X.snd).summap (fun y => t.evalSolution y)) ≤
    Finset.univ.sum (fun tᵥ : (Σ t : I, (Fin t.fst.n → D)) =>
      (ω.size • tᵥ.fst.fst.f tᵥ.snd * x (Sum.inl tᵥ)))
  · simp [RelaxBLP]
    congr
    ext1
    rewrite [mul_assoc]
    rfl
  show
    I.summap (fun t => (ω.tt X.snd).summap (fun y => t.evalSolution y)) ≤
    (Finset.univ.sigma (fun _ => Finset.univ)).sum (fun tᵥ : (Σ t : I, (Fin t.fst.n → D)) =>
      ω.size • tᵥ.fst.fst.f tᵥ.snd * x (Sum.inl tᵥ))
  rw [Finset.sum_sigma]
  show
    I.summap (fun t : Γ.Term ι => (ω.tt X.snd).summap (fun y => t.evalSolution y)) ≤
    Finset.univ.sum (fun t : I => Finset.univ.sum (fun v : Fin t.fst.n → D =>
      ω.size • t.fst.f v * x (Sum.inl ⟨t, v⟩)))
  convert_to
    Finset.univ.sum (fun t : I => (ω.tt X.snd).summap (fun y => t.fst.evalSolution y)) ≤
    Finset.univ.sum (fun t : I => Finset.univ.sum (fun v : Fin t.fst.n → D =>
      ω.size • t.fst.f v * x (Sum.inl ⟨t, v⟩)))
  · rw [Finset.sum, Multiset.summap, ←Multiset.map_univ] -- trick by Damiano Testa
  apply Finset.sum_le_sum
  intro t₁ tin
  clear tin
  show
    (ω.tt X.snd).summap (fun y : ι → D => t₁.fst.evalSolution y) ≤
    Finset.univ.sum (fun v : Fin t₁.fst.n → D =>
      ω.size • t₁.fst.f v * x (Sum.inl ⟨t₁, v⟩))
  convert_to
    ω.summap (fun g : (Fin X.fst → D) → D => t₁.fst.evalSolution (fun j : ι =>
      g (fun i : Fin X.fst => (convertColumn δ j).get (Fin.cast (convertColumn_height non_neg sum_one j) i)))) ≤
    Finset.univ.sum (fun v : Fin t₁.fst.n → D =>
      ω.size • t₁.fst.f v * x (Sum.inl ⟨t₁, v⟩))
  · simp [FractionalOperation.tt]
    rfl
  show
    ω.summap (fun g : (Fin X.fst → D) → D => t₁.fst.f (fun p : Fin t₁.fst.n => (
      g (fun i : Fin X.fst => (convertColumn δ (t₁.fst.app p)).get
        (Fin.cast (convertColumn_height non_neg sum_one (t₁.fst.app p)) i))))) ≤
    Finset.univ.sum (fun v : Fin t₁.fst.n → D =>
      ω.size • t₁.fst.f v * x (Sum.inl ⟨t₁, v⟩))
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
