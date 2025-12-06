import Duality.Common
import VCSP.LinearProgrammingQ
import VCSP.LinearRelaxation
import Mathlib.Algebra.BigOperators.Field


lemma Sum.fun_elim_index {α β γ : Type*} (x : α → γ) (y : β → γ) :
    (fun i => Sum.elim x y i) = Sum.elim x y :=
  rfl

lemma ite_isTrue {α : Type*} {P : Prop} [Decidable P] (hp : P) (a b : α) :
    (if P then a else b) = a := by
  simp only [hp]
  apply ite_true

lemma ite_eq_symm {α β : Type*} [DecidableEq α] (a₁ a₂ : α) (b₁ b₂ : β) :
    (if a₁ = a₂ then b₁ else b₂) = (if a₂ = a₁ then b₁ else b₂) := by
  aesop

-- Yaël Dillies proved this lemma:
lemma Multiset.toList_map_sum {α β : Type*} (s : Multiset α) [AddCommMonoid β] (f : α → β) :
    (s.toList.map f).sum = (s.map f).sum := by
  rw [←Multiset.sum_coe, ←Multiset.map_coe, Multiset.coe_toList]

-- Damiano Testa proved this lemma:
lemma Finset.univ_sum_multisetToType {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s : Multiset α) (f : α → β) :
    Finset.univ.sum (fun a : s.ToType => f a.fst) = s.summap f := by
  rw [Finset.sum, Multiset.map_univ]

lemma Finset.sigma_univ_sum_to_sum_sum {α : Type*} [Fintype α] {σ : α → Type*} [∀ a : α, Fintype (σ a)]
    {β : Type*} [AddCommMonoid β]
    (f : (Σ a, σ a) → β) :
    Finset.univ.sum f = Finset.univ.sum (fun a : α => Finset.univ.sum (fun s : σ a => f ⟨a, s⟩)) := by
  rewrite [←Finset.sum_sigma]
  rfl

lemma div_eq_div_inj {β : Type*} [GroupWithZero β] {x y z : β} (hxy : x / z = y / z) (hz : z ≠ 0) : x = y := by
  rw [division_def, division_def, mul_eq_mul_right_iff] at hxy
  cases hxy with
  | inl hyp => exact hyp
  | inr hyp =>
    exfalso
    rw [inv_eq_zero] at hyp
    exact hz hyp

lemma nsmul_div {β : Type*} [DivisionSemiring β] (n : ℕ) (x y : β) : n • (x / y) = (n • x) / y := by
  rw [←mul_one_div x y, ←mul_one_div (n • x) y, smul_mul_assoc]

lemma Finset.sum_of_sum_div_const_eq_one {α β : Type*} [Fintype α] [Semifield β] {f : α → β} {z : β}
    (hfz : Finset.univ.sum (fun a => f a / z) = (1 : β)) :
    z = Finset.univ.sum f := by
  if hz : z = 0 then
    exfalso
    simp_rw [hz, div_zero, Finset.sum_const_zero] at hfz
    exact zero_ne_one hfz
  else
    refine (div_eq_div_inj ?_ hz).symm
    convert hfz
    rw [Finset.sum_div]
    exact div_self hz

lemma List.ofFn_get_fin_cast {α : Type*} {l : List α} {n : ℕ} (hnl : n = l.length) :
    List.ofFn (fun i : Fin n => l.get (Fin.cast hnl i)) = l := by
  rw [←List.ofFn_congr hnl.symm, List.ofFn_get]

lemma Fin_cast_bijective {m n : ℕ} (hmn : m = n) : Function.Bijective (Fin.cast hmn) :=
  ⟨fun x y hxy => by aesop, fun z => ⟨⟨z.val, hmn ▸ z.isLt⟩, rfl⟩⟩

lemma Finset.univ_sum_list_get (x : List ℚ) :
    Finset.univ.sum (fun i : Fin x.length => x[i]) = x.sum := by
  induction x with
  | nil => rfl
  | cons d l ih =>
    rw [List.sum_cons, ←ih, Fin.univ_succ]
    simp

lemma List.get_map {α β : Type*} (l : List α) (i : Fin l.length) (f : α → β) : f l[i] = (l.map f)[i] := by
  rw [Fin.getElem_fin, Fin.getElem_fin, List.getElem_map]

lemma Finset.univ_sum_aux {α : Type*} [Fintype α] (f : α → ℚ) (g : α → ℕ) :
    Finset.univ.sum (fun i : Fin _ =>
      f ((List.flatten (Finset.univ.val.toList.map (fun a : α =>
            List.replicate (g a) a
          )))[i])) =
    Finset.univ.sum (fun b : α => f b * g b) := by
  convert_to
    Finset.univ.sum (fun i : Fin _ =>
      (((List.flatten (Finset.univ.val.toList.map (fun a : α =>
            List.replicate (g a) a
          ))).map f)[i])) =
    Finset.univ.sum (fun b : α => f b * g b)
  · simp_rw [List.get_map]
    apply Fintype.sum_bijective (by apply Fin.cast; rw [List.length_map])
    · apply Fin_cast_bijective
    · aesop
  rw [
    List.map_flatten, List.map_map, ←Finset.sum_to_list, Finset.sum_to_list,
    show List.map f ∘ (fun a => List.replicate (g a) a) = (fun a => List.replicate (g a) (f a)) by aesop,
    Finset.univ_sum_list_get, List.sum_flatten, List.map_map]
  show
    ((Multiset.toList Finset.univ.val).map ((fun a => List.sum (List.replicate (g a) (f a))))).sum =
    Finset.univ.sum (fun b : α => f b * g b)
  simp_rw [List.sum_replicate]
  convert_to
    (Finset.univ.val.toList.map (fun a => g a * f a)).sum =
    Finset.univ.sum (fun b : α => f b * g b)
  · simp
  rw [Multiset.toList_map_sum, Finset.sum_map_val]
  simp_rw [mul_comm]


variable {D : Type*} [Fintype D]

lemma Finset.univ_sum_mul_of_list_replicate {n m : ℕ} (f : (Fin m → D) → ℚ) (g : (Fin m → D) → ℕ)
    (hn : n = (List.flatten (Finset.univ.val.toList.map (fun v => List.replicate (g v) v))).length) :
    Finset.univ.sum (fun v : Fin m → D => f v * g v) =
    Finset.univ.sum (fun i : Fin n =>
      f ((List.flatten (Finset.univ.val.toList.map (fun v : Fin m → D =>
            List.replicate (g v) v
          ))).get (Fin.cast hn i))) := by
  convert (Finset.univ_sum_aux f g).symm using 1
  aesop

private noncomputable abbrev buildVertically (p : D → ℕ) : List D :=
  (Finset.univ.val.toList.map (fun d : D => List.replicate (p d) d)).flatten

open scoped Matrix
variable [DecidableEq D] {ι : Type*} [Fintype ι] [DecidableEq ι] {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

private lemma ValuedCSP.Instance.relaxBLP_denominator_eq_height_marginal (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (x_solv : I.RelaxBLP.A *ᵥ x.toCanonicalRationalSolution.toFunction = I.RelaxBLP.b)
    (j : ι) :
    x.toCanonicalRationalSolution.denominator =
    (buildVertically (fun d : D => x.toCanonicalRationalSolution.numerators ◪⟨j, d⟩)).length := by
  unfold buildVertically
  rw [List.length_flatten, List.map_map]
  show
    x.toCanonicalRationalSolution.denominator =
    (Finset.univ.val.toList.map (fun d => (List.replicate (x.toCanonicalRationalSolution.numerators ◪⟨j, d⟩) d).length)).sum
  have eqv := congr_fun x_solv ◪◩j
  simp_rw [
    ValuedCSP.Instance.RelaxBLP, Sum.elim_inr,
    Matrix.fromBlocks_mulVec, Sum.elim_inr,
    Matrix.fromRows_mulVec, Matrix.zero_mulVec, Pi.add_apply, Sum.elim_inl,
    Pi.zero_apply, zero_add,
    Matrix.mulVec, Matrix.of_apply, dotProduct,
    Function.comp_apply, ite_mul, one_mul, zero_mul, Fintype.sum_prod_type
  ] at eqv
  rw [Finset.sum_comm] at eqv -- must not be used in `simp_rw` (would cycle forever)
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true] at eqv
  qify
  rw [Finset.sum_of_sum_div_const_eq_one eqv]
  simp only [List.length_replicate]
  clear * -
  rw [List.map_map, List.map_map]
  show
    (Finset.univ.val.summap     (Nat.cast <| x.toCanonicalRationalSolution.numerators ◪⟨j, ·⟩)) =
    (Finset.univ.val.toList.map (Nat.cast <| x.toCanonicalRationalSolution.numerators ◪⟨j, ·⟩)).sum
  symm
  apply Multiset.toList_map_sum

private lemma ValuedCSP.Instance.relaxBLP_denominator_eq_height_joint (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (x_solv : I.RelaxBLP.A *ᵥ x.toCanonicalRationalSolution.toFunction = I.RelaxBLP.b)
    (t : I) :
    x.toCanonicalRationalSolution.denominator =
    (buildVertically
      (fun v : Fin t.fst.n → D =>
        x.toCanonicalRationalSolution.numerators ◩⟨t, v⟩
      )).length := by
  have eqv := congr_fun x_solv ◪◪t
  simp_rw [
    ValuedCSP.Instance.RelaxBLP, Sum.elim_inr,
    Matrix.fromBlocks_mulVec, Sum.elim_inr,
    Matrix.fromRows_mulVec, Matrix.zero_mulVec, Pi.add_apply, Sum.elim_inr,
    Pi.zero_apply, add_zero,
    Matrix.mulVec, Matrix.of_apply, dotProduct,
    Function.comp_apply, ite_mul, one_mul, zero_mul,
    Finset.sigma_univ_sum_to_sum_sum
  ] at eqv
  conv at eqv => lhs; congr; rfl; ext; dsimp only; rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_ite_eq, ite_isTrue (Finset.mem_univ t)] at eqv
  qify
  rw [Finset.sum_of_sum_div_const_eq_one eqv]
  simp [buildVertically, Multiset.toList_map_sum]

open scoped List in
private lemma Multiset.ToType.cost_improved_by_isSymmetricFractionalPolymorphism {I : Γ.Instance ι} (t : I)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (solution : CanonicalLP.IsSolution I.RelaxBLP x)
    {ω : FractionalOperation D x.toCanonicalRationalSolution.denominator}
    (sfp : FractionalOperation.IsSymmetricFractionalPolymorphismFor ω Γ) :
    (ω.tt (fun i : Fin _ => fun j : ι =>
        (buildVertically (fun d => x.toCanonicalRationalSolution.numerators ◪⟨j, d⟩)).get
          (Fin.cast (I.relaxBLP_denominator_eq_height_marginal solution.toCanonicalRationalSolution j) i)
      )).summap t.fst.evalSolution ≤
    ω.size • Finset.univ.sum (fun v => t.fst.f v * x ◩⟨t, v⟩) := by
  have hxdQ : 0 < (x.toCanonicalRationalSolution.denominator : ℚ)
  · rw [Nat.cast_pos]
    exact x.toCanonicalRationalSolution.denom_pos
  let Z : Fin x.toCanonicalRationalSolution.denominator → Fin t.fst.n → D := fun i : Fin _ =>
    (buildVertically (fun v : Fin t.fst.n → D => x.toCanonicalRationalSolution.numerators ◩⟨t, v⟩)).get
      (Fin.cast (I.relaxBLP_denominator_eq_height_joint solution.toCanonicalRationalSolution t) i)
  have hZ :
    Finset.univ.sum (fun v : Fin t.fst.n → D => t.fst.f v * x ◩⟨t, v⟩) =
    Finset.univ.sum (t.fst.f ∘ Z) / (x.toCanonicalRationalSolution.denominator : ℚ)
  · convert_to
      Finset.univ.sum (fun v : Fin t.fst.n → D => t.fst.f v * (
          (x.toCanonicalRationalSolution.numerators ◩⟨t, v⟩ : ℚ) /
          (x.toCanonicalRationalSolution.denominator : ℚ)
        )) =
      Finset.univ.sum (fun i : Fin x.toCanonicalRationalSolution.denominator => t.fst.f (Z i)) /
        (x.toCanonicalRationalSolution.denominator : ℚ)
    · apply congr_arg
      ext v
      congr
      nth_rewrite 1 [←toCanonicalRationalSolution_toFunction solution.right]
      rfl
    simp_rw [←mul_div_assoc]
    rw [←Finset.sum_div]
    congr 1
    apply Finset.univ_sum_mul_of_list_replicate
  rw [hZ, nsmul_div, le_div_iff₀ hxdQ]
  refine le_trans ?_ (sfp.left ⟨t.fst.n, t.fst.f⟩ t.fst.inΓ Z)
  rw [mul_comm, nsmul_eq_mul, mul_le_mul_left hxdQ]
  apply le_of_eq
  show
    (ω.tt (fun i : Fin _ => fun j : ι =>
        (buildVertically (x.toCanonicalRationalSolution.numerators ◪⟨j, ·⟩)).get
          (Fin.cast (I.relaxBLP_denominator_eq_height_marginal solution.toCanonicalRationalSolution j) i)
      )).summap (fun x : ι → D => t.fst.f (x ∘ t.fst.app)) =
    (ω.tt Z).summap t.fst.f
  convert_to
    (ω.tt (fun i : Fin _ => fun k : Fin t.fst.n =>
        (buildVertically (x.toCanonicalRationalSolution.numerators ◪⟨t.fst.app k, ·⟩)).get
          (Fin.cast (I.relaxBLP_denominator_eq_height_marginal solution.toCanonicalRationalSolution (t.fst.app k)) i)
      )).summap t.fst.f =
    (ω.tt (fun i : Fin _ =>
      (buildVertically (fun v : Fin t.fst.n → D => x.toCanonicalRationalSolution.numerators ◩⟨t, v⟩)).get
        (Fin.cast (I.relaxBLP_denominator_eq_height_joint solution.toCanonicalRationalSolution t) i)
      )).summap t.fst.f
  · unfold FractionalOperation.tt Multiset.summap
    aesop
  refine congr_arg₂ _ ?_ rfl
  unfold FractionalOperation.tt
  rw [←Multiset.attach_map_val ω, Multiset.map_map, Multiset.map_map]
  refine congr_arg₂ _ ?_ rfl
  ext ⟨g, gin⟩ k
  refine sfp.right _ _ ?_ g gin
  show
    List.ofFn (fun i : Fin x.toCanonicalRationalSolution.denominator =>
      (buildVertically (x.toCanonicalRationalSolution.numerators ◪⟨t.fst.app k, ·⟩)).get
        (Fin.cast (I.relaxBLP_denominator_eq_height_marginal solution.toCanonicalRationalSolution (t.fst.app k)) i)) ~
    List.ofFn (fun i : Fin x.toCanonicalRationalSolution.denominator =>
      (buildVertically (x.toCanonicalRationalSolution.numerators ◩⟨t, ·⟩)).get
        (Fin.cast (I.relaxBLP_denominator_eq_height_joint solution.toCanonicalRationalSolution t) i) k)
  convert_to
    List.ofFn (fun i : Fin x.toCanonicalRationalSolution.denominator =>
      (buildVertically (x.toCanonicalRationalSolution.numerators ◪⟨t.fst.app k, ·⟩)).get
        (Fin.cast (I.relaxBLP_denominator_eq_height_marginal solution.toCanonicalRationalSolution (t.fst.app k)) i)) ~
    (List.ofFn (fun i : Fin x.toCanonicalRationalSolution.denominator =>
      (buildVertically (x.toCanonicalRationalSolution.numerators ◩⟨t, ·⟩)).get
        (Fin.cast (I.relaxBLP_denominator_eq_height_joint solution.toCanonicalRationalSolution t) i))).map (· k)
  · aesop
  rw [List.ofFn_get_fin_cast, List.ofFn_get_fin_cast, List.map_flatten, List.map_map]
  show
    List.flatten
      (Finset.univ.val.toList.map (fun d : D =>
        List.replicate ((x.toCanonicalRationalSolution.numerators ◪⟨t.fst.app k, ·⟩) d) d)) ~
    List.flatten
      (Finset.univ.val.toList.map
        (List.map (· k) ∘ (fun v : Fin t.fst.n → D =>
          List.replicate ((x.toCanonicalRationalSolution.numerators ◩⟨t, ·⟩) v) v)))
  convert_to
    List.flatten
      (Finset.univ.val.toList.map (fun d : D =>
        List.replicate (x.toCanonicalRationalSolution.numerators ◪⟨t.fst.app k, d⟩) d)) ~
    List.flatten
      (Finset.univ.val.toList.map (fun v : Fin t.fst.n → D =>
        List.replicate (x.toCanonicalRationalSolution.numerators ◩⟨t, v⟩) (v k)))
  · apply congr_arg
    aesop
  symm
  -- now we need to show that the `k`th joint column and the `t.fst.app k`th marginal column differ only by permuting
  rw [List.perm_iff_count]
  intro a
  rw [List.count_flatten, List.count_flatten, List.map_map, List.map_map]
  show
    (Finset.univ.val.toList.map (fun v : Fin t.fst.n → D =>
      List.count a (List.replicate (x.toCanonicalRationalSolution.numerators ◩⟨t, v⟩) (v k)))).sum =
    (Finset.univ.val.toList.map (fun d : D =>
      List.count a (List.replicate (x.toCanonicalRationalSolution.numerators ◪⟨t.fst.app k, d⟩) d))).sum
  rw [Multiset.toList_map_sum, Multiset.toList_map_sum, Finset.sum_map_val, Finset.sum_map_val]
  simp_rw [List.count_replicate, beq_iff_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_eq_symm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  show
    (Finset.univ.filter (a = · k)).sum (x.toCanonicalRationalSolution.numerators ◩⟨t, ·⟩) =
    x.toCanonicalRationalSolution.numerators ◪⟨t.fst.app k, a⟩

  have key := congr_fun solution.toCanonicalRationalSolution ◩⟨t, k, a⟩
  simp_rw [ValuedCSP.Instance.RelaxBLP, Matrix.mulVec] at key
  rw [←Matrix.fromRows_fromCols_eq_fromBlocks, Sum.elim_inl] at key
  simp_rw [Matrix.fromRows_apply_inl] at key
  rw [←Sum.elim_comp_inl_inr x.toCanonicalRationalSolution.toFunction] at key
  unfold Matrix.fromCols at key
  simp_rw [Matrix.of_apply] at key
  rw [Sum.fun_elim_index, sumElim_dotProduct_sumElim] at key
  simp_rw [dotProduct, Matrix.of_apply, Function.comp_apply] at key
  change key to
    (Finset.univ.sigma (fun _ => Finset.univ)).sum (fun (tᵥ : Σ t : I, (Fin t.fst.n → D)) =>
      (if ht : t = tᵥ.fst then
        if tᵥ.snd (Fin.cast (congr_arg (ValuedCSP.Term.n ∘ Sigma.fst) ht) k) = a then 1 else 0
        else 0) *
      x.toCanonicalRationalSolution.toFunction ◩tᵥ) +
    Finset.univ.sum (fun p : ι × D =>
      (if t.fst.app k = p.fst ∧ a = p.snd then -1 else 0) *
      x.toCanonicalRationalSolution.toFunction ◪p) =
    (0 : ℚ)
  have key' :
    (Finset.univ.sigma (fun _ => Finset.univ)).sum (fun (tᵥ : Σ t : I, (Fin t.fst.n → D)) =>
      (if ht : t = tᵥ.fst then
        if tᵥ.snd (Fin.cast (congr_arg (ValuedCSP.Term.n ∘ Sigma.fst) ht) k) = a then 1 else 0
        else 0) *
      x.toCanonicalRationalSolution.toFunction ◩tᵥ) +
    Finset.univ.sum (fun p : ι × D =>
      (if ⟨t.fst.app k, a⟩ = p then -1 else 0) *
      x.toCanonicalRationalSolution.toFunction ◪p) =
    (0 : ℚ)
  · convert key
    apply Prod.eq_iff_fst_eq_snd_eq
  simp_rw [ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ] at key'
  rw [if_true, add_neg_eq_zero, Finset.sum_sigma] at key'
  change key' to
    Finset.univ.sum (fun cₜ : I =>
      (Finset.univ.sum (fun cᵥ : Fin cₜ.fst.n → D =>
        (if ht : t = cₜ then
          if cᵥ (Fin.cast (congr_arg (ValuedCSP.Term.n ∘ Sigma.fst) ht) k) = a then 1 else 0
          else 0) *
        x.toCanonicalRationalSolution.toFunction ◩⟨cₜ, cᵥ⟩
      ))) =
    x.toCanonicalRationalSolution.toFunction ◪⟨t.fst.app k, a⟩
  have key'' :
    Finset.univ.sum (fun cₜ : I =>
      (if ht : t = cₜ then
        Finset.univ.sum (fun cᵥ : Fin cₜ.fst.n → D =>
          if cᵥ (Fin.cast (congr_arg (ValuedCSP.Term.n ∘ Sigma.fst) ht) k) = a
          then x.toCanonicalRationalSolution.toFunction ◩⟨cₜ, cᵥ⟩ else 0)
       else 0
      )) =
    x.toCanonicalRationalSolution.toFunction ◪⟨t.fst.app k, a⟩
  · convert key' with cₜ
    by_cases hct : t = cₜ <;> simp [hct]
  have key''' :
    (Finset.filter (· k = a) Finset.univ).sum (x.toCanonicalRationalSolution.toFunction ◩⟨t, ·⟩) =
    x.toCanonicalRationalSolution.toFunction ◪⟨t.fst.app k, a⟩
  · convert key'' using 1
    simp [Finset.sum_ite]
  have the_key :
    (Finset.filter (a = · k) Finset.univ).sum (fun v : Fin t.fst.n → D =>
      (x.toCanonicalRationalSolution.numerators ◩⟨t, v⟩ : ℚ) /
      (x.toCanonicalRationalSolution.denominator : ℚ)) =
    x.toCanonicalRationalSolution.toFunction ◪⟨t.fst.app k, a⟩
  · convert key''' using 3
    ext
    apply eq_comm
  qify
  rw [←Finset.sum_div] at the_key
  rw [←div_eq_div_inj the_key hxdQ.ne.symm]

private lemma ValuedCSP.Instance.relaxBLP_improved_by_isSymmetricFractionalPolymorphism (I : Γ.Instance ι)
    {x : ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) → ℚ}
    (solution : CanonicalLP.IsSolution I.RelaxBLP x)
    {ω : FractionalOperation D x.toCanonicalRationalSolution.denominator}
    (sfp : FractionalOperation.IsSymmetricFractionalPolymorphismFor ω Γ) :
    (ω.tt (fun i : Fin _ => fun j : ι =>
        (buildVertically (fun d => x.toCanonicalRationalSolution.numerators ◪⟨j, d⟩)).get
          (Fin.cast (I.relaxBLP_denominator_eq_height_marginal solution.toCanonicalRationalSolution j) i)
      )).summap I.evalSolution ≤
    ω.size • (I.RelaxBLP.c ⬝ᵥ x) := by
  -- LHS:
  unfold ValuedCSP.Instance.evalSolution
  rw [Multiset.summap_summap_swap]
  -- RHS:
  simp_rw [ValuedCSP.Instance.RelaxBLP, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul]
  rw [Finset.sum_const_zero, add_zero, Finset.sigma_univ_sum_to_sum_sum, Finset.smul_sum]
  -- Conversion to per-term inequalities:
  rw [←Finset.univ_sum_multisetToType]
  apply Finset.sum_le_sum
  intro t _
  exact t.cost_improved_by_isSymmetricFractionalPolymorphism solution sfp

lemma ValuedCSP.Instance.relaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux (I : Γ.Instance ι)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ)
    {o : ℚ} (ho : I.RelaxBLP.Reaches o) :
    ∃ m : ℕ, ∃ ω : FractionalOperation D m,
      ω.IsValid ∧ ∃ X : Fin m → ι → D, (ω.tt X).summap I.evalSolution ≤ ω.size • o := by
  obtain ⟨x, solution, rfl⟩ := ho
  obtain ⟨ω, valid, sfp⟩ := hΓ x.toCanonicalRationalSolution.denominator
  exact ⟨x.toCanonicalRationalSolution.denominator, ω, valid, _,
    I.relaxBLP_improved_by_isSymmetricFractionalPolymorphism solution sfp⟩

theorem ValuedCSP.Instance.relaxBLP_improved_of_allSymmetricFractionalPolymorphisms (I : Γ.Instance ι)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ)
    {o : ℚ} (ho : I.RelaxBLP.Reaches o) :
    ∃ x : ι → D, I.evalSolution x ≤ o := by
  by_contra! contr
  obtain ⟨m, ω, valid, X, result⟩ := I.relaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux hΓ ho
  have impos : (ω.tt X).summap I.evalSolution < (ω.tt X).summap I.evalSolution
  · apply result.trans_lt
    convert_to ((ω.tt X).map (fun _ => o)).sum < (ω.tt X).summap I.evalSolution
    · simp [FractionalOperation.tt]
    apply Multiset.summap_lt_summap valid.tt_nonempty
    simp [contr]
  exact impos.false

#print axioms ValuedCSP.Instance.relaxBLP_improved_of_allSymmetricFractionalPolymorphisms
