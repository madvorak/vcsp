import Mathlib.Algebra.Order.Module.Defs
import VCSP.Basic


class LinearOrderedDivisionRing (R : Type*) extends
  LinearOrderedRing R, DivisionRing R

lemma inv_pos_of_pos' {R : Type*} [LinearOrderedDivisionRing R] {a : R} (ha : 0 < a) : 0 < a⁻¹ :=
  lt_of_mul_lt_mul_left (by simp [ha.ne.symm]) ha.le

private def chop {m : ℕ} {R W : Type*} [Semiring R] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) : W →ₗ[R] Fin m → R :=
  ⟨⟨
    fun w : W => fun i : Fin m => A w i.castSucc,
  by
    intros
    ext
    simp
  ⟩,
  by
    intros
    ext
    simp
  ⟩

private def auxLinMaps {m : ℕ} {R W : Type*} [Ring R] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) (x : W) : W →ₗ[R] Fin m → R :=
  ⟨⟨
    chop A - (A · ⟨m, lt_add_one m⟩ • chop A x),
  by
    intros
    ext
    simp only [chop, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, map_add, smul_eq_mul, add_mul]
    abel
  ⟩,
  by
    intros
    ext
    simp [chop, mul_sub, mul_assoc]
  ⟩

private def auxLinMap {m : ℕ} {R V W : Type*} [Semiring R] [AddCommGroup V] [Module R V] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) (b : W →ₗ[R] V) (x : W) : W →ₗ[R] V :=
  ⟨⟨
    b - (A · ⟨m, lt_add_one m⟩ • b x),
  by
    intros
    simp only [Pi.add_apply, Pi.sub_apply, map_add, add_smul]
    abel
  ⟩,
  by
    intros
    -- note that `simp` does not work here
    simp only [Pi.smul_apply, Pi.sub_apply, LinearMapClass.map_smul, RingHom.id_apply, smul_sub, IsScalarTower.smul_assoc]
  ⟩

private lemma filter_yielding_singleton_attach_sum {m : ℕ} {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (f : Fin m.succ → R) (v : V) :
    (Finset.univ.filter (¬ ·.val < m)).attach.sum (fun j => f j.val • v) =
    f ⟨m, lt_add_one m⟩ • v := by
  have singlet : Finset.univ.filter (fun j : Fin m.succ => ¬(j.val < m)) = {⟨m, lt_add_one m⟩}
  · rw [Finset.ext_iff]
    intro i
    constructor <;> rw [Finset.mem_singleton, Finset.mem_filter] <;> intro hi
    · have him := hi.right
      push_neg at him
      exact eq_of_le_of_le (Nat.le_of_lt_succ i.isLt) him
    · refine ⟨Finset.mem_univ i, ?_⟩
      rw [hi]
      push_neg
      rfl
  rw [singlet, Finset.sum_attach _ (fun j => f j • v), Finset.sum_singleton]

private lemma impossible_index {m : ℕ} {i : Fin m.succ} (hi : ¬(i.val < m)) (i_neq_m : i ≠ ⟨m, lt_add_one m⟩) : False := by
  push_neg at hi
  exact i_neq_m (eq_of_le_of_le (Fin.succ_le_succ_iff.mp i.isLt) hi)

variable {R V W : Type*}

private lemma sum_nneg_aux {m : ℕ} [OrderedRing R]
    [OrderedAddCommGroup V] [Module R V] [PosSMulMono R V] [AddCommMonoid W] [Module R W]
    {A : W →ₗ[R] Fin m → R} {x : W} {U : Fin m → V} (hU : 0 ≤ U) (hAx : A x ≤ 0) :
    Finset.univ.sum (fun i : Fin m => A x i • U i) ≤ 0 := by
  rw [←neg_zero, ←le_neg, ←Finset.sum_neg_distrib]
  apply Finset.sum_nonneg
  intro i _
  rw [le_neg, neg_zero]
  exact smul_nonpos_of_nonpos_of_nonneg (hAx i) (hU i)

private lemma finishing_piece {m : ℕ} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    {A : W →ₗ[R] Fin m.succ → R} {w : W} {U : Fin m → V} :
    Finset.univ.sum (fun i : Fin m => chop A w i • U i) =
    (Finset.univ.filter _).attach.sum
      (fun i : { _i : Fin m.succ // _i ∈ Finset.univ.filter (·.val < m) } => A w i.val • U ⟨i.val.val, by aesop⟩) := by
  apply
    Finset.sum_bij'
      (fun i : Fin m => fun _ => (⟨⟨i.val, by omega⟩, by aesop⟩ : { a : Fin m.succ // a ∈ Finset.univ.filter (·.val < m) }))
      (fun i' : { a : Fin m.succ // a ∈ Finset.univ.filter (·.val < m) } => fun _ => ⟨i'.val.val, by aesop⟩)
      (by aesop)
      (by aesop)
      (by aesop)
      (by aesop)
  intros
  rfl

lemma industepFarkasBartl {m : ℕ} [LinearOrderedDivisionRing R]
    [LinearOrderedAddCommGroup V] [Module R V] [PosSMulMono R V] [AddCommGroup W] [Module R W]
    (ih : ∀ A₀ : W →ₗ[R] Fin m → R, ∀ b₀ : W →ₗ[R] V,
      (∀ x : W, A₀ x ≤ 0 → b₀ x ≤ 0) →
        (∃ U : Fin m → V, 0 ≤ U ∧ ∀ w : W, b₀ w = Finset.univ.sum (fun i : Fin m => A₀ w i • U i)))
    {A : W →ₗ[R] Fin m.succ → R} {b : W →ₗ[R] V} (hAb : ∀ x : W, A x ≤ 0 → b x ≤ 0) :
    ∃ U : Fin m.succ → V, 0 ≤ U ∧ ∀ w : W, b w = Finset.univ.sum (fun i : Fin m.succ => A w i • U i) := by
  if is_easy : ∀ x : W, chop A x ≤ 0 → b x ≤ 0 then
    obtain ⟨U, hU, hbU⟩ := ih (chop A) b is_easy
    use (fun i : Fin m.succ => if hi : i.val < m then U ⟨i.val, hi⟩ else 0)
    constructor
    · intro i
      if hi : i.val < m then
        clear * - hi hU
        aesop
      else
        simp [hi]
    · intro w
      simp_rw [smul_dite, smul_zero]
      rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
      convert hbU w using 1
      rw [finishing_piece]
  else
    push_neg at is_easy
    obtain ⟨x', hax', hbx'⟩ := is_easy
    let j : Fin m.succ := ⟨m, lt_add_one m⟩
    let x := (A x' j)⁻¹ • x'
    have hAx' : 0 < A x' j
    · by_contra! contr
      exact (
        (hAb x' (fun i => if hi : i.val < m then hax' ⟨i, hi⟩ else if hij : i = j then hij ▸ contr else by
          exfalso
          exact impossible_index hi hij
        )).trans_lt hbx'
      ).false
    have hAx : A x j = 1
    · convert inv_mul_cancel hAx'.ne.symm
      simp [x]
    have hAA : ∀ w : W, A (w - (A w j • x)) j = 0
    · intro w
      simp [hAx]
    have haAbA : ∀ w : W, chop A (w - (A w j • x)) ≤ 0 → b (w - (A w j • x)) ≤ 0
    · intro w hw
      apply hAb
      intro i
      if hi : i.val < m then
        exact hw ⟨i, hi⟩
      else if hij : i = j then
        rewrite [hij, hAA]
        rfl
      else
        exfalso
        exact impossible_index hi hij
    have haaAbbA : ∀ w : W, chop A w - chop A (A w j • x) ≤ 0 → b w - b (A w j • x) ≤ 0
    · simpa using haAbA
    have haAabAb : ∀ w : W, (chop A - (A · j • chop A x)) w ≤ 0 → (b - (A · j • b x)) w ≤ 0
    · simpa using haaAbbA
    obtain ⟨U', hU', hbU'⟩ := ih (auxLinMaps A x) (auxLinMap A b x) haAabAb
    use (fun i : Fin m.succ => if hi : i.val < m then U' ⟨i.val, hi⟩ else b x - Finset.univ.sum (fun i : Fin m => chop A x i • U' i))
    constructor
    · intro i
      if hi : i.val < m then
        clear * - hi hU'
        aesop
      else
        have hAx'inv : 0 ≤ (A x' j)⁻¹
        · exact (inv_pos_of_pos' hAx').le
        have hax : chop A x ≤ 0
        · simpa [x] using smul_nonpos_of_nonneg_of_nonpos hAx'inv hax'
        have hbx : 0 ≤ b x
        · simpa [x] using smul_nonneg hAx'inv hbx'.le
        simpa [hi] using (sum_nneg_aux hU' hax).trans hbx
    · intro w
      have key : b w - A w j • b x = Finset.univ.sum (fun i : Fin m => (chop A w i - A w j * chop A x i) • U' i)
      · simpa using hbU' w
      rw [←add_eq_of_eq_sub key.symm]
      simp_rw [smul_dite]
      rw [Finset.sum_dite, filter_yielding_singleton_attach_sum]
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      simp_rw [←smul_smul, ←Finset.smul_sum]
      rw [smul_sub, finishing_piece]
      abel

theorem finFarkasBartl {n : ℕ} [LinearOrderedDivisionRing R]
    [LinearOrderedAddCommGroup V] [Module R V] [PosSMulMono R V] [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] Fin n → R) (b : W →ₗ[R] V) :
    (∀ x : W, A x ≤ 0 → b x ≤ 0) ↔ (∃ U : Fin n → V, 0 ≤ U ∧ ∀ w : W, b w = Finset.univ.sum (fun i : Fin n => A w i • U i)) := by
  constructor
  · induction n generalizing b with -- note that `A` is "generalized" automatically
    | zero =>
      have A_tauto (w : W) : A w ≤ 0
      · intro i
        exfalso
        apply Nat.not_lt_zero
        exact i.isLt
      intro hAb
      refine ⟨0, by rfl, fun x : W => ?_⟩
      simp_rw [Pi.zero_apply, smul_zero, Finset.sum_const_zero]
      apply eq_of_le_of_le
      · exact hAb x (A_tauto x)
      · simpa using hAb (-x) (A_tauto (-x))
    | succ m ih =>
      exact industepFarkasBartl ih
  · intro ⟨U, hU, hb⟩
    intro x hx
    rw [hb]
    exact sum_nneg_aux hU hx

theorem fintypeFarkasBartl {I : Type*} [Fintype I] [LinearOrderedDivisionRing R]
    [LinearOrderedAddCommGroup V] [Module R V] [PosSMulMono R V] [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] I → R) (b : W →ₗ[R] V) :
    (∀ x : W, A x ≤ 0 → b x ≤ 0) ↔ (∃ U : I → V, 0 ≤ U ∧ ∀ w : W, b w = Finset.univ.sum (fun i : I => A w i • U i)) := by
  convert
    finFarkasBartl ⟨⟨fun w : W => fun i' => A w ((Fintype.equivFin I).symm i'), by aesop⟩, by aesop⟩ b
      using 1
  · constructor <;> intro hyp x <;> convert hyp x <;> constructor <;> intro hx i
    · simpa using hx ((Fintype.equivFin I).toFun i)
    · simpa using hx ((Fintype.equivFin I).invFun i)
    · simpa using hx ((Fintype.equivFin I).invFun i)
    · simpa using hx ((Fintype.equivFin I).toFun i)
  · constructor <;> intro ⟨U, hU, hyp⟩
    · use U ∘ (Fintype.equivFin I).invFun
      constructor
      · intro i
        simpa using hU ((Fintype.equivFin I).invFun i)
      · intro w
        convert hyp w
        apply Finset.sum_equiv (Fintype.equivFin I).symm <;>
        · intros
          simp
    · use U ∘ (Fintype.equivFin I).toFun
      constructor
      · intro i
        simpa using hU ((Fintype.equivFin I).toFun i)
      · intro w
        convert hyp w
        apply Finset.sum_equiv (Fintype.equivFin I) <;>
        · intros
          simp
