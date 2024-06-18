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
    (A : W →ₗ[R] Fin m.succ → R) (y : W) : W →ₗ[R] Fin m → R :=
  ⟨⟨
    chop A - (A · ⟨m, lt_add_one m⟩ • chop A y),
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
    (A : W →ₗ[R] Fin m.succ → R) (b : W →ₗ[R] V) (y : W) : W →ₗ[R] V :=
  ⟨⟨
    b - (A · ⟨m, lt_add_one m⟩ • b y),
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
  rw [singlet, Finset.sum_attach _ (fun j : Fin m.succ => f j • v), Finset.sum_singleton]

private lemma impossible_index {m : ℕ} {i : Fin m.succ} (hi : ¬(i.val < m)) (i_neq_m : i ≠ ⟨m, lt_add_one m⟩) : False := by
  push_neg at hi
  exact i_neq_m (eq_of_le_of_le (Fin.succ_le_succ_iff.mp i.isLt) hi)

variable {R V W : Type*}

private lemma sum_nneg_aux {m : ℕ} [OrderedRing R]
    [OrderedAddCommGroup V] [Module R V] [PosSMulMono R V] [AddCommMonoid W] [Module R W]
    {A : W →ₗ[R] Fin m → R} {y : W} {x : Fin m → V} (hx : 0 ≤ x) (hAy : A y ≤ 0) :
    Finset.univ.sum (fun i : Fin m => A y i • x i) ≤ 0 := by
  rw [←neg_zero, ←le_neg, ←Finset.sum_neg_distrib]
  apply Finset.sum_nonneg
  intro i _
  rw [le_neg, neg_zero]
  exact smul_nonpos_of_nonpos_of_nonneg (hAy i) (hx i)

private lemma finishing_piece {m : ℕ} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    {A : W →ₗ[R] Fin m.succ → R} {w : W} {x : Fin m → V} :
    Finset.univ.sum (fun i : Fin m => chop A w i • x i) =
    (Finset.univ.filter _).attach.sum
      (fun i : { _i : Fin m.succ // _i ∈ Finset.univ.filter (·.val < m) } => A w i.val • x ⟨i.val.val, by aesop⟩) := by
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
      (∀ y₀ : W, A₀ y₀ ≤ 0 → b₀ y₀ ≤ 0) →
        (∃ x₀ : Fin m → V, 0 ≤ x₀ ∧ ∀ w₀ : W, b₀ w₀ = Finset.univ.sum (fun i₀ : Fin m => A₀ w₀ i₀ • x₀ i₀)))
    {A : W →ₗ[R] Fin m.succ → R} {b : W →ₗ[R] V} (hAb : ∀ y : W, A y ≤ 0 → b y ≤ 0) :
    ∃ x : Fin m.succ → V, 0 ≤ x ∧ ∀ w : W, b w = Finset.univ.sum (fun i : Fin m.succ => A w i • x i) := by
  if is_easy : ∀ y : W, chop A y ≤ 0 → b y ≤ 0 then
    obtain ⟨x, hx, hbx⟩ := ih (chop A) b is_easy
    use (fun i : Fin m.succ => if hi : i.val < m then x ⟨i.val, hi⟩ else 0)
    constructor
    · intro i
      if hi : i.val < m then
        clear * - hi hx
        aesop
      else
        simp [hi]
    · intro w
      simp_rw [smul_dite, smul_zero]
      rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
      convert hbx w using 1
      rw [finishing_piece]
  else
    push_neg at is_easy
    obtain ⟨y', hay', hby'⟩ := is_easy
    let j : Fin m.succ := ⟨m, lt_add_one m⟩
    let y := (A y' j)⁻¹ • y'
    have hAy' : 0 < A y' j
    · by_contra! contr
      exact (
        (hAb y' (fun i => if hi : i.val < m then hay' ⟨i, hi⟩ else if hij : i = j then hij ▸ contr else by
          exfalso
          exact impossible_index hi hij
        )).trans_lt hby'
      ).false
    have hAy : A y j = 1
    · convert inv_mul_cancel hAy'.ne.symm
      simp [y]
    have hAA : ∀ w : W, A (w - (A w j • y)) j = 0
    · intro w
      simp [hAy]
    have haAbA : ∀ w : W, chop A (w - (A w j • y)) ≤ 0 → b (w - (A w j • y)) ≤ 0
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
    have haaAbbA : ∀ w : W, chop A w - chop A (A w j • y) ≤ 0 → b w - b (A w j • y) ≤ 0
    · simpa using haAbA
    have haAabAb : ∀ w : W, (chop A - (A · j • chop A y)) w ≤ 0 → (b - (A · j • b y)) w ≤ 0
    · simpa using haaAbbA
    obtain ⟨x', hx', hbx'⟩ := ih (auxLinMaps A y) (auxLinMap A b y) haAabAb
    use (fun i : Fin m.succ => if hi : i.val < m then x' ⟨i.val, hi⟩ else b y - Finset.univ.sum (fun i : Fin m => chop A y i • x' i))
    constructor
    · intro i
      if hi : i.val < m then
        clear * - hi hx'
        aesop
      else
        have hAy'inv : 0 ≤ (A y' j)⁻¹
        · exact (inv_pos_of_pos' hAy').le
        have hay : chop A y ≤ 0
        · simpa [y] using smul_nonpos_of_nonneg_of_nonpos hAy'inv hay'
        have hby : 0 ≤ b y
        · simpa [y] using smul_nonneg hAy'inv hby'.le
        simpa [hi] using (sum_nneg_aux hx' hay).trans hby
    · intro w
      have key : b w - A w j • b y = Finset.univ.sum (fun i : Fin m => (chop A w i - A w j * chop A y i) • x' i)
      · simpa using hbx' w
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
    (∃ x : Fin n → V, 0 ≤ x ∧ ∀ w : W, b w = Finset.univ.sum (fun j : Fin n => A w j • x j)) ≠ (∃ y : W, A y ≤ 0 ∧ 0 < b y) := by
  apply neq_of_iff_neg
  push_neg -- TODO maybe try to rephrase the induction step with `∃ y` and then simplify this proof
  constructor
  · intro ⟨x, hx, hb⟩ y hy
    rw [hb]
    exact sum_nneg_aux hx hy
  · induction n generalizing b with -- note that `A` is "generalized" automatically
    | zero =>
      have A_tauto (w : W) : A w ≤ 0
      · intro j
        exfalso
        apply Nat.not_lt_zero
        exact j.isLt
      intro hAb
      refine ⟨0, le_refl 0, fun y : W => ?_⟩
      simp_rw [Pi.zero_apply, smul_zero, Finset.sum_const_zero]
      apply eq_of_le_of_le
      · exact hAb y (A_tauto y)
      · simpa using hAb (-y) (A_tauto (-y))
    | succ m ih =>
      exact industepFarkasBartl ih

theorem fintypeFarkasBartl {J : Type*} [Fintype J] [LinearOrderedDivisionRing R]
    [LinearOrderedAddCommGroup V] [Module R V] [PosSMulMono R V] [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] J → R) (b : W →ₗ[R] V) :
    (∃ x : J → V, 0 ≤ x ∧ ∀ w : W, b w = Finset.univ.sum (fun j : J => A w j • x j)) ≠ (∃ y : W, A y ≤ 0 ∧ 0 < b y) := by
  convert
    finFarkasBartl ⟨⟨fun w : W => fun j' => A w ((Fintype.equivFin J).symm j'), by aesop⟩, by aesop⟩ b
      using 1
  · constructor <;> intro ⟨x, hx, hyp⟩
    · use x ∘ (Fintype.equivFin J).invFun
      constructor
      · intro j
        simpa using hx ((Fintype.equivFin J).invFun j)
      · intro w
        convert hyp w
        apply Finset.sum_equiv (Fintype.equivFin J).symm <;>
        · intros
          simp
    · use x ∘ (Fintype.equivFin J).toFun
      constructor
      · intro j
        simpa using hx ((Fintype.equivFin J).toFun j)
      · intro w
        convert hyp w
        apply Finset.sum_equiv (Fintype.equivFin J) <;>
        · intros
          simp
  · constructor <;> intro ⟨y, hAy, hby⟩ <;> refine ⟨y, fun j => ?_, hby⟩
    · simpa using hAy ((Fintype.equivFin J).invFun j)
    · simpa using hAy ((Fintype.equivFin J).toFun j)
