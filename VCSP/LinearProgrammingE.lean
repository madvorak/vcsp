import Mathlib.Algebra.Order.Pi
import VCSP.FarkasSpecial

open scoped Matrix

/-- Linear program over `ℚ∞` in the standard form (system of linear inequalities with nonnegative `ℚ` variables).
    Variables are of type `J`. Conditions are indexed by type `I`. -/
structure ExtendedLP (I J : Type*) where
  /-- The left-hand-side matrix. -/
  A : Matrix I J ℚ∞
  /-- The right-hand-side vector. -/
  b : I → ℚ∞
  /-- The objective function coefficients. -/
  c : J → ℚ∞
  /-- No `⊥` and `⊤` in the same row. -/
  hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤)
  /-- No `⊥` and `⊤` in the same column. -/
  hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤)
  /-- No `⊤` in the right-hand-side vector. -/
  hbi : ¬∃ i : I, b i = ⊤
  /-- No `⊥` in the objective function coefficients. -/
  hcj : ¬∃ j : J, c j = ⊥
  /-- No `⊥` in the row where the right-hand-side vector has `⊥`. -/
  hAb : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥
  /-- No `⊤` in the column where the objective function has `⊤`. -/
  hAc : ¬∃ j : J, (∃ i : I, A i j = ⊤) ∧ c j = ⊤

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and its
    multiplication by matrix `A` from the left yields a vector whose all entries are less or equal
    to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution (P : ExtendedLP I J) (x : J → ℚ) : Prop :=
  P.A ₘ* x ≤ P.b ∧ 0 ≤ x -- Do not refactor to `x : J → ℚ≥0` even tho it would look nicer here!

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`.
    Linear program `P` is considered feasible even if all solutions yield `⊥` as the objective. -/
def ExtendedLP.IsFeasible (P : ExtendedLP I J) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. Note that `⊤` can be reached but `⊥` cannot. -/
def ExtendedLP.Reaches (P : ExtendedLP I J) (r : ℚ∞) : Prop :=
  ∃ x : J → ℚ, P.IsSolution x ∧ P.c ᵥ⬝ x = r

/-- Linear program `P` is bounded by `r` iff all values reached by `P` are less or equal to `r`. -/
def ExtendedLP.IsBoundedBy (P : ExtendedLP I J) (r : ℚ) : Prop :=
  ∀ p : ℚ∞, P.Reaches p → p ≤ r.toERat

open scoped Classical in
/-- Extended notion of "maximum" of LP. -/
noncomputable def ExtendedLP.optimum (P : ExtendedLP I J) : Option ℚ∞ :=
  if P.IsFeasible then
    if ∃ u : ℚ, P.IsBoundedBy u then
      if hr : ∃ r : ℚ, P.Reaches r.toERat ∧ P.IsBoundedBy r then
        hr.choose -- the "maximum"
      else
        none -- invalid finite value (supremum is not attained; later, we prove it cannot happen)
    else
      some ⊤ -- unbounded
  else
    some ⊥ -- infeasible

/-- `PolarOpposites p q` essentially says `p = -q` where `none` is forbidden. -/
def PolarOpposites : Option ℚ∞ → Option ℚ∞ → Prop
| (p : ℚ), (q : ℚ) => p + q = 0
| some ⊥ , some ⊤  => True
| some ⊤ , some ⊥  => True
| _      , _       => False -- namely `none ≠ -none`

lemma opposites_of_neg {r s : ℚ∞} (hrs : -r = s) : PolarOpposites (some r) (some s) := by
  match r with
  | ⊥ =>
    have hs : s = ⊤
    · symm
      simpa using hrs
    rw [hs]
    trivial
  | ⊤ =>
    have hs : s = ⊥
    · symm
      simpa using hrs
    rw [hs]
    trivial
  | (p : ℚ) =>
    match s with
    | ⊥ =>
      exfalso
      simp at hrs
    | ⊤ =>
      exfalso
      simp at hrs
    | (q : ℚ) =>
      have hpq : p + q = 0
      · cases hrs
        apply add_right_neg
      trivial

lemma opposites_comm (p q : Option ℚ∞) : PolarOpposites p q ↔ PolarOpposites q p := by
  match p with
  | none | some ⊥ | some ⊤ =>
    match q with
    | none | some ⊥ | some ⊤ | some (_ : ℚ) => rfl
  | some (p' : ℚ) =>
    match q with
    | none | some ⊥ | some ⊤ => rfl
    | some (q' : ℚ) => exact (add_comm p' q').congr_left

/-- Note that `ExtendedLP.dualize` is significantly different from `StandardLP.dualize`;
    here we keep maximizing in the dual problem but the sign is flipped;
    as a result, `ExtendedLP.dualize` is involution (good),
    but the strong LP duality can no longer be written as equality (bad);
    also, assumptions are bundled into the definition here. -/
def ExtendedLP.dualize (P : ExtendedLP I J) : ExtendedLP J I :=
  ⟨ -P.Aᵀ
  , -P.c
  , -P.b
  , by
      intro ⟨j, hbot, htop⟩
      apply P.hAj
      use j
      constructor
      · convert htop using 2
        simp
      · convert hbot using 2
        simp
  , by
      intro ⟨i, hbot, htop⟩
      apply P.hAi
      use i
      constructor
      · convert htop using 2
        simp
      · convert hbot using 2
        simp
  , by
      intro ⟨j, hj⟩
      apply P.hcj
      use j
      simpa using hj
  , by
      intro ⟨i, hi⟩
      apply P.hbi
      use i
      simpa using hi
  , by
      intro ⟨j, hAj, hcj⟩
      apply P.hAc
      use j
      constructor
      · convert hAj using 2
        simp
      · simpa using hcj
  , by
      intro ⟨i, hAi, hbi⟩
      apply P.hAb
      use i
      constructor
      · convert hAi using 2
        simp
      · simpa using hbi
  ⟩

lemma ExtendedLP.dualize_dualize (P : ExtendedLP I J) : P.dualize.dualize = P := by
  obtain ⟨A, b, c⟩ := P
  simp [ExtendedLP.dualize, ←Matrix.ext_iff]

lemma ExtendedLP.strongDuality_of_both_feas {P : ExtendedLP I J} (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    PolarOpposites P.optimum P.dualize.optimum := by
  cases
    or_of_neq
      (@extendedFarkas _ _ _ _
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.row (Sum.elim (-P.c) P.b)))
        (Sum.elim (Sum.elim P.b (-P.c)) 0)
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              rw [Matrix.fromRows_apply_inl] at hks hkt
              apply P.hAi
              use i
              constructor
              · cases s with
                | inl jₛ =>
                  use jₛ
                  simpa using hks
                | inr iₛ =>
                  exfalso
                  simp at hks
              · cases t with
                | inl jₜ =>
                  use jₜ
                  simpa using hkt
                | inr iₜ =>
                  exfalso
                  simp at hkt
            | inr j =>
              rw [Matrix.fromRows_apply_inl] at hks hkt
              apply P.hAj
              use j
              constructor
              · cases t with
                | inl jₜ =>
                  exfalso
                  simp at hkt
                | inr iₜ =>
                  use iₜ
                  simpa using hkt
              · cases s with
                | inl jₛ =>
                  exfalso
                  simp at hks
                | inr iₛ =>
                  use iₛ
                  simpa using hks
          | inr _ =>
            rw [Matrix.fromRows_apply_inr, Matrix.row_apply] at hks hkt
            cases t with
            | inl jₜ =>
              rw [Sum.elim_inl, Pi.neg_apply, ERat.neg_eq_top_iff] at hkt
              apply P.hcj
              use jₜ
            | inr iₜ =>
              rw [Sum.elim_inr] at hkt
              apply P.hbi
              use iₜ
        )
        sorry sorry sorry) with
  | inl case_x =>
    obtain ⟨x, hx, hAx⟩ := case_x
    have hPx : P.Reaches (P.c ᵥ⬝ x ∘ Sum.inl)
    · sorry
    have hQx : P.dualize.Reaches (- (P.b ᵥ⬝ x ∘ Sum.inr))
    · sorry
    have hPopt : P.optimum = some (P.c ᵥ⬝ x ∘ Sum.inl)
    · sorry
    have hQopt : P.dualize.optimum = some (- (P.b ᵥ⬝ x ∘ Sum.inr))
    · sorry
    rw [hPopt, hQopt]
    apply opposites_of_neg
    apply congr_arg
    apply eq_of_le_of_le
    · sorry -- weak duality
    · rw [←add_zero (P.c ᵥ⬝ x ∘ Sum.inl)]
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
      rfl
  | inr case_y =>
    obtain ⟨y, hy, hAy, hbcy⟩ := case_y
    exfalso
    simp [Matrix.transpose_fromRows, Matrix.fromBlocks_transpose] at hAy
    have hcb : Matrix.col (Sum.elim (-P.c) P.b) ₘ* y ∘ Sum.inr = -(Sum.elim (y (Sum.inr ()) • P.c) (y (Sum.inr ()) • -P.b))
    · ext k
      sorry
    sorry

theorem ExtendedLP.strongDuality_of_prim_feas {P : ExtendedLP I J} (hP : P.IsFeasible) :
    PolarOpposites P.optimum P.dualize.optimum := by
  sorry

theorem ExtendedLP.strongDuality_of_dual_feas {P : ExtendedLP I J} (hP : P.dualize.IsFeasible) :
    PolarOpposites P.optimum P.dualize.optimum := by
  have result := P.dualize_dualize ▸ P.dualize.strongDuality_of_prim_feas hP
  rwa [opposites_comm]

theorem ExtendedLP.strongDuality {P : ExtendedLP I J} (hP : P.IsFeasible ∨ P.dualize.IsFeasible) :
    PolarOpposites P.optimum P.dualize.optimum :=
  hP.casesOn
    (fun primFeas => P.strongDuality_of_prim_feas primFeas)
    (fun dualFeas => P.strongDuality_of_dual_feas dualFeas)
