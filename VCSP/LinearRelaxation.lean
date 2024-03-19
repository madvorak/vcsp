import VCSP.Hardness
import VCSP.LinearProgramming
import Mathlib.Data.Multiset.Fintype

open scoped Matrix



lemma Matrix.fromBlocks_mulVec_sumType {α β γ δ R : Type*} [Semiring R]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : Matrix α β R) (B : Matrix α γ R) (C : Matrix δ β R) (D : Matrix δ γ R)
    (u : β → R) (v : γ → R) :
    Matrix.fromBlocks A B C D *ᵥ Sum.elim u v = Sum.elim (A *ᵥ u + B *ᵥ v) (C *ᵥ u + D *ᵥ v) := by
  rw [← Matrix.fromRows_fromColumn_eq_fromBlocks, Matrix.fromRows_mulVec,
    Matrix.fromColumns_mulVec_sum_elim, Matrix.fromColumns_mulVec_sum_elim]

-- Emilie (Shad Amethyst) stated this lemma:
lemma Finset.filter_univ_eq_image {α : Type*} [Fintype α] [DecidableEq α] {p : α → Prop} [DecidablePred p] :
    Finset.univ.filter p = (Finset.univ : Finset { a : α // p a }).image Subtype.val := by
  aesop

lemma Multiset.summap_to_sumFinset {α β : Type*} [DecidableEq α] [OrderedAddCommMonoid β]
    (S : Multiset α) (f : α → β) :
    S.summap f = Finset.univ.sum (fun a : S => f a.fst) := by
  simp [Multiset.summap, Finset.sum]

lemma neg_finset_univ_sum {α R : Type} [Fintype α] [Ring R] (f : α → R) :
    -(Finset.univ.sum f) = Finset.univ.sum (-f) := by
  simp only [Pi.neg_apply, Finset.sum_neg_distrib]

lemma indicator_of_neg {α R : Type} [Fintype α] [Ring R] (P : α → Prop) [DecidablePred P] :
    -(fun x => if P x then -1 else (0 : R)) = (fun x => if P x then 1 else 0) := by
  aesop

/-- Nonterminal `aesop` (strongly discouraged to use) -/
macro (name := aesopnt) "aesopnt" : tactic =>
  `(tactic| aesop (config := {warnOnNonterminal := false}))


variable
  {D : Type} [Fintype D] [DecidableEq D]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {C : Type} [LinearOrderedField C]
  {Γ : ValuedCSP D C} [DecidableEq (Γ.Term ι)]

instance deceqInstance (I : Γ.Instance ι) : DecidableEq I :=
  inferInstanceAs (DecidableEq (Σ t : Γ.Term ι, Fin (I.count t)))

@[pp_dot]
def ValuedCSP.Instance.RelaxBLP (I : Γ.Instance ι) :
    CanonicalLP
      ((Σ t : I, (Fin t.fst.n → D)) ⊕ ι × D) -- variables
      ((Σ t : I, (Fin t.fst.n × D)) ⊕ ι)     -- equalities
      C :=
  CanonicalLP.mk
    (Matrix.fromBlocks
      (Matrix.of fun ⟨cₜ, cₙ, cₐ⟩ => fun ⟨t, x⟩ =>
        if ht : cₜ = t
        then
          if x (@Fin.cast cₜ.fst.n t.fst.n (congr_arg (Term.n ∘ Sigma.fst) ht) cₙ) = cₐ
          then 1
          else 0
        else 0)
      (Matrix.of fun ⟨⟨cₜ, _⟩, cₙ, cₐ⟩ => fun ⟨i, a⟩ => if cₜ.app cₙ = i ∧ cₐ = a then -1 else 0)
      0
      (Matrix.of fun cᵢ : ι => fun ⟨i, _⟩ => if cᵢ = i then 1 else 0))
    (Sum.elim
      (fun _ : (Σ t : I, (Fin t.fst.n × D)) => 0)
      (fun _ : ι => 1))
    (Sum.elim
      (fun ⟨⟨t, _⟩, x⟩ => t.f x)
      (fun _ => 0))

@[pp_dot]
abbrev ValuedCSP.Instance.solutionVCSPtoBLP (I : Γ.Instance ι) (x : ι → D) :
    ((Σ t : I, (Fin t.fst.n → D)) ⊕ (ι × D)) → C :=
  Sum.elim
    (fun ⟨⟨t, _⟩, (v : (Fin t.n → D))⟩ => if ∀ i : Fin t.n, v i = x (t.app i) then 1 else 0)
    (fun ⟨i, d⟩ => if x i = d then 1 else 0)

lemma ValuedCSP.Instance.solutionVCSPtoBLP_nneg (I : Γ.Instance ι) (x : ι → D) :
    0 ≤ I.solutionVCSPtoBLP x := by
  unfold Pi.hasLe
  aesop

set_option maxHeartbeats 333333 in
lemma ValuedCSP.Instance.solutionVCSPtoBLP_cost (I : Γ.Instance ι) (x : ι → D) :
    I.RelaxBLP.c ⬝ᵥ I.solutionVCSPtoBLP x = I.evalSolution x := by
  simp [ValuedCSP.Instance.RelaxBLP, ValuedCSP.Instance.solutionVCSPtoBLP,
        ValuedCSP.Instance.evalSolution, ValuedCSP.Term.evalSolution, Matrix.dotProduct]
  show
    Finset.univ.sum
      (fun (⟨⟨t, _⟩, v⟩ : Σ _t : I, (Fin _t.fst.n → D)) =>
        t.f v * if (∀ i : Fin t.n, v i = x (t.app i)) then 1 else 0) =
    I.summap (fun t => t.f (fun i : Fin t.n => x (t.app i)))
  simp_rw [mul_ite, mul_one, mul_zero]
  show
    Finset.sum Finset.univ (fun (e : Σ t : I, (Fin t.fst.n → D)) =>
      if ∀ (i : Fin e.fst.fst.n), e.snd i = x (e.fst.fst.app i) then e.fst.fst.f e.snd else 0) =
    I.summap (fun t => t.f (fun i : Fin t.n => x (t.app i)))
  -- The rest of this proof is based on a proof by Emilie (Shad Amethyst):
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_univ_eq_image,
      Finset.sum_image (fun _ _ _ _ equ => Subtype.coe_injective equ), Multiset.summap_to_sumFinset]
  apply Finset.sum_equiv ⟨
      fun ⟨⟨⟨t, m⟩, _⟩, _⟩ => ⟨t, m, Fin.prop m⟩,
      fun t => ⟨⟨t, fun i => x (t.fst.app i)⟩, fun _ => rfl⟩,
      fun _ => by aesopnt; ext i; exact (property i).symm,
      fun _ => by aesop⟩
  · aesop
  · aesopnt
    congr
    ext
    simp_all

set_option maxHeartbeats 666666 in
lemma ValuedCSP.Instance.RelaxBLP_solutionVCSPtoBLP_top_left_of_hit (I : Γ.Instance ι)
    {cₜ : Σ t : Γ.Term ι, Fin (I.count t)} {cₙ : Fin cₜ.fst.n} {cₐ : D} {x : ι → D}
    (hit : x (cₜ.fst.app cₙ) = cₐ) :
    (fun ⟨t, y⟩ =>
      if ht : cₜ = t
      then
        if y (@Fin.cast cₜ.fst.n t.fst.n (congr_arg (Term.n ∘ Sigma.fst) ht) cₙ) = cₐ
        then 1
        else 0
      else 0
      ) ⬝ᵥ (I.solutionVCSPtoBLP x ∘ Sum.inl) =
    1 := by
  rw [Sum.elim_comp_inl, Matrix.dotProduct]
  show
    -- DO NOT refactor to `fun (⟨t, y⟩ : Σ t : I, (Fin t.fst.n → D))` as it would hinder aesop
    -- TODO check whether still the case
    Finset.univ.sum (fun (tᵥ : Σ t : I, (Fin t.fst.n → D)) =>
      (match tᵥ with
        | ⟨t, v⟩ =>
          if ht : cₜ = t
          then
            if v (Fin.cast (congr_arg (Term.n ∘ Sigma.fst) ht) cₙ) = cₐ
            then 1
            else 0
          else 0
        ) *
      (match tᵥ with
        | ⟨t, v⟩ =>
          if (∀ i : Fin t.fst.n, v i = x (t.fst.app i))
          then 1
          else 0
        )
      ) =
    (1 : C)
  simp_rw [mul_ite, mul_one, mul_zero]
  convert_to
    Finset.univ.sum (fun (tᵥ : Σ t : I, (Fin t.fst.n → D)) =>
      (match tᵥ with
        | ⟨t, v⟩ =>
          if (
            if (∀ i : Fin t.fst.n, v i = x (t.fst.app i))
            then
              if ht : cₜ = t
              then
                if v (Fin.cast (congr_arg (Term.n ∘ Sigma.fst) ht) cₙ) = cₐ
                then True
                else False
              else False
            else False
          )
          then 1
          else 0
      )) =
    (1 : C)
        using 2
  · aesop
  rw [Finset.sum_boole, Nat.cast_eq_one, Finset.card_eq_one]
  use ⟨cₜ, x ∘ cₜ.fst.app⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor <;> aesop

lemma ValuedCSP.Instance.RelaxBLP_solutionVCSPtoBLP_top_left_of_miss (I : Γ.Instance ι)
    {cₜ : Σ t : Γ.Term ι, Fin (I.count t)} {cₙ : Fin cₜ.fst.n} {cₐ : D} {x : ι → D}
    (miss : x (cₜ.fst.app cₙ) ≠ cₐ) :
    (fun ⟨t, y⟩ =>
      if ht : cₜ = t
      then
        if y (@Fin.cast cₜ.fst.n t.fst.n (congr_arg (Term.n ∘ Sigma.fst) ht) cₙ) = cₐ
        then 1
        else 0
      else 0
      ) ⬝ᵥ (I.solutionVCSPtoBLP x ∘ Sum.inl) =
    0 := by
  rw [Sum.elim_comp_inl, Matrix.dotProduct]
  show
    Finset.univ.sum (fun (tᵥ : Σ t : I, (Fin t.fst.n → D)) =>
      (match tᵥ with
        | ⟨t, v⟩ =>
          if ht : cₜ = t
          then
            if v (Fin.cast (congr_arg (Term.n ∘ Sigma.fst) ht) cₙ) = cₐ
            then 1
            else 0
          else 0
        ) *
      (match tᵥ with
        | ⟨t, v⟩ =>
          if (∀ i : Fin t.fst.n, v i = x (t.fst.app i))
          then 1
          else 0
        )
      ) =
    (0 : C)
  simp_rw [mul_ite, mul_one, mul_zero]
  convert_to
    Finset.univ.sum (fun (tᵥ : Σ t : I, (Fin t.fst.n → D)) =>
      (match tᵥ with
        | ⟨t, v⟩ =>
          if (
            if (∀ i : Fin t.fst.n, v i = x (t.fst.app i))
            then
              if ht : cₜ = t
              then
                if v (Fin.cast (congr_arg (Term.n ∘ Sigma.fst) ht) cₙ) = cₐ
                then True
                else False
              else False
            else False
          )
          then 1
          else 0
      )) =
    (0 : C)
        using 2
  · aesop
  rw [Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro _ _
  aesop

lemma ValuedCSP.Instance.RelaxBLP_solutionVCSPtoBLP_top_right_of_hit (I : Γ.Instance ι)
    {cₜ : Σ t : Γ.Term ι, Fin (I.count t)} {cₙ : Fin cₜ.fst.n} {cₐ : D} {x : ι → D}
    (hit : x (cₜ.fst.app cₙ) = cₐ) :
    (fun ⟨i, a⟩ => if cₜ.fst.app cₙ = i ∧ cₐ = a then -1 else 0) ⬝ᵥ (I.solutionVCSPtoBLP x ∘ Sum.inr) = -1 := by
  rw [Sum.elim_comp_inr, Matrix.dotProduct]
  simp_rw [mul_ite, mul_one, mul_zero, ←ite_and]
  rw [←neg_eq_iff_eq_neg, neg_finset_univ_sum, indicator_of_neg]
  rw [Finset.sum_boole, Nat.cast_eq_one, Finset.card_eq_one]
  use (cₜ.fst.app cₙ, cₐ)
  aesop

lemma ValuedCSP.Instance.RelaxBLP_solutionVCSPtoBLP_top_right_of_miss (I : Γ.Instance ι)
    {cₜ : Σ t : Γ.Term ι, Fin (I.count t)} {cₙ : Fin cₜ.fst.n} {cₐ : D} {x : ι → D}
    (miss : x (cₜ.fst.app cₙ) ≠ cₐ) :
    (fun ⟨i, a⟩ => if cₜ.fst.app cₙ = i ∧ cₐ = a then -1 else 0) ⬝ᵥ (I.solutionVCSPtoBLP x ∘ Sum.inr) = -0 := by
  rw [Sum.elim_comp_inr, Matrix.dotProduct]
  simp_rw [mul_ite, mul_one, mul_zero, ←ite_and]
  rw [←neg_eq_iff_eq_neg, neg_finset_univ_sum, indicator_of_neg, Finset.sum_boole]
  aesop

lemma ValuedCSP.Instance.RelaxBLP_solutionVCSPtoBLP_bottom_right (I : Γ.Instance ι)
    (cᵢ : ι) (x : ι → D) :
    (fun ⟨i, _⟩ => if cᵢ = i then 1 else 0) ⬝ᵥ (I.solutionVCSPtoBLP x ∘ Sum.inr) = 1 := by
  rw [Sum.elim_comp_inr, Matrix.dotProduct]
  simp_rw [mul_ite, mul_one, mul_zero, ←ite_and]
  rw [Finset.sum_boole, Nat.cast_eq_one, Finset.card_eq_one]
  use (cᵢ, x cᵢ)
  aesop

theorem ValuedCSP.Instance.RelaxBLP_reaches (I : Γ.Instance ι) (x : ι → D) :
    I.RelaxBLP.Reaches (I.evalSolution x) := by
  use I.solutionVCSPtoBLP x
  constructor
  · simp only [CanonicalLP.IsSolution, ValuedCSP.Instance.RelaxBLP]
    constructor
    · ext j
      rw [Matrix.fromBlocks_mulVec_sumType]
      rw [Matrix.zero_mulVec, zero_add]
      cases j with
      | inl c =>
        obtain ⟨cₜ, cₙ, cₐ⟩ := c
        rw [Sum.elim_inl, Sum.elim_inl, Pi.add_apply]
        if hits : x (cₜ.fst.app cₙ) = cₐ then
          convert @add_neg_self C _ 1
          · exact I.RelaxBLP_solutionVCSPtoBLP_top_left_of_hit hits
          · exact I.RelaxBLP_solutionVCSPtoBLP_top_right_of_hit hits
        else
          convert @add_neg_self C _ 0
          · exact I.RelaxBLP_solutionVCSPtoBLP_top_left_of_miss hits
          · exact I.RelaxBLP_solutionVCSPtoBLP_top_right_of_miss hits
      | inr cᵢ =>
        rw [Sum.elim_inr, Sum.elim_inr]
        exact I.RelaxBLP_solutionVCSPtoBLP_bottom_right cᵢ x
    · exact I.solutionVCSPtoBLP_nneg x
  · exact I.solutionVCSPtoBLP_cost x
