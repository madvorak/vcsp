import VCSP.Expressibility
import VCSP.FractionalPolymorphisms
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.Algebra.GroupPower.Order


lemma fractionalPolymorphism_expressivePower {D C : Type} {m k : ℕ}
    [Nonempty D] [OrderedAddCommMonoid C] [CompleteLattice C]
    {ω : FractionalOperation D m k} {Γ : ValuedCspTemplate D C}
    (frop : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expressivePower := by
  intro f hf
  simp only [ValuedCspTemplate.expressivePower, Set.mem_setOf_eq] at hf
  rcases hf with ⟨q, μ, I, rfl⟩
  simp only [ValuedCspInstance.expresses, ValuedCspInstance.evalMinimize]
  intro x
  simp only [ValuedCspInstance.evalPartial, ValuedCspInstance.evalSolution]
  rw [List.smul_sum, List.smul_sum, List.map_map, List.map_map]
  unfold FractionalOperation.IsFractionalPolymorphismFor at frop
  unfold Function.AdmitsFractional at frop
  unfold ValuedCspInstance at I
  dsimp only
  sorry

def Function.HasMaxCutPropertyAt {D C : Type} [OrderedAddCommMonoid C]
    (f : (Fin 2 → D) → C) (a b : D) : Prop := -- `argmin f` is exactly `{ ![a, b] , ![b, a] }`
  f ![a, b] = f ![b, a] ∧ ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

def Function.HasMaxCutPropertyAt' {D C : Type} [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  ∀ x : Fin 2 → D, f x ∈ lowerBounds (Set.range f) ↔ x = ![a, b] ∨ x = ![b, a]

example {D C : Type} [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) (a b : D) :
  f.HasMaxCutPropertyAt a b ↔ f.HasMaxCutPropertyAt' a b :=
by
  constructor
  · rintro ⟨heq, hmin⟩
    intro x
    constructor
    · intro hyp
      rw [mem_lowerBounds] at hyp
      simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hyp
      sorry
    · intro hyp
      cases hyp with
      | inl hab =>
        unfold lowerBounds
        simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq]
        intro y
        rw [hab]
        sorry
        /-convert (hmin (y 0) (y 1)).left
        exact List.ofFn_inj.mp rfl-/
      | inr hba =>
        unfold lowerBounds
        simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq]
        intro y
        rw [hba, ← heq]
        sorry
        /-convert (hmin (y 0) (y 1)).left
        exact List.ofFn_inj.mp rfl-/
  · intro mcp
    constructor
    · sorry
    · intro x y
      constructor
      · specialize mcp ![a, b]
        simp at mcp
        rw [mem_lowerBounds] at mcp
        simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at mcp
        apply mcp
        sorry
        sorry
      · intro habxy
        sorry

def Function.HasMaxCutProperty {D C : Type} [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

lemma two_nsmul_le_two_nsmul {C : Type} [LinearOrderedAddCommGroup C] {x y : C}
    (hyp : 2 • x ≤ 2 • y) : x ≤ y :=
  le_of_nsmul_le_nsmul (by decide) hyp

lemma two_nsmul_le_two_nsmul' {C : Type} [LinearOrderedAddCommMonoid C] {x y : C}
    [CovariantClass C C (· + ·) (· < ·)]
    (hyp : 2 • x ≤ 2 • y) : x ≤ y :=
  le_of_nsmul_le_nsmul (by decide) hyp

lemma two_nsmul_le_two_nsmul'' {C : Type} [OrderedAddCommMonoid C] {x y : C}
    [ContravariantClass ℕ C HSMul.hSMul LE.le]
    -- useless lemma but demonstrates what kind of assumptions (partial order...) we would like to work with
    (hyp : 2 • x ≤ 2 • y) : x ≤ y :=
  @ContravariantClass.elim ℕ C HSMul.hSMul LE.le _ _ _ _ hyp

lemma apply222tt {D : Type} (ω : FractionalOperation D 2 2) (a b c d : D) :
    ω.tt ![ ![a, b] , ![c, d] ] = ![ ![ ω ![a, c] 0 , ω ![b, d] 0 ] , ![ ω ![a, c] 1 , ω ![b, d] 1 ] ] := by
  ext i j
  match j with
  | 0 =>
    have h0 : ∀ k : Fin 2, ![ ![a, b] , ![c, d] ] k 0 = ![ a , c ] k
    · intro k
      match k with
      | 0 => rfl
      | 1 => rfl
    match i with
    | 0 => simp [FractionalOperation.tt, h0]
    | 1 => simp [FractionalOperation.tt, h0]
  | 1 =>
    have h1 : ∀ k : Fin 2, ![ ![a, b] , ![c, d] ] k 1 = ![ b , d ] k
    · intro k
      match k with
      | 0 => rfl
      | 1 => rfl
    match i with
    | 0 => simp [FractionalOperation.tt, h1]
    | 1 => simp [FractionalOperation.tt, h1]

lemma todo_name {C : Type} [OrderedAddCommMonoid C] [IsLeftCancelAdd C] {x x' y y' : C}
    (hxy : x + y ≤ x' + y') (hx : x > x') (hy : y > y') : False := by
  have impossible : x + y < x + y
  · apply hxy.trans_lt
    apply (OrderedAddCommMonoid.add_le_add_left y' y (le_of_lt hy) x').trans_lt
    rw [add_comm x', add_comm x]
    apply lt_of_le_of_ne
    · exact add_le_add (le_of_eq rfl) (le_of_lt hx)
    rw [add_ne_add_right]
    exact ne_of_lt hx
  exact LT.lt.false impossible

lemma Function.HasMaxCutProperty.forbids_commutative {D C : Type} [LinearOrderedAddCommMonoid C] [IsLeftCancelAdd C]
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  intro contr
  rcases mcf with ⟨a, b, hab, mcfab⟩
  have cclass : CovariantClass C C (· + ·) (· < ·) -- TODO refactor into a typeclass instance
  · constructor
    intro x y z hyz
    show x + y < x + z
    have hle : x + y ≤ x + z
    · exact add_le_add_left (le_of_lt hyz) x
    have hne : x + y ≠ x + z
    · intro contr
      apply LT.lt.ne hyz
      apply add_left_cancel
      exact contr
    exact Ne.lt_of_le hne hle
  have tt_le := two_nsmul_le_two_nsmul' (contr ![ ![a, b] , ![b, a] ])
  clear contr
  rw [
    show
      List.map (f ∘ ![ ![a, b] , ![b, a] ]) (List.finRange 2) =
      [ f ![a, b] , f ![b, a] ] by
      rfl,
    show
      List.sum [ f ![a, b] , f ![b, a] ] =
      f ![a, b] + f ![b, a] by
      simp,
    apply222tt,
    show ω ![b, a] = ω ![a, b] by
      apply symmega
      apply List.Perm.swap,
    show
      List.map (f ∘ ![ ![ ω ![a, b] 0 , ω ![a, b] 0 ], ![ ω ![a, b] 1 , ω ![a, b] 1 ]]) (List.finRange 2) =
      [ f ![ ω ![a, b] 0 , ω ![a, b] 0 ] , f ![ ω ![a, b] 1 , ω ![a, b] 1 ] ] by
      rfl,
    show
      List.sum [ f ![ ω ![a, b] 0 , ω ![a, b] 0 ] , f ![ ω ![a, b] 1 , ω ![a, b] 1 ] ] =
      f ![ ω ![a, b] 0, ω ![a, b] 0 ] + f ![ ω ![a, b] 1, ω ![a, b] 1 ] by
      simp
  ] at tt_le
  have wrong0 : f ![ω ![a, b] 0, ω ![a, b] 0] > f ![a, b]
  · obtain ⟨fle, fne⟩ := mcfab.right (ω ![a, b] 0) (ω ![a, b] 0)
    refine Ne.lt_of_le ?_neq0 fle
    intro equ
    rcases fne equ with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩ <;>
    · rw [← hb0] at ha0
      exact hab ha0
  have wrong1 : f ![ω ![a, b] 1, ω ![a, b] 1] > f ![b, a]
  · obtain ⟨fle, fne⟩ := mcfab.right (ω ![a, b] 1) (ω ![a, b] 1)
    rw [← mcfab.left]
    refine Ne.lt_of_le ?_neq1 fle
    intro equ
    rcases fne equ with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩ <;>
    · rw [← hb0] at ha0
      exact hab ha0
  exact todo_name tt_le wrong0 wrong1

lemma Function.HasMaxCutProperty.forbids_commutative' {D C : Type} [LinearOrderedAddCommMonoid C] [IsRightCancelAdd C]
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω :=
  let _ := AddCommSemigroup.IsRightCancelAdd.toIsLeftCancelAdd C;
  Function.HasMaxCutProperty.forbids_commutative mcf symmega

lemma Function.HasMaxCutProperty.forbids_commutative'' {D C : Type} [LinearOrderedAddCommMonoid C] [IsCancelAdd C]
    -- see also `AddCancelCommMonoid`
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω :=
  Function.HasMaxCutProperty.forbids_commutative mcf symmega

lemma Function.HasMaxCutProperty.forbids_commutative''' {D C : Type} [LinearOrderedAddCommGroup C]
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω :=
  Function.HasMaxCutProperty.forbids_commutative'' mcf symmega

theorem Function.HasMaxCutProperty.forbids_symmetric {D C : Type} [LinearOrderedAddCommMonoid C] [IsLeftCancelAdd C]
    {m k : ℕ} {f : (Fin 2 → D) → C} {ω : FractionalOperation D m k}
    (mcf : f.HasMaxCutProperty) (omega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  sorry
