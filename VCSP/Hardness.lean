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
    (f : (Fin 2 → D) → C) (a b : D) : Prop := -- `argmin f` is exactly `{ ![a, b], ![b, a] }`
  f ![a, b] = f ![b, a] ∧ ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

def Function.HasMaxCutProperty {D C : Type} [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

lemma two_nsmul_le_two_nsmul {C : Type} [LinearOrderedAddCommGroup C] {x y : C}
    (hyp : 2 • x ≤ 2 • y) : x ≤ y :=
  le_of_nsmul_le_nsmul (by decide) hyp

lemma two_nsmul_le_two_nsmul_ {C : Type} [LinearOrderedAddCommMonoid C] {x y : C}
    [CovariantClass C C (· + ·) (· < ·)]
    [CovariantClass C C (Function.swap (· + ·)) (· < ·)]
    (hyp : 2 • x ≤ 2 • y) : x ≤ y :=
  le_of_nsmul_le_nsmul (by decide) hyp

lemma two_smul_le_two_smul {C : Type} [OrderedAddCommMonoid C] {x y : C}
    (hyp : 2 • x ≤ 2 • y) : x ≤ y := by
  -- Does not hold this way!!!
  sorry

lemma apply222tt {D : Type} (ω : FractionalOperation D 2 2) (a b c d : D) :
    ω.tt ![ ![a, b] , ![c, d] ] = ![ ![ ω ![a, c] 0 , ω ![b, d] 0 ] , ![ ω ![a, c] 1 , ω ![b, d] 1 ] ] := by
  ext i j
  simp only [FractionalOperation.tt]
  match j with
  | 0 =>
    show ω (fun i => ![ ![a, b] , ![c, d] ] i 0) i = ![ ![ω ![a, c] 0, ω ![b, d] 0], ![ω ![a, c] 1, ω ![b, d] 1]] i 0
    have i0 : ∀ i : Fin 2, ![ ![a, b] , ![c, d] ] i 0 = ![ a , c ] i
    · intro i 
      match i with
      | 0 => rfl
      | 1 => rfl
    simp [i0]
    /-have ii : ![ ![ω ![a, c] 0, ω ![b, d] 0], ![ω ![a, c] 1, ω ![b, d] 1]] i 0 = ![ ω ![a, c] 0, ω ![a, c] 1] i
    · match i with
      | 0 => rfl
      | 1 => rfl
    simp [ii]-/
    match i with
    | 0 => simp
    | 1 => simp
  | 1 => 
    have i1 : ∀ i : Fin 2, ![ ![a, b] , ![c, d] ] i 1 = ![ b , d ] i
    · intro i 
      match i with
      | 0 => rfl
      | 1 => rfl
    simp [i1]
    match i with
    | 0 => simp
    | 1 => simp

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

lemma Function.HasMaxCutProperty.forbids_commutative {D C : Type} [OrderedAddCommMonoid C] [IsLeftCancelAdd C]
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  intro contr
  rcases mcf with ⟨a, b, hab, mcfab⟩
  have tt_le := two_smul_le_two_smul (contr ![ ![a, b] , ![b, a] ])
  clear contr
  have same_output : ω ![b, a] = ω ![a, b]
  · apply symmega
    apply List.Perm.swap
  rw [
    show
      List.map (f ∘ ![ ![a, b] , ![b, a] ]) (List.finRange 2) =
      [ f ![a, b] , f ![b, a] ] by rfl,
    show
      List.sum [ f ![a, b] , f ![b, a] ] =
      f ![a, b] + f ![b, a] by simp,
    apply222tt,
    same_output,
    show
      List.map (f ∘ ![ ![ ω ![a, b] 0 , ω ![a, b] 0 ], ![ ω ![a, b] 1 , ω ![a, b] 1 ]]) (List.finRange 2) =
      [ f ![ ω ![a, b] 0 , ω ![a, b] 0 ] , f ![ ω ![a, b] 1 , ω ![a, b] 1 ] ] by rfl,
    show
      List.sum [ f ![ ω ![a, b] 0 , ω ![a, b] 0 ] , f ![ ω ![a, b] 1 , ω ![a, b] 1 ] ] =
      f ![ ω ![a, b] 0, ω ![a, b] 0 ] + f ![ ω ![a, b] 1, ω ![a, b] 1 ] by simp
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

lemma Function.HasMaxCutProperty.forbids_commutative' {D C : Type} [OrderedAddCommMonoid C] [IsRightCancelAdd C]
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω :=
  let _ := AddCommSemigroup.IsRightCancelAdd.toIsLeftCancelAdd C;
  Function.HasMaxCutProperty.forbids_commutative mcf symmega

lemma Function.HasMaxCutProperty.forbids_commutative'' {D C : Type} [OrderedAddCommMonoid C] [IsCancelAdd C]
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω :=
  Function.HasMaxCutProperty.forbids_commutative mcf symmega

lemma Function.HasMaxCutProperty.forbids_commutative''' {D C : Type} [OrderedAddCommGroup C]
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω :=
  Function.HasMaxCutProperty.forbids_commutative'' mcf symmega

theorem Function.HasMaxCutProperty.forbids_symmetric {D C : Type} [OrderedAddCommMonoid C]
    {m k : ℕ} {f : (Fin 2 → D) → C} {ω : FractionalOperation D m k}
    (mcf : f.HasMaxCutProperty) (omega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  sorry
