import VCSP.FractionalPolymorphisms
import VCSP.Expressibility
import Mathlib.Algebra.Order.SMul
import Mathlib.Data.Fin.VecNotation


lemma univ_val_map_2x2 {α β : Type*} {f : (Fin 2 → α) → β} {a b c d : α} :
    Finset.univ.val.map (fun i => f (![![a, b], ![c, d]] i)) = [f ![a, b], f ![c, d]] :=
  rfl

lemma Multiset.sum_ofList_twice {M : Type*} [AddCommMonoid M] (x : M) :
    Multiset.sum ↑[x, x] = 2 • x :=
by -- not sure we want to keep this form
  convert (add_nsmul x 1 1).symm
  simp

lemma Multiset.sum_lt_sum {ι M : Type*}
    [OrderedAddCommMonoid M]
    [CovariantClass M M (· + ·) (· < ·)]
    {s : Multiset ι} {f g : ι → M}
    (all_le : ∀ i ∈ s, f i ≤ g i) (exists_lt : ∃ i ∈ s, f i < g i) :
    (s.map f).sum < (s.map g).sum :=
by -- TODO contribute to mathlib
  rcases s with ⟨l⟩
  simp only [quot_mk_to_coe'', coe_map, coe_sum]
  apply List.sum_lt_sum
  · exact all_le
  · exact exists_lt

lemma column_of_2x2_left {α : Type*} (a b c d : α) :
    (fun i => ![![a, b], ![c, d]] i 0) = (fun i => ![a, c] i) :=
by -- why not oneliner?
  ext i
  match i with
  | 0 => rfl
  | 1 => rfl

lemma column_of_2x2_right {α : Type*} (a b c d : α) :
    (fun i => ![![a, b], ![c, d]] i 1) = (fun i => ![b, d] i) :=
by -- why not oneliner?
  ext i
  match i with
  | 0 => rfl
  | 1 => rfl


variable {D C : Type*}

lemma FractionalOperation.IsFractionalPolymorphismFor.expressivePower
    [OrderedAddCommMonoid C] [CompleteLattice C]
    {m : ℕ} {ω : FractionalOperation D m} {Γ : ValuedCsp D C}
    (frop : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expressivePower := by
  intro f hf
  simp only [ValuedCsp.expressivePower, Set.mem_setOf_eq] at hf
  rcases hf with ⟨q, μ, I, rfl⟩
  simp only [ValuedCsp.Instance.expresses, ValuedCsp.Instance.evalMinimize]
  intro x
  simp only [ValuedCsp.Instance.evalPartial, ValuedCsp.Instance.evalSolution]
  rw [Multiset.smul_sum, Multiset.smul_sum, Multiset.map_map, Multiset.map_map]
  unfold FractionalOperation.IsFractionalPolymorphismFor at frop
  unfold Function.AdmitsFractional at frop
  unfold ValuedCsp.Instance at I
  dsimp only
  sorry

/-- Function `f` has Max-Cut property at labels `a` and `b` when `argmin f` is exactly:
   `{ ![a, b] , ![b, a] }` -/
def Function.HasMaxCutPropertyAt [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
  ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

/-- Function `f` has Max-Cut property at some two non-identical labels. -/
def Function.HasMaxCutProperty [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

lemma noo [OrderedCancelAddCommMonoid C] {x y z w : C} (hlt : x + z < y + w) (hzw : ¬ (z < w)) :
     x < y :=
/- Counterexample:
(1, 1) + (1, 1) < (0, 3) + (3, 0)
¬ (1, 1) < (3, 0)
¬ (1, 1) < (0, 3)
We will need stronger assumptions. OrderedCancelAddCommMonoid is not enough. -/
  sorry

lemma Function.HasMaxCutProperty.forbids_commutative [OrderedCancelAddCommMonoid C]
    {f : (Fin 2 → D) → C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  have ccCC : CovariantClass C C (· + ·) (· < ·) -- automatic?
  · exact AddLeftCancelSemigroup.covariant_add_lt_of_covariant_add_le C
  have osNC : OrderedSMul ℕ C -- overkill?
  · constructor
    · intro a b n hab hzn
      induction n with
      | zero => simp only at hzn
      | succ n ih =>
        rw [succ_nsmul, succ_nsmul]
        cases n with
        | zero => rwa [Nat.zero_eq, zero_smul, add_zero, zero_smul, add_zero]
        | succ n => exact add_lt_add hab (ih n.succ_pos)
    · intro a b n hnsmul hzn
      induction n with
      | zero => simp only at hzn
      | succ n ih =>
        rw [succ_nsmul, succ_nsmul] at hnsmul
        cases n with
        | zero => rwa [Nat.zero_eq, zero_smul, add_zero, zero_smul, add_zero] at hnsmul
        | succ n =>
          by_cases hyp : n.succ • a < n.succ • b
          · exact ih hyp n.succ_pos
          · exact noo hnsmul hyp
  intro contr
  rcases mcf with ⟨a, b, hab, mcfab⟩
  specialize contr ![![a, b], ![b, a]]
  rw [univ_val_map_2x2, ← mcfab.left, Multiset.sum_ofList_twice] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun r => f r)).sum
  · have rows_lt : ∀ r ∈ (ω.tt ![![a, b], ![b, a]]), f ![a, b] < f r
    · intro r rin
      rw [FractionalOperation.tt, Multiset.mem_map] at rin
      rcases rin with ⟨o, in_omega, eq_r⟩
      rw [show r = ![r 0, r 1] from List.ofFn_inj.mp rfl]
      apply lt_of_le_of_ne (mcfab.right (r 0) (r 1)).left
      intro equ
      have asymm : r 0 ≠ r 1
      · rcases (mcfab.right (r 0) (r 1)).right equ with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
        · rw [ha0, hb1] at hab
          exact hab
        · rw [ha1, hb0] at hab
          exact hab.symm
      apply asymm
      rw [← eq_r]
      show o (fun j => ![![a, b], ![b, a]] j 0) = o (fun j => ![![a, b], ![b, a]] j 1)
      rw [column_of_2x2_left, column_of_2x2_right]
      exact symmega ![a, b] ![b, a] (List.Perm.swap b a []) o in_omega
    have half_sharp :
      ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
      ((ω.tt ![![a, b], ![b, a]]).map (fun r => f r)).sum
    · apply Multiset.sum_lt_sum
      · intro r rin
        exact le_of_lt (rows_lt r rin)
      · rcases Multiset.exists_mem_of_ne_zero valid with ⟨g, _⟩
        use fun i => g ((Function.swap ![![a, b], ![b, a]]) i)
        constructor
        · simp [FractionalOperation.tt]
          use g
        · apply rows_lt
          simp [FractionalOperation.tt]
          use g
    -- Strictly speaking, we only need `x + x ≤ y + y` to imply `x ≤ y` here?
    -- Strictly speaking, we only need `x < y` to imply `x + x < y + y` here.
    exact smul_lt_smul_of_pos half_sharp (by decide)
  have impos : 2 • (ω.map (fun _ => f ![a, b])).sum < Multiset.card.toFun ω • 2 • f ![a, b]
  · convert lt_of_lt_of_le sharp contr
    simp [FractionalOperation.tt, Multiset.map_map]
  have rhs_swap : Multiset.card.toFun ω • 2 • f ![a, b] = 2 • Multiset.card.toFun ω • f ![a, b]
  · apply nsmul_left_comm
  have distrib : (ω.map (fun _ => f ![a, b])).sum = Multiset.card.toFun ω • f ![a, b]
  · simp
  rw [rhs_swap, distrib] at impos
  exact ne_of_lt impos rfl
