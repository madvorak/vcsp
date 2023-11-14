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
    [CovariantClass M M (· + ·) (· ≤ ·)]
    [CovariantClass M M (· + ·) (· < ·)]
    {s : Multiset ι} {f g : ι → M}
    (all_le : ∀ i ∈ s, f i ≤ g i) (exists_lt : ∃ i ∈ s, f i < g i) :
    (s.map f).sum < (s.map g).sum :=
by -- TODO move elsewhere
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


variable {D C : Type*} [OrderedAddCommMonoid C]

lemma FractionalOperation.IsFractionalPolymorphismFor.expressivePower {m : ℕ} [CompleteLattice C]
    {ω : FractionalOperation D m} {Γ : ValuedCsp D C}
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
def Function.HasMaxCutPropertyAt (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
    ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

/-- Function `f` has Max-Cut property at some two non-identical labels. -/
def Function.HasMaxCutProperty (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

lemma Function.HasMaxCutProperty.forbids_commutative -- TODO use `OrderedCancelAddCommMonoid`
    [CovariantClass C C (· + ·) (· < ·)] [OrderedSMul ℕ C]
    {f : (Fin 2 → D) → C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  rcases mcf with ⟨a, b, hab, mcfab⟩
  intro contr
  specialize contr ![![a, b], ![b, a]]
  -- on each row `r` we have `f r.fst > f a b = f b a`
  rw [univ_val_map_2x2, ←mcfab.left, Multiset.sum_ofList_twice] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun r => r.snd • f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun r => r.snd • f r.fst)).sum
  · obtain ⟨nonempty, nonzeros⟩ := valid
    have rows_lt : ∀ r ∈ (ω.tt ![![a, b], ![b, a]]), r.snd • f ![a, b] < r.snd • f r.fst
    · intro r rin
      rw [FractionalOperation.tt, Multiset.mem_map, Prod.exists] at rin
      rcases rin with ⟨o, w, in_omega, eq_r⟩
      have rsnd_pos : 0 < r.snd
      · rw [← eq_r]
        exact Nat.pos_of_ne_zero (nonzeros (o, w) in_omega)
      have key : f ![a, b] < f r.fst
      · rw [show r.1 = ![r.fst 0, r.fst 1] from List.ofFn_inj.mp rfl]
        apply lt_of_le_of_ne (mcfab.right (r.fst 0) (r.fst 1)).left
        intro equ
        have asymm : r.fst 0 ≠ r.fst 1
        · rcases (mcfab.right (r.fst 0) (r.fst 1)).right equ with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
          · rw [ha0, hb1] at hab
            exact hab
          · rw [ha1, hb0] at hab
            exact hab.symm
        apply asymm
        rw [← eq_r]
        show o (fun j => ![![a, b], ![b, a]] j 0) = o (fun j => ![![a, b], ![b, a]] j 1)
        rw [column_of_2x2_left, column_of_2x2_right]
        exact symmega ![a, b] ![b, a] (List.Perm.swap b a []) (o, w) in_omega
      exact smul_lt_smul_of_pos key rsnd_pos
    have half_sharp :
      ((ω.tt ![![a, b], ![b, a]]).map (fun r => r.snd • f ![a, b])).sum <
      ((ω.tt ![![a, b], ![b, a]]).map (fun r => r.snd • f r.fst)).sum
    · apply Multiset.sum_lt_sum
      · intro r rin
        exact le_of_lt (rows_lt r rin)
      · obtain ⟨g, gin⟩ := Multiset.exists_mem_of_ne_zero nonempty
        use weightedApplication g (Function.swap ![![a, b], ![b, a]])
        constructor
        · apply weightedApplication_in gin
        · apply rows_lt
          apply weightedApplication_in gin
    exact smul_lt_smul_of_pos half_sharp (by decide)
  have impos : 2 • (ω.map (fun r => r.snd • f ![a, b])).sum < (ω.map Prod.snd).sum • 2 • f ![a, b]
  · convert lt_of_lt_of_le sharp contr
    simp [FractionalOperation.tt, weightedApplication, Multiset.map_map]
  have rhs_swap : (ω.map Prod.snd).sum • 2 • f ![a, b] = 2 • (ω.map Prod.snd).sum • f ![a, b]
  · apply nsmul_left_comm
  have distrib : (ω.map (fun r => r.snd • f ![a, b])).sum = (ω.map Prod.snd).sum • f ![a, b]
  · rw [Multiset.sum_smul, Multiset.map_map]
    rfl
  rw [rhs_swap, distrib] at impos
  exact ne_of_lt impos rfl
