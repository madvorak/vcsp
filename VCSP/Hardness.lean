import VCSP.FractionalPolymorphisms
import VCSP.Expressibility
import Mathlib.Algebra.Order.SMul
import Mathlib.Data.Fin.VecNotation


section infoview_notation

@[app_unexpander List.map]
def List.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `map) $f)
  | _ => throw ()

@[app_unexpander List.take]
def List.take.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `take) $f)
  | _ => throw ()

@[app_unexpander List.drop]
def List.drop.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `drop) $f)
  | _ => throw ()

@[app_unexpander List.takeWhile]
def List.takeWhile.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `takeWhile) $f)
  | _ => throw ()

@[app_unexpander List.dropWhile]
def List.dropWhile.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `dropWhile) $f)
  | _ => throw ()

@[app_unexpander Multiset.map]
def Multiset.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ) => `($(μ).$(Lean.mkIdent `map) $f)
  | _ => throw ()

attribute [pp_dot] List.length List.get List.sum Multiset.sum
  Function.swap Sigma.fst Sigma.snd
  ValuedCsp.Term.evalSolution FractionalOperation.size FractionalOperation.tt

end infoview_notation


section push_higher

lemma univ_val_map_2x2 {α β : Type*} {f : (Fin 2 → α) → β} {a b c d : α} :
    Finset.univ.val.map (fun i => f (![![a, b], ![c, d]] i)) = [f ![a, b], f ![c, d]] :=
  rfl

lemma Multiset.sum_ofList_twice {M : Type*} [AddCommMonoid M] (x : M) :
    Multiset.sum ↑[x, x] = 2 • x := by
  simp [two_nsmul]

lemma column_of_2x2_left {α : Type*} (a b c d : α) :
    (fun i => ![![a, b], ![c, d]] i 0) = (fun i => ![a, c] i) := by
  ext i
  match i with
  | 0 => rfl
  | 1 => rfl

lemma column_of_2x2_right {α : Type*} (a b c d : α) :
    (fun i => ![![a, b], ![c, d]] i 1) = (fun i => ![b, d] i) := by
  ext i
  match i with
  | 0 => rfl
  | 1 => rfl

end push_higher


variable {D C : Type*}

lemma FractionalOperation.IsFractionalPolymorphismFor.expressivePower
    [OrderedAddCommMonoidWithInfima C] {Γ : ValuedCsp D C}
    {m : ℕ} {ω : FractionalOperation D m}
    (frop : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expressivePower := by
  intro f hf
  simp only [ValuedCsp.expressivePower, Set.mem_setOf_eq] at hf
  rcases hf with ⟨q, μ, I, rfl⟩
  unfold ValuedCsp.Instance.expresses
  unfold ValuedCsp.Instance.evalMinimize
  intro x
  -- TODO is `Multiset.smul_sum` really desirable here?
  rw [Multiset.smul_sum, Multiset.smul_sum, Multiset.map_map, Multiset.map_map]
  unfold FractionalOperation.IsFractionalPolymorphismFor at frop
  unfold Function.AdmitsFractional at frop
  show
    ((ω.tt x).map (fun y : Fin q → D =>
        m • sInf { κ | ∃ z, (I.map (fun t => t.evalSolution (Sum.elim y z))).sum = κ })
      ).sum ≤
    (Finset.univ.val.map (fun i : Fin m =>
        ω.size • sInf { κ | ∃ z, (I.map (fun t => t.evalSolution (Sum.elim (x i) z))).sum = κ })
      ).sum
  sorry

/-- Function `f` has Max-Cut property at labels `a` and `b` when `argmin f` is exactly:
   `{ ![a, b] , ![b, a] }` -/
def Function.HasMaxCutPropertyAt [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
  ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

/-- Function `f` has Max-Cut property at some two non-identical labels. -/
def Function.HasMaxCutProperty [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

lemma Function.HasMaxCutProperty.forbids_commutative [OrderedCancelAddCommMonoid C]
    {f : (Fin 2 → D) → C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
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
      · obtain ⟨g, _⟩ := valid.contains
        use fun i => g ((Function.swap ![![a, b], ![b, a]]) i)
        constructor
        · simp [FractionalOperation.tt]
          use g
        · apply rows_lt
          simp [FractionalOperation.tt]
          use g
    rw [two_nsmul, two_nsmul]
    exact add_lt_add half_sharp half_sharp
  have impos : 2 • (ω.map (fun _ => f ![a, b])).sum < ω.size • 2 • f ![a, b]
  · convert lt_of_lt_of_le sharp contr
    simp [FractionalOperation.tt, Multiset.map_map]
  have rhs_swap : ω.size • 2 • f ![a, b] = 2 • ω.size • f ![a, b]
  · apply nsmul_left_comm
  have distrib : (ω.map (fun _ => f ![a, b])).sum = ω.size • f ![a, b]
  · simp
  rw [rhs_swap, distrib] at impos
  exact ne_of_lt impos rfl
