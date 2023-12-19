import VCSP.FractionalPolymorphisms
import VCSP.Expressibility
import Mathlib.Algebra.Order.SMul
import Mathlib.Data.Fin.VecNotation


@[simp]
abbrev Multiset.summap {α β : Type*} [AddCommMonoid β] (s : Multiset α) (f : α → β) : β :=
  (s.map f).sum


section better_notation

/-- Given `n : ℕ` and `l : List α`, print `List.take n l` as `l.take n` in Infoview. -/
@[app_unexpander List.take]
def List.take.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `take) $n)
  | _ => throw ()

/-- Given `n : ℕ` and `l : List α`, print `List.drop n l` as `l.drop n` in Infoview. -/
@[app_unexpander List.drop]
def List.drop.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `drop) $n)
  | _ => throw ()

/-- Given `p : α → Bool` and `l : List α`, print `List.takeWhile p l` as `l.takeWhile p` in Infoview. -/
@[app_unexpander List.takeWhile]
def List.takeWhile.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $p $l) => `($(l).$(Lean.mkIdent `takeWhile) $p)
  | _ => throw ()

/-- Given `p : α → Bool` and `l : List α`, print `List.dropWhile p l` as `l.dropWhile p` in Infoview. -/
@[app_unexpander List.dropWhile]
def List.dropWhile.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $p $l) => `($(l).$(Lean.mkIdent `dropWhile) $p)
  | _ => throw ()

/-- Given `f : α → β` and `l : List α`, print `List.map f l` as `l.map f` in Infoview. -/
@[app_unexpander List.map]
def List.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `map) $f)
  | _ => throw ()

/-- Given `f : α → β` and `s : Multiset α`, print `Multiset.map f s` as `s.map f` in Infoview. -/
@[app_unexpander Multiset.map]
def Multiset.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $s) => `($(s).$(Lean.mkIdent `map) $f)
  | _ => throw ()

attribute [pp_dot] List.length List.get List.sum Multiset.sum Multiset.summap
  Sigma.fst Sigma.snd
  ValuedCsp.Term.evalSolution ValuedCsp.Term.f ValuedCsp.Term.n ValuedCsp.Term.app
  FractionalOperation.size FractionalOperation.tt

macro "change " h:ident " to " t:term : tactic => `(tactic| change $t at $h:ident)

end better_notation


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

lemma Multiset.summap_singleton {α β : Type*} [AddCommMonoid β] (a : α) (f : α → β) :
    Multiset.summap {a} f = f a := by
  simp

lemma Multiset.summap_nsmul {α β : Type*} [AddCommMonoid β] (s : Multiset α) (f : α → β) (n : ℕ) :
    s.summap (fun a => n • f a) = n • s.summap f := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, Multiset.sum_map_add, ih]

lemma Multiset.summap_summap_swap {α β γ : Type*} [AddCommMonoid γ]
    (A : Multiset α) (B : Multiset β) (f : α → β → γ) :
    A.summap (fun a => B.summap (fun b => f a b)) =
    B.summap (fun b => A.summap (fun a => f a b)) := by
  apply Multiset.sum_map_sum_map

end push_higher


variable {D C : Type*}

lemma level1 [OrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι : Type*} (t : Γ.Term ι)
    {m : ℕ} (ω : FractionalOperation D m) (x : Fin m → (ι → D))
    (impr : t.f.AdmitsFractional ω) :
    m • (ω.tt (fun i : Fin m => x i ∘ t.app)).summap t.f ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => t.f (x i ∘ t.app)) :=
  impr (x · ∘ t.app)

lemma level2 [OrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι : Type*} (t : Γ.Term ι)
    {m : ℕ} (ω : FractionalOperation D m) (x : Fin m → (ι → D))
    (impr : t.f.AdmitsFractional ω) :
    m • (ω.tt (fun i : Fin m => x i)).summap t.evalSolution ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => t.evalSolution (x i)) := by
  convert level1 t ω x impr
  show
    (ω.tt (x ·)).summap (fun xᵢ => t.f (xᵢ ∘ t.app)) =
    (ω.tt (x · ∘ t.app)).summap t.f
  convert_to
    Multiset.sum ((ω.tt (x ·)).map (fun xᵢ => t.f (fun i => xᵢ (t.app i)))) =
    Multiset.sum ((ω.tt (x · ∘ t.app)).map t.f)
  apply congr_arg
  show
    (ω.tt (x ·)).map (fun xᵢ : ι → D => t.f (fun i : Fin t.n => xᵢ (t.app i))) =
    (ω.tt (x · ∘ t.app)).map t.f
  sorry

lemma level3 [OrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι : Type*} (I : Γ.Instance ι)
    {m : ℕ} (ω : FractionalOperation D m) (x : Fin m → (ι → D))
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    m • (ω.tt x).summap I.evalSolution ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => I.evalSolution (x i)) := by
  show
    m • (ω.tt x).summap (fun yᵢ => I.summap (fun t => t.evalSolution yᵢ)) ≤
    ω.size • Finset.univ.val.summap (fun i => I.summap (fun t => t.evalSolution (x i)))
  rw [Multiset.summap_summap_swap _ I, Multiset.summap_summap_swap _ I]
  rw [←Multiset.summap_nsmul, ←Multiset.summap_nsmul]
  apply Multiset.sum_map_le_sum_map
  intro t _
  apply level2
  exact frpo ⟨t.n, t.f⟩ t.inΓ

lemma level4 [OrderedAddCommMonoid C] {Γ : ValuedCsp D C} {ι μ : Type*} (I : Γ.Instance (ι ⊕ μ))
    {m : ℕ} (ω : FractionalOperation D m) (x : Fin m → (ι → D)) (z : μ → D)
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    m • (ω.tt x).summap (I.evalPartial · z) ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => I.evalPartial (x i) z) := by
  show
    m • (ω.tt x).summap (fun yᵢ => I.summap (fun t => t.evalSolution (Sum.elim yᵢ z))) ≤
    ω.size • Finset.univ.val.summap (fun i => I.summap (fun t => t.evalSolution (Sum.elim (x i) z)))
  rw [Multiset.summap_summap_swap _ I, Multiset.summap_summap_swap _ I]
  rw [←Multiset.summap_nsmul, ←Multiset.summap_nsmul]
  apply Multiset.sum_map_le_sum_map
  intro t _
  sorry

lemma level5 [Nonempty D] [Fintype D] [OrderedAddCommMonoidWithInfima C] {Γ : ValuedCsp D C}
    {ι μ : Type*} [DecidableEq μ] [Fintype μ] (I : Γ.Instance (ι ⊕ μ))
    {m : ℕ} (ω : FractionalOperation D m) (x : Fin m → (ι → D))
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    m • (ω.tt x).summap I.evalMinimize ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => I.evalMinimize (x i)) := by
  sorry

lemma FractionalOperation.IsFractionalPolymorphismFor.expressivePower
    [Nonempty D] [Fintype D] [OrderedAddCommMonoidWithInfima C] {Γ : ValuedCsp D C}
    {m : ℕ} {ω : FractionalOperation D m}
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expressivePower := by
  intro f hf
  rw [ValuedCsp.expressivePower, Set.mem_setOf_eq] at hf
  rcases hf with ⟨n, μ, I, rfl⟩
  intro x
  apply level5
  exact frpo

/-- Function `f` has Max-Cut property at labels `a` and `b` when `argmin f` is exactly:
   `{ ![a, b] , ![b, a] }` -/
def Function.HasMaxCutPropertyAt [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
  ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

/-- Function `f` has Max-Cut property at some two non-identical labels. -/
def Function.HasMaxCutProperty [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

def ValuedCsp.CanExpressMaxCut [Nonempty D] [Fintype D] [OrderedAddCommMonoidWithInfima C]
    {Γ : ValuedCsp D C} : Prop :=
  ∃ f : (Fin 2 → D) → C, ⟨2, f⟩ ∈ Γ.expressivePower ∧ f.HasMaxCutProperty

lemma Function.HasMaxCutProperty.forbids_commutativeFP [OrderedCancelAddCommMonoid C]
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

theorem ValuedCsp.CanExpressMaxCut.forbids_commutativeFP
    [Nonempty D] [Fintype D] [OrderedCancelAddCommMonoidWithInfima C]
    {Γ : ValuedCsp D C} (expressMC : Γ.CanExpressMaxCut)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) :
    ¬ ω.IsSymmetricFractionalPolymorphismFor Γ := by
  rintro ⟨frpol, symme⟩
  rcases expressMC with ⟨f, fin, fmc⟩
  apply fmc.forbids_commutativeFP valid symme
  exact frpol.expressivePower ⟨2, f⟩ fin
