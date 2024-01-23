import VCSP.FractionalPolymorphisms
import VCSP.Expressibility
import Mathlib.Data.Fin.VecNotation


section better_notation

/-- Given `n : ℕ` and `l : List _`, print `List.take n l` as `l.take n` in Infoview. -/
@[app_unexpander List.take]
def List.take.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `take) $n)
  | _ => throw ()

/-- Given `n : ℕ` and `l : List _`, print `List.drop n l` as `l.drop n` in Infoview. -/
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

/-- Given `f : α → _` and `l : List α`, print `List.map f l` as `l.map f` in Infoview. -/
@[app_unexpander List.map]
def List.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `map) $f)
  | _ => throw ()

/-- Given `f : α → _` and `s : Multiset α`, print `Multiset.map f s` as `s.map f` in Infoview. -/
@[app_unexpander Multiset.map]
def Multiset.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $s) => `($(s).$(Lean.mkIdent `map) $f)
  | _ => throw ()

@[simp]
abbrev Multiset.summap {α β : Type*} [AddCommMonoid β] (s : Multiset α) (f : α → β) : β :=
  (s.map f).sum

attribute [pp_dot] List.length List.get List.sum Multiset.sum Multiset.summap
  Sigma.fst Sigma.snd
  ValuedCSP.Term.f ValuedCSP.Term.n ValuedCSP.Term.app ValuedCSP.Term.evalSolution
  ValuedCSP.Instance.evalSolution ValuedCSP.Instance.evalPartial ValuedCSP.Instance.evalMinimize
  FractionalOperation.size FractionalOperation.tt

macro "change " h:ident " to " t:term : tactic => `(tactic| change $t at $h:ident)

end better_notation


section not_VCSP_specific

variable {α β γ : Type*}

lemma univ_val_map_2x2 {f : (Fin 2 → α) → β} {a b c d : α} :
    Finset.univ.val.map (fun i => f (![![a, b], ![c, d]] i)) = [f ![a, b], f ![c, d]] :=
  rfl

lemma Multiset.sum_ofList_twice [AddCommMonoid α] (x : α) :
    Multiset.sum ↑[x, x] = 2 • x := by
  simp [two_nsmul]

lemma column_of_2x2_left (a b c d : α) :
    (fun i => ![![a, b], ![c, d]] i 0) = (fun i => ![a, c] i) := by
  ext i
  match i with
  | 0 => rfl
  | 1 => rfl

lemma column_of_2x2_right (a b c d : α) :
    (fun i => ![![a, b], ![c, d]] i 1) = (fun i => ![b, d] i) := by
  ext i
  match i with
  | 0 => rfl
  | 1 => rfl

lemma Multiset.summap_singleton [AddCommMonoid β] (a : α) (f : α → β) :
    Multiset.summap {a} f = f a := by
  simp

lemma Multiset.summap_nsmul [AddCommMonoid β] (s : Multiset α) (f : α → β) (n : ℕ) :
    s.summap (fun a => n • f a) = n • s.summap f := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, Multiset.sum_map_add, ih]

lemma Multiset.summap_summap_swap [AddCommMonoid γ]
    (A : Multiset α) (B : Multiset β) (f : α → β → γ) :
    A.summap (fun a => B.summap (fun b => f a b)) =
    B.summap (fun b => A.summap (fun a => f a b)) :=
  Multiset.sum_map_sum_map A B

lemma Multiset.summap_le_summap [OrderedAddCommMonoid β] {s : Multiset α}
    {f g : α → β} (hfg : ∀ i ∈ s, f i ≤ g i) :
    s.summap f ≤ s.summap g :=
  Multiset.sum_map_le_sum_map f g hfg

lemma Finset.nsmul_inf' [LinearOrderedAddCommMonoid β] {s : Finset α}
    (hs : s.Nonempty) (f : α → β) (n : ℕ) :
    s.inf' hs (fun a => n • f a) = n • s.inf' hs f := by
  if nz : n = 0 then
    rw [nz]
    simp_rw [zero_smul]
    apply Finset.inf'_const
  else
    obtain ⟨d, hd, hfd⟩ := Finset.exists_mem_eq_inf' hs f
    obtain ⟨dₙ, hnₙ, hfdₙ⟩ := Finset.exists_mem_eq_inf' hs (fun a => n • f a)
    have key : n • f dₙ = n • f d
    · apply eq_of_ge_of_not_gt
      · rw [← hfd]
        exact nsmul_le_nsmul_right (Finset.inf'_le f hnₙ) n
      · rw [not_lt, ← hfdₙ]
        exact Finset.inf'_le (fun a => n • f a) hd
    rw [hfd, hfdₙ, key]

end not_VCSP_specific


variable {D C : Type*}

section expressiveness

section partial_order

variable [OrderedAddCommMonoid C] {Γ : ValuedCSP D C} {ι : Type*} {m : ℕ} {ω : FractionalOperation D m}

lemma Function.AdmitsFractional.evalTerm_le_evalTerm {t : Γ.Term ι}
    (impr : t.f.AdmitsFractional ω) (x : Fin m → (ι → D)) :
    m • (ω.tt (fun i : Fin m => x i ∘ t.app)).summap t.f ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => t.f (x i ∘ t.app)) := by
  apply impr

lemma Function.AdmitsFractional.evalSolution_le_evalSolution {t : Γ.Term ι}
    (impr : t.f.AdmitsFractional ω) (x : Fin m → (ι → D)) :
    m • (ω.tt (fun i : Fin m => x i)).summap t.evalSolution ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => t.evalSolution (x i)) := by
  convert impr.evalTerm_le_evalTerm x
  convert_to
    Multiset.sum ((ω.tt (x ·)).map (fun xᵢ => t.f (fun i => xᵢ (t.app i)))) =
    Multiset.sum ((ω.tt (x · ∘ t.app)).map t.f)
  apply congr_arg
  unfold FractionalOperation.tt
  rewrite [Multiset.map_map, Multiset.map_map]
  rfl

lemma FractionalOperation.IsFractionalPolymorphismFor.evalSolution_le_evalSolution
    (frpo : ω.IsFractionalPolymorphismFor Γ) (I : Γ.Instance ι) (x : Fin m → (ι → D)) :
    m • (ω.tt x).summap I.evalSolution ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => I.evalSolution (x i)) := by
  show
    m • (ω.tt x).summap (fun yᵢ => I.summap (fun t => t.evalSolution yᵢ)) ≤
    ω.size • Finset.univ.val.summap (fun i => I.summap (fun t => t.evalSolution (x i)))
  iterate 2
    rw [Multiset.summap_summap_swap _ I, ←Multiset.summap_nsmul]
  apply Multiset.summap_le_summap
  intro t _
  apply (frpo ⟨t.n, t.f⟩ t.inΓ).evalSolution_le_evalSolution

lemma FractionalOperation.IsFractionalPolymorphismFor.evalPartial_le_evalPartial
    (frpo : ω.IsFractionalPolymorphismFor Γ) {μ : Type*} (I : Γ.Instance (ι ⊕ μ))
    (x : Fin m → (ι → D)) (z : Fin m → (μ → D)) :
    m • (ω.tt (fun i : Fin m => Sum.elim (x i) (z i))).summap (fun y : (ι ⊕ μ) → D =>
      I.evalPartial (y ∘ Sum.inl) (y ∘ Sum.inr)) ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => I.evalPartial (x i) (z i)) := by
  convert frpo.evalSolution_le_evalSolution I (fun i : Fin m => Sum.elim (x i) (z i)) with s
  show I.evalSolution (Sum.elim (s ∘ Sum.inl) (s ∘ Sum.inr)) = I.evalSolution s
  rw [Sum.elim_comp_inl_inr]

lemma FractionalOperation.IsFractionalPolymorphismFor.evalPartial_le_evalPartial_with_nsmul_inside
    (frpo : ω.IsFractionalPolymorphismFor Γ) {μ : Type*} (I : Γ.Instance (ι ⊕ μ))
    (x : Fin m → (ι → D)) (z : Fin m → (μ → D)) :
    (ω.tt (fun i : Fin m => Sum.elim (x i) (z i))).summap (fun y : (ι ⊕ μ) → D =>
      m • I.evalPartial (y ∘ Sum.inl) (y ∘ Sum.inr)) ≤
    Finset.univ.val.summap (fun i : Fin m => ω.size • I.evalPartial (x i) (z i)) := by
  rw [Multiset.summap_nsmul, Multiset.summap_nsmul]
  exact frpo.evalPartial_le_evalPartial I x z

end partial_order

section total_order

variable [Nonempty D] [Fintype D] [LinearOrderedAddCommMonoid C]
         {Γ : ValuedCSP D C} {m : ℕ} {ω : FractionalOperation D m}

lemma FractionalOperation.IsFractionalPolymorphismFor.evalMinimize_le_evalMinimize_with_nsmul_inside
    (frpo : ω.IsFractionalPolymorphismFor Γ) {ι μ : Type*} [DecidableEq μ] [Fintype μ]
    (I : Γ.Instance (ι ⊕ μ)) (x : Fin m → (ι → D)) :
    (ω.tt x).summap (fun yᵢ => m • I.evalMinimize yᵢ) ≤
    Finset.univ.val.summap (fun i : Fin m => ω.size • I.evalMinimize (x i)) := by
  show
    (ω.tt x).summap (fun yᵢ => m • Finset.univ.inf' Finset.univ_nonempty (I.evalPartial yᵢ)) ≤
    Finset.univ.val.summap (fun i : Fin m =>
      ω.size • Finset.univ.inf' Finset.univ_nonempty (I.evalPartial (x i)))
  convert_to
    (ω.tt x).summap (fun yᵢ : ι → D =>
      Finset.univ.inf' Finset.univ_nonempty (m • I.evalPartial yᵢ)) ≤
    Finset.univ.val.summap (fun i : Fin m =>
      Finset.univ.inf' Finset.univ_nonempty (ω.size • I.evalPartial (x i)))
  · simp [Finset.nsmul_inf']
  · simp [Finset.nsmul_inf']
  let z := fun i : Fin m =>
    (Finset.exists_mem_eq_inf' Finset.univ_nonempty (ω.size • I.evalPartial (x i))).choose
  convert_to
    (ω.tt x).summap (fun yᵢ : ι → D =>
      Finset.univ.inf' Finset.univ_nonempty (m • I.evalPartial yᵢ)) ≤
    Finset.univ.val.summap (fun i : Fin m =>
      (ω.size • I.evalPartial (x i) (z i)))
  · congr
    ext i
    exact (Finset.exists_mem_eq_inf' Finset.univ_nonempty (ω.size • I.evalPartial (x i))).choose_spec.right
  have ineq_for_z :
    (ω.tt (fun i : Fin m => Sum.elim (x i) (z i))).summap (fun yᵢ : (ι ⊕ μ) → D =>
      m • I.evalPartial (yᵢ ∘ Sum.inl) (yᵢ ∘ Sum.inr)) ≤
    Finset.univ.val.summap (fun i : Fin m =>
      ω.size • I.evalPartial (x i) (z i))
  · exact frpo.evalPartial_le_evalPartial_with_nsmul_inside I x z
  refine LE.le.trans ?_ ineq_for_z
  show
    (ω.tt x).summap (fun y₁ : ι → D =>
      Finset.univ.inf' Finset.univ_nonempty (m • I.evalPartial y₁)) ≤
    (ω.tt (fun i : Fin m => Sum.elim (x i) (z i))).summap (fun y₂ : (ι ⊕ μ) → D =>
      m • I.evalPartial (y₂ ∘ Sum.inl) (y₂ ∘ Sum.inr))
  simp [FractionalOperation.tt, Multiset.map_map]
  apply Multiset.summap_le_summap
  intro g _
  simp only [Finset.inf'_le_iff, Finset.mem_univ, true_and]
  show
    ∃ zᵢ : μ → D,
      m • I.evalPartial (fun j : ι => g (Function.swap x j)) zᵢ ≤
      m • I.evalPartial (fun j : ι => g (Function.swap x j)) (fun i : μ => g _)
  exact ⟨_, le_of_eq rfl⟩

lemma FractionalOperation.IsFractionalPolymorphismFor.evalMinimize_le_evalMinimize
    (frpo : ω.IsFractionalPolymorphismFor Γ) {ι μ : Type*} [DecidableEq μ] [Fintype μ]
    (I : Γ.Instance (ι ⊕ μ)) (x : Fin m → (ι → D)) :
    m • (ω.tt x).summap I.evalMinimize ≤
    ω.size • Finset.univ.val.summap (fun i : Fin m => I.evalMinimize (x i)) := by
  rw [←Multiset.summap_nsmul, ←Multiset.summap_nsmul]
  exact frpo.evalMinimize_le_evalMinimize_with_nsmul_inside I x

lemma FractionalOperation.IsFractionalPolymorphismFor.expressivePowerVCSP
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expressivePower := by
  intro f hf
  rw [ValuedCSP.expressivePower, Set.mem_setOf_eq] at hf
  rcases hf with ⟨n, μ, I, -, -, rfl⟩
  intro x
  apply frpo.evalMinimize_le_evalMinimize

end total_order

end expressiveness


section max_cut

/-- Function `f` has Max-Cut property at labels `a` and `b` when `argmin f` is exactly:
   `{ ![a, b] , ![b, a] }` -/
def Function.HasMaxCutPropertyAt [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
  ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

/-- Function `f` has Max-Cut property at some two non-identical labels. -/
def Function.HasMaxCutProperty [OrderedAddCommMonoid C] (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

/-- VCSP template `Γ` can express Max Cut via summation and minimization. -/
def ValuedCSP.CanExpressMaxCut [Nonempty D] [Fintype D] [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCSP D C} : Prop :=
  ∃ f : (Fin 2 → D) → C, ⟨2, f⟩ ∈ Γ.expressivePower ∧ f.HasMaxCutProperty

lemma Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism [OrderedCancelAddCommMonoid C]
    {f : (Fin 2 → D) → C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  intro contr
  rcases mcf with ⟨a, b, hab, mcfab⟩
  specialize contr ![![a, b], ![b, a]]
  rw [univ_val_map_2x2, ←mcfab.left, Multiset.sum_ofList_twice] at contr
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
      rw [←eq_r]
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

theorem ValuedCSP.CanExpressMaxCut.forbids_commutativeFractionalPolymorphism
    [Nonempty D] [Fintype D] [LinearOrderedCancelAddCommMonoid C]
    {Γ : ValuedCSP D C} (expressMC : Γ.CanExpressMaxCut)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) :
    ¬ ω.IsSymmetricFractionalPolymorphismFor Γ := by
  rintro ⟨frpol, symme⟩
  rcases expressMC with ⟨f, fin, fmc⟩
  apply fmc.forbids_commutativeFractionalPolymorphism valid symme
  exact frpol.expressivePowerVCSP ⟨2, f⟩ fin

end max_cut

example [Nonempty D] [Fintype D] (ζ : Type) [Nonempty ζ] [Fintype ζ]
    (A : Multiset (Σ α : Type, Σ _ : Fintype α, D × α × ζ → ℚ)) :
  ∃ β : Type, ∃ _ : Fintype β, ∃ B : Multiset (D × β → ℚ), ∀ d : D,
    Finset.univ.inf' Finset.univ_nonempty (fun z : ζ =>
      A.summap (fun ⟨α, _, f⟩ => Finset.univ.inf' sorry (fun a : α => f (d, a, z)))) =
    Finset.univ.inf' sorry (fun b : β => B.summap (· (d, b))) := by
  classical
  use (A.map Sigma.fst).toList.TProd id × ζ, sorry
  use A.map (fun t => by
    intro ⟨d, a, z⟩
    have alpha : t.fst ∈ (A.map Sigma.fst).toList
    · have tin : t ∈ A
      · sorry
      aesop
    exact t.snd.snd ⟨d, a.elim alpha, z⟩)
  intro d
  apply le_antisymm
  · rw [Finset.inf'_le_iff]
    sorry
  · rw [Finset.inf'_le_iff]
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun z : ζ =>
        A.summap (fun ⟨α, _, f⟩ => Finset.univ.inf' sorry (fun a : α => f (d, a, z))))
    rw [hi]
    sorry
