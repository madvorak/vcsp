import VCSP.Expressibility
import VCSP.FractionalOperations
import Mathlib.Tactic.Have


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

/-- Summation à la `Finset.sum` (but without notation). -/
abbrev Multiset.summap {α β : Type*} [AddCommMonoid β] (s : Multiset α) (f : α → β) : β :=
  (s.map f).sum

attribute [pp_dot] List.length List.get List.sum Multiset.sum Multiset.summap Finset.sum
  Sigma.fst Sigma.snd
  ValuedCSP.Term.f ValuedCSP.Term.n ValuedCSP.Term.app
  ValuedCSP.Term.evalSolution ValuedCSP.Instance.evalSolution
  FractionalOperation.size FractionalOperation.tt

macro "change " h:ident " to " t:term : tactic => `(tactic| change $t at $h:ident)

end better_notation


section not_VCSP_specific

variable {α β γ : Type*}

lemma Multiset.nsmul_summap [AddCommMonoid β] (s : Multiset α) (f : α → β) (n : ℕ) :
    n • s.summap f = s.summap (fun a => n • f a) :=
  Multiset.sum_map_nsmul.symm

lemma Multiset.summap_summap_swap [AddCommMonoid γ]
    (A : Multiset α) (B : Multiset β) (f : α → β → γ) :
    A.summap (fun a => B.summap (fun b => f a b)) =
    B.summap (fun b => A.summap (fun a => f a b)) :=
  Multiset.sum_map_sum_map A B

lemma Multiset.summap_le_summap [OrderedAddCommMonoid β] {s : Multiset α}
    {f g : α → β} (hfg : ∀ i ∈ s, f i ≤ g i) :
    s.summap f ≤ s.summap g :=
  Multiset.sum_map_le_sum_map f g hfg

lemma Multiset.summap_lt_summap [OrderedCancelAddCommMonoid β] {s : Multiset α}
    (hs : s ≠ ∅) {f g : α → β} (hfg : ∀ i ∈ s, f i < g i) :
    s.summap f < s.summap g :=
  Multiset.sum_lt_sum_of_nonempty hs hfg

end not_VCSP_specific


variable {D C : Type*} [Nonempty D] [Fintype D]

lemma FractionalOperation.IsFractionalPolymorphismFor.expressesVCSP [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCSP D C} {m : ℕ} {ω : FractionalOperation D m}
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expresses := by
  intro F hF
  induction hF with
  | single hf =>
    apply frpo
    exact hf
  | double _ _ ihf ihg =>
    intro x
    have summed := add_le_add (ihf x) (ihg x)
    rw [
      Finset.smul_sum, Finset.smul_sum, ←Finset.sum_add_distrib,
      Multiset.nsmul_summap, Multiset.nsmul_summap, ←Multiset.sum_map_add
    ] at summed
    rw [Finset.smul_sum, Multiset.nsmul_summap]
    convert summed using 2 <;> simp
  | @minimize n f _ ih =>
    intro x
    rw [Multiset.nsmul_summap, Finset.smul_sum]
    simp_rw [←Finset.nsmul_inf']
    let z :=
      fun i : Fin m =>
        (Finset.exists_mem_eq_inf' Finset.univ_nonempty
          (fun d : D => ω.size • f (Matrix.vecCons d (x i)))
        ).choose
    specialize ih (fun i j => Matrix.vecCons (z i) (x i) j)
    rw [Multiset.nsmul_summap, Finset.smul_sum] at ih
    convert_to
      (ω.tt x).summap (fun yᵢ : Fin n → D =>
        Finset.univ.inf' Finset.univ_nonempty (fun zᵢ : D => m • f (Matrix.vecCons zᵢ yᵢ))) ≤
      Finset.univ.val.summap (fun i : Fin m =>
        ω.size • f (fun j : Fin n.succ => Matrix.vecCons (z i) (x i) j))
    · congr
      ext i
      exact (Finset.exists_mem_eq_inf' Finset.univ_nonempty _).choose_spec.right
    refine LE.le.trans ?_ ih
    simp_rw [Multiset.summap, FractionalOperation.tt, Multiset.map_map, Function.comp_apply]
    apply Multiset.summap_le_summap
    intro g _
    rw [Finset.nsmul_inf']
    apply nsmul_le_nsmul_right
    simp only [Finset.inf'_le_iff, Finset.mem_univ, true_and]
    use g z
    apply le_of_eq
    apply congr_arg
    ext i
    match i with
    | 0 => rfl
    | ⟨i'+1, _⟩ => rfl
  | remap _ τ ih =>
    intro x
    specialize ih (fun i j => x i (τ j))
    convert ih using 3
    unfold FractionalOperation.tt
    rewrite [Multiset.map_map, Multiset.map_map]
    rfl

/-- VCSP template `Γ` can express Max Cut via summation and minimization. -/
def ValuedCSP.CanExpressMaxCut [LinearOrderedAddCommMonoid C] (Γ : ValuedCSP D C) : Prop :=
  ∃ f : (Fin 2 → D) → C, ⟨2, f⟩ ∈ Γ.expresses ∧ f.HasMaxCutProperty

theorem ValuedCSP.CanExpressMaxCut.forbids_commutativeFractionalPolymorphism
    [LinearOrderedCancelAddCommMonoid C]
    {Γ : ValuedCSP D C} (expressMC : Γ.CanExpressMaxCut)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) :
    ¬ ω.IsSymmetricFractionalPolymorphismFor Γ := by
  rintro ⟨frpol, symme⟩
  obtain ⟨f, fin, fmc⟩ := expressMC
  apply fmc.forbids_commutativeFractionalPolymorphism valid symme
  exact frpol.expressesVCSP ⟨2, f⟩ fin

#print axioms ValuedCSP.CanExpressMaxCut.forbids_commutativeFractionalPolymorphism
