import Mathlib.Combinatorics.Optimization.ValuedCSP
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

end better_notation


section multisets_and_finsets
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

lemma Finset.subtype_univ_sum_eq_subtype_univ_sum {p q : α → Prop} (hpq : p = q)
    [Fintype { a : α // p a }] [Fintype { a : α // q a }] [AddCommMonoid β]
    {f : { a : α // p a } → β} {g : { a : α // q a } → β}
    (hfg : ∀ a : α, ∀ hpa : p a, ∀ hqa : q a, f ⟨a, hpa⟩ = g ⟨a, hqa⟩) :
    Finset.univ.sum f = Finset.univ.sum g := by
  subst hpq
  convert rfl
  ext
  simp_all only

-- Andrew Yang proved this lemma
lemma Finset.univ_sum_of_zero_when_neg [Fintype α] [AddCommMonoid β]
    {f : α → β} (p : α → Prop) [DecidablePred p] (hpf : ∀ a : α, ¬(p a) → f a = 0) :
    Finset.univ.sum f = Finset.univ.sum (fun a : { a : α // p a } => f a.val) := by
  classical
  trans (Finset.univ.filter p).sum f
  · symm
    apply Finset.sum_subset_zero_on_sdiff
    · apply Finset.subset_univ
    · simpa
    · intros
      rfl
  · apply Finset.sum_subtype
    simp

end multisets_and_finsets


section uncategorized_stuff

lemma FractionalOperation.IsValid.tt_nonempty {D ι : Type*} {m : ℕ} {ω : FractionalOperation D m}
    (valid : ω.IsValid) {x : Fin m → ι → D} :
    ω.tt x ≠ ∅ := by
  simpa [FractionalOperation.tt] using valid

lemma not_neq_of_iff {P Q : Prop} (hpq : P ↔ Q) : (¬P) ≠ Q := by
  tauto

lemma sumElim_le_sumElim_iff {α₁ α₂ β : Type*} [LE β] (u₁ v₁ : α₁ → β) (u₂ v₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ Sum.elim v₁ v₂ ↔ u₁ ≤ v₁ ∧ u₂ ≤ v₂ := by
  constructor <;> intro hyp
  · constructor
    · intro i₁
      have hi₁ := hyp (Sum.inl i₁)
      rwa [Sum.elim_inl, Sum.elim_inl] at hi₁
    · intro i₂
      have hi₂ := hyp (Sum.inr i₂)
      rwa [Sum.elim_inr, Sum.elim_inr] at hi₂
  · intro j
    cases j with
    | inl j₁ =>
      rw [Sum.elim_inl, Sum.elim_inl]
      exact hyp.left j₁
    | inr j₂ =>
      rw [Sum.elim_inr, Sum.elim_inr]
      exact hyp.right j₂

lemma le_of_nng_add {α : Type*} [OrderedAddCommGroup α] {a b c : α} (habc : a + b = c) (ha : 0 ≤ a) : b ≤ c := by
  aesop

macro "change " h:ident " to " t:term : tactic => `(tactic| change $t at $h:ident)

/-- Nonterminal `aesop` (strongly discouraged to use) -/
macro (name := aesopnt) "aesopnt" : tactic =>
  `(tactic| aesop (config := {warnOnNonterminal := false}))

open Matrix
variable {I J R : Type*} [Fintype I] [Fintype J]

lemma Matrix.neg_mulVec_neg [Ring R] (v : J → R) (A : Matrix I J R) : (-A) *ᵥ (-v) = A *ᵥ v := by
  rw [Matrix.mulVec_neg, Matrix.neg_mulVec, neg_neg]

lemma Matrix.zero_le_one_elem [OrderedSemiring R] [DecidableEq I] (i i' : I) :
    (0 : R) ≤ (1 : Matrix I I R) i i' := by
  by_cases hi : i = i' <;> simp [hi]

end uncategorized_stuff
