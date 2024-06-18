import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Tactic.Have


section multisets_and_finsets
variable {α β γ : Type*}

/-- Summation à la `Finset.sum` (but without notation). -/
abbrev Multiset.summap [AddCommMonoid β] (s : Multiset α) (f : α → β) : β :=
  (s.map f).sum

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

-- Andrew Yang proved this lemma:
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

lemma or_of_neq {P Q : Prop} (hPQ : P ≠ Q) : P ∨ Q := by
  tauto

lemma not_neq_of_iff {P Q : Prop} (hpq : P ↔ Q) : (¬P) ≠ Q := by
  tauto

lemma neq_of_iff_neg {P Q : Prop} (hpq : P ↔ ¬Q) : P ≠ Q := by
  tauto

lemma le_of_nneg_add {α : Type*} [OrderedAddCommGroup α] {a b c : α} (habc : a + b = c) (ha : 0 ≤ a) : b ≤ c := by
  aesop

lemma nneg_comp {α β ι : Type*} [Zero β] [LE β] {x : α → β} (hx : 0 ≤ x) (f : ι → α) : 0 ≤ x ∘ f :=
  fun (i : ι) => hx (f i)

lemma FractionalOperation.IsValid.tt_nonempty {D ι : Type*} {m : ℕ} {ω : FractionalOperation D m}
    (valid : ω.IsValid) {x : Fin m → ι → D} :
    ω.tt x ≠ ∅ := by
  simpa [FractionalOperation.tt] using valid

macro "change " h:ident " to " t:term : tactic => `(tactic| change $t at $h:ident)

/-- Nonterminal `aesop` (strongly discouraged to use) -/
macro (name := aesopnt) "aesopnt" : tactic =>
  `(tactic| aesop (config := {warnOnNonterminal := false}))

end uncategorized_stuff
