import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Tactic.Have


section multisets_and_finsets
variable {α β γ : Type*}

/-- Summation à la `Finset.sum` (but without notation). -/
abbrev Multiset.summap {α β : Type*} [AddCommMonoid β] (s : Multiset α) (f : α → β) : β :=
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


section sum_elims
-- TODO remove this section after https://github.com/leanprover-community/mathlib4/pull/13167 gets merged
variable {α₁ α₂ β : Type*} [LE β]

lemma elim_le_elim_iff (u₁ v₁ : α₁ → β) (u₂ v₂ : α₂ → β) :
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

lemma const_le_elim_iff (b : β) (v₁ : α₁ → β) (v₂ : α₂ → β) :
    (Function.const _ b) ≤ Sum.elim v₁ v₂ ↔ (Function.const _ b) ≤ v₁ ∧ (Function.const _ b) ≤ v₂ := by
  rw [←Sum.elim_const_const, elim_le_elim_iff]

lemma zero_le_elim_iff [Zero β] (v₁ : α₁ → β) (v₂ : α₂ → β) :
    0 ≤ Sum.elim v₁ v₂ ↔ 0 ≤ v₁ ∧ 0 ≤ v₂ :=
  const_le_elim_iff 0 v₁ v₂

lemma one_le_elim_iff [One β] (v₁ : α₁ → β) (v₂ : α₂ → β) :
    1 ≤ Sum.elim v₁ v₂ ↔ 1 ≤ v₁ ∧ 1 ≤ v₂ :=
  const_le_elim_iff 1 v₁ v₂

lemma elim_le_const_iff (b : β) (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ (Function.const _ b) ↔ u₁ ≤ (Function.const _ b) ∧ u₂ ≤ (Function.const _ b) := by
  rw [←Sum.elim_const_const, elim_le_elim_iff]

lemma elim_le_zero_iff [Zero β] (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ 0 ↔ u₁ ≤ 0 ∧ u₂ ≤ 0 :=
  elim_le_const_iff 0 u₁ u₂

lemma elim_le_one_iff [One β] (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ 1 ↔ u₁ ≤ 1 ∧ u₂ ≤ 1 :=
  elim_le_const_iff 1 u₁ u₂

end sum_elims


section uncategorized_stuff

lemma or_of_neq {P Q : Prop} (hPQ : P ≠ Q) : P ∨ Q := by
  tauto

lemma not_neq_of_iff {P Q : Prop} (hpq : P ↔ Q) : (¬P) ≠ Q := by
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
