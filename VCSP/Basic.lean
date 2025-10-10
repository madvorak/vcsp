import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Tactic.Have


section multiset_summap
variable {α β γ : Type*}

/-- Summation à la `Finset.sum` (but without notation). -/
abbrev Multiset.summap [AddCommMonoid β] (s : Multiset α) (f : α → β) : β :=
  (s.map f).sum

lemma Multiset.nsmul_summap [AddCommMonoid β] (s : Multiset α) (f : α → β) (n : ℕ) :
    n • s.summap f = s.summap (fun a => n • f a) :=
  Multiset.sum_map_nsmul.symm

lemma Multiset.summap_summap_swap [AddCommMonoid γ]
    (A : Multiset α) (B : Multiset β) (f : α → β → γ) :
    A.summap (fun a : α => B.summap (fun b : β => f a b)) =
    B.summap (fun b : β => A.summap (fun a : α => f a b)) :=
  Multiset.sum_map_sum_map A B

lemma Multiset.summap_le_summap [OrderedAddCommMonoid β] {s : Multiset α}
    {f g : α → β} (hfg : ∀ i ∈ s, f i ≤ g i) :
    s.summap f ≤ s.summap g :=
  Multiset.sum_map_le_sum_map f g hfg

lemma Multiset.summap_lt_summap [OrderedCancelAddCommMonoid β] {s : Multiset α}
    (hs : s ≠ ∅) {f g : α → β} (hfg : ∀ i ∈ s, f i < g i) :
    s.summap f < s.summap g :=
  Multiset.sum_lt_sum_of_nonempty hs hfg

end multiset_summap


section uncategorized_stuff

lemma nneg_comp {α β ι : Type*} [Zero β] [LE β] {x : α → β} (hx : 0 ≤ x) (f : ι → α) : 0 ≤ x ∘ f :=
  fun i : ι => hx (f i)

lemma FractionalOperation.IsValid.tt_nonempty {D ι : Type*} {m : ℕ} {ω : FractionalOperation D m}
    (valid : ω.IsValid) {x : Fin m → ι → D} :
    ω.tt x ≠ ∅ := by
  simpa [FractionalOperation.tt] using valid

/-- Nonterminal `aesop` (strongly discouraged to use). -/
macro "aesopnt" : tactic => `(tactic| aesop (config := {warnOnNonterminal := false}))

end uncategorized_stuff
