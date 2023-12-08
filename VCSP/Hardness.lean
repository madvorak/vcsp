import VCSP.FractionalPolymorphisms
import VCSP.Expressibility
import Mathlib.Algebra.Order.SMul
import Mathlib.Data.Fin.VecNotation


abbrev Multiset.summap {α β : Type*} [AddCommMonoid β] (s : Multiset α) (f : α → β) : β :=
  (s.map f).sum


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

attribute [pp_dot] List.length List.get List.sum Multiset.sum Multiset.summap
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

example [CompleteSemilatticeInf C] (a b c d : C) (hac : a ≤ c) (hbd : b ≤ d) :
    sInf ({a, b} : Set C) ≤ sInf ({c, d} : Set C) := by
  have hsa : sInf ({a, b} : Set C) ≤ a
  · exact sInf_le (Set.mem_insert a {b})
  have hsb : sInf ({a, b} : Set C) ≤ b
  · rw [Set.pair_comm]
    exact sInf_le (Set.mem_insert b {a})
  have hsc : sInf ({a, b} : Set C) ≤ c
  · exact hsa.trans hac
  have hsd : sInf ({a, b} : Set C) ≤ d
  · exact hsb.trans hbd
  aesop

example [OrderedAddCommMonoidWithInfima C] (a a' b b' c c' d d' : C)
    (hac : a ≤ c) (hbd : b ≤ d) (hac' : a' ≤ c') (hbd' : b' ≤ d') :
    sInf {a, b} + sInf {a', b'} ≤ sInf {c, d} + sInf {c', d'} := by
  have hsc : sInf ({a, b} : Set C) ≤ c
  · exact (sInf_le (Set.mem_insert a {b})).trans hac
  have hsd : sInf ({a, b} : Set C) ≤ d
  · rw [Set.pair_comm]
    exact (sInf_le (Set.mem_insert b {a})).trans hbd
  have hsc' : sInf ({a', b'} : Set C) ≤ c'
  · exact (sInf_le (Set.mem_insert a' {b'})).trans hac'
  have hsd' : sInf ({a', b'} : Set C) ≤ d'
  · rw [Set.pair_comm]
    exact (sInf_le (Set.mem_insert b' {a'})).trans hbd'
  apply add_le_add <;> simp_all

example [OrderedAddCommMonoidWithInfima C] (a b c d : Fin 9 → C) (hac : a ≤ c) (hbd : b ≤ d) :
    (Finset.univ.val.map (fun i : Fin 9 => sInf {a i, b i})).sum ≤
    (Finset.univ.val.map (fun i : Fin 9 => sInf {c i, d i})).sum := by
  apply Multiset.sum_map_le_sum_map
  intro i _
  have hsci : sInf {a i, b i} ≤ c i
  · exact (sInf_le (Set.mem_insert (a i) {b i})).trans (hac i)
  have hsdi : sInf {a i, b i} ≤ d i
  · rw [Set.pair_comm]
    exact (sInf_le (Set.mem_insert (b i) {a i})).trans (hbd i)
  simp [hsci, hsdi]

example [CompleteLattice C] (f g : D → C) (hfg : ∀ x : D, f x ≤ g x) :
    sInf { f x | x : D } ≤ sInf { g x | x : D } := by
  simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
  intro a
  have hfa : f a ∈ { f x | x : D }
  · use a
  exact sInf_le_of_le hfa (hfg a)

example [OrderedAddCommMonoidWithInfima C] (n : ℕ) (a b : Fin n → D → C) (hab : a ≤ b) :
    (Finset.univ.val.map (fun i : Fin n => sInf { a i j | j : D })).sum ≤
    (Finset.univ.val.map (fun i : Fin n => sInf { b i j | j : D })).sum := by
  apply Multiset.sum_map_le_sum_map
  intro i _
  simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
  intro x
  have haix : a i x ∈ { a i j | j : D }
  · use x
  exact sInf_le_of_le haix (hab i x)

example [OrderedAddCommMonoidWithInfima C] (n : ℕ) (a b c d : Fin n → D → C)
    (hac : a ≤ c) (hbd : b ≤ d) :
    (Finset.univ.val.map (fun i : Fin n => sInf { a i j + b i j | j : D })).sum ≤
    (Finset.univ.val.map (fun i : Fin n => sInf { c i j + d i j | j : D })).sum := by
  apply Multiset.sum_map_le_sum_map
  intro i _
  simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
  intro x
  have habix : a i x + b i x ∈ { a i j + b i j | j : D }
  · use x
  apply sInf_le_of_le habix
  apply add_le_add
  · apply hac
  · apply hbd

example [OrderedAddCommMonoidWithInfima C] (n : ℕ) (x : Fin n → D → Multiset D)
    (f g : D → C) (hfg : f ≤ g) :
    (Finset.univ.val.map (fun i : Fin n => sInf { ((x i j).map f).sum | j : D })).sum ≤
    (Finset.univ.val.map (fun i : Fin n => sInf { ((x i j).map g).sum | j : D })).sum := by
  apply Multiset.sum_map_le_sum_map
  intro i _
  simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
  intro d
  have hxidf : ((x i d).map f).sum ∈ { ((x i j).map f).sum | j : D }
  · use d
  apply sInf_le_of_le hxidf
  apply Multiset.sum_map_le_sum_map
  intro e _
  exact hfg e

lemma sInf_summap_le_sInf_summap [OrderedAddCommMonoidWithInfima C] {μ : Type} {f g : D → μ → C}
    (hfg : ∀ d, ∀ z, f d z ≤ g d z) (S : Multiset D) :
    sInf { S.summap (f · z) | z : μ } ≤
    sInf { S.summap (g · z) | z : μ } := by
  apply sInf_le_sInf_of_forall_exists_le
  intro x xin
  rw [Set.mem_setOf_eq] at xin
  obtain ⟨z, hxz⟩ := xin
  use S.summap (f · z)
  convert_to S.summap (f · z) ≤ x
  · simp
  rw [←hxz]
  apply Multiset.sum_map_le_sum_map
  intros
  apply hfg

-- If we have homomorphism `h` in place of fractional polymorphism `ω` ...
example [OrderedAddCommMonoidWithInfima C] {Γ : ValuedCsp D C} {ι μ : Type} {I : Γ.Instance (ι ⊕ μ)}
    {h : D → D} (hhh : ∀ f ∈ Γ, ∀ x : Fin f.fst → D, f.snd (fun i => h (x i)) ≤ f.snd x) :
  ∀ x : ι → D,
    sInf { I.summap (fun t : Γ.Term (ι ⊕ μ) => t.f (Sum.elim (fun i => h (x i)) z ∘ t.app)) | z : μ → D } ≤
    sInf { I.summap (fun t : Γ.Term (ι ⊕ μ) => t.f (Sum.elim x z ∘ t.app)) | z : μ → D } := by
  intro x
  apply sInf_le_sInf_of_forall_exists_le
  intro c cin
  rw [Set.mem_setOf_eq] at cin
  obtain ⟨z, hcz⟩ := cin
  simp only [Set.mem_setOf_eq, exists_exists_eq_and]
  use (h ∘ z)
  rw [←hcz]
  apply Multiset.sum_map_le_sum_map
  intro t _
  convert hhh ⟨t.n, t.f⟩ t.inΓ (Sum.elim x z ∘ t.app) with j
  show (Sum.elim (h ∘ x) (h ∘ z)) (t.app j) = (h ∘ Sum.elim x z) (t.app j)
  apply congr_fun
  exact (Sum.comp_elim h x z).symm

lemma FractionalOperation.IsFractionalPolymorphismFor.expressivePower
    [OrderedAddCommMonoidWithInfima C] {Γ : ValuedCsp D C}
    {m : ℕ} {ω : FractionalOperation D m}
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expressivePower := by
  intro f hf
  rw [ValuedCsp.expressivePower, Set.mem_setOf_eq] at hf
  rcases hf with ⟨n, μ, I, rfl⟩
  unfold FractionalOperation.IsFractionalPolymorphismFor at frpo
  unfold Function.AdmitsFractional at frpo
  intro x
  rw [Multiset.smul_sum, Multiset.map_map, Multiset.smul_sum, Multiset.map_map]
  show
    (ω.tt x).summap (fun y : Fin n → D =>
        m • sInf { I.summap (fun t : Γ.Term (Fin n ⊕ μ) => t.f (Sum.elim y z ∘ t.app)) | z : μ → D }) ≤
    Finset.univ.val.summap (fun i : Fin m =>
        ω.size • sInf { I.summap (fun t : Γ.Term (Fin n ⊕ μ) => t.f (Sum.elim (x i) z ∘ t.app)) | z : μ → D })
  convert_to
    (ω.tt x).summap (fun y : Fin n → D =>
        sInf { I.summap (fun t : Γ.Term (Fin n ⊕ μ) => m • t.f (Sum.elim y z ∘ t.app)) | z : μ → D }) ≤
    Finset.univ.val.summap (fun i : Fin m =>
        sInf { I.summap (fun t : Γ.Term (Fin n ⊕ μ) => ω.size • t.f (Sum.elim (x i) z ∘ t.app)) | z : μ → D })
  · sorry
  · sorry
  /-
  frpo : `m • ((ω.tt x).map f.snd).sum ≤ ω.size • (Finset.univ.val.map (fun i => f.snd (x i))).sum`
  -/
  have part_ineq :
    ∀ f₁ ∈ Γ, ∀ x₁ : Fin m → Fin f₁.fst → D,
      (ω.tt x₁).summap (fun v : Fin f₁.fst → D => m • f₁.snd v) ≤
      Finset.univ.val.summap (fun i : Fin m => ω.size • f₁.snd (x₁ i))
  · sorry -- from `frpo` using distributivity of `nsmul` over `sum` of `map`
  clear frpo
  -- now instantiate `part_ineq` for every term in `I`
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
