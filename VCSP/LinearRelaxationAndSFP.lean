import VCSP.LinearRelaxation
import Mathlib.Data.Fin.Tuple.Curry

variable
  {D : Type} [Nonempty D] [Fintype D] [DecidableEq D]
  {ι : Type} [Nonempty ι] [Fintype ι] [DecidableEq ι]
  {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

def aux (κ : D → ℕ) : ∃ m : ℕ, ∃ v : Fin m → D, ∀ a : D, 0 < κ a ↔ ∃ i : Fin m, v i = a := by
  let l : List D := List.join (Finset.univ.val.map (fun d : D => List.replicate (κ d) d)).toList
  use l.length
  use l.get
  intro a
  constructor <;> intro hyp
  · apply List.get_of_mem
    rw [List.mem_join]
    simp only [Multiset.mem_toList, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    rw [exists_exists_eq_and]
    use a
    rw [List.mem_replicate]
    constructor
    · rwa [Nat.pos_iff_ne_zero] at hyp
    · rfl
  · rw [←List.mem_iff_get, List.mem_join] at hyp
    simp only [Multiset.mem_toList, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hyp
    rw [exists_exists_eq_and] at hyp
    obtain ⟨a', ha'⟩ := hyp
    rw [List.mem_replicate] at ha'
    obtain ⟨ha, rfl⟩ := ha'
    exact Nat.pos_of_ne_zero ha

example (δ : D → ℚ) (non_neg : 0 ≤ δ) (sum_one : Finset.univ.sum δ = 1) :
    ∃ m : ℕ, ∃ v : Fin m → D, ∀ a : D, 0 < δ a ↔ ∃ i : Fin m, v i = a := by
  let w : D → ℕ := fun a : D =>
    Finset.univ.prod (fun b : D => if a = b then (δ b).num.toNat else (δ b).den)
  obtain ⟨m, v, rest⟩ := aux w
  use m
  use v
  intro a
  rw [← rest a]
  constructor <;> intro hyp
  · sorry
  · apply lt_of_le_of_ne
    · exact non_neg a
    symm
    apply ne_of_gt at hyp
    rw [Finset.prod_ne_zero_iff] at hyp
    convert hyp a (Finset.mem_univ a)
    simp only [↓reduceIte, Int.toNat_eq_zero]
    have triv : (δ a).num ≤ 0 ↔ (δ a).num = 0
    · constructor
      · intro hle
        apply eq_of_le_of_not_lt hle
        push_neg
        exact Rat.num_nonneg_iff_zero_le.mpr (non_neg a)
      · apply Eq.le
    rw [triv]
    apply Rat.zero_iff_num_zero

def Function.unaryAdmitsFractional {m : ℕ} (f : D → ℚ) (ω : FractionalOperation D m) : Prop :=
  ∀ x : (Fin m → D),
    m • (ω.map (· x)).summap f ≤ ω.size • Finset.univ.sum (fun i => f (x i))

noncomputable def convertDistribution_aux {δ : ι → D → ℚ} (nonneg : 0 ≤ δ) : Σ m : ℕ, ι → Fin m → D := by
  let w : ι → D → ℕ := fun i : ι => fun a : D =>
    Finset.univ.prod (fun j : ι =>
      Finset.univ.prod (fun b : D => if i = j ∧ a = b then (δ j b).num.toNat else (δ j b).den)
    )
  use Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => (δ j b).den))
  intro i
  let l : List D := List.join (Finset.univ.val.map (fun d : D => List.replicate (w i d) d)).toList
  have llen : l.length = Finset.univ.prod (fun j : ι => Finset.univ.prod (fun b : D => (δ j b).den))
  · have missing : ∀ j : ι, Finset.univ.sum (δ j) = 1
    · sorry
    rw [List.length_join]
    sorry
  convert l.get
  exact llen.symm

-- TODO change to perhaps `∃ m : ℕ, ∃ v : Fin m → ι → D, ` (properties of `v` wrt `δ`)
noncomputable def convertDistribution {δ : ι → D → ℚ} (nonneg : 0 ≤ δ) : Σ m : ℕ, Fin m → ι → D :=
  let ⟨m, v⟩ := convertDistribution_aux nonneg
  ⟨m, Function.swap v⟩

open scoped Matrix

lemma ValuedCSP.Instance.RelaxBLP_case_single_unary_function
    (I : Γ.Instance ι) {o : ℚ} (ho : I.RelaxBLP.Reaches o)
    {f : D → ℚ} (hf : Γ = {⟨1, Function.OfArity.uncurry f⟩})
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ f.unaryAdmitsFractional ω ∧ ω.IsSymmetric) :
    ∃ m : ℕ, ∃ ω : FractionalOperation D m,
      ω.IsValid ∧ ∃ X : Fin m → ι → D, (ω.tt X).summap I.evalSolution ≤ ω.size • o := by
  obtain ⟨x, ⟨x_equl, x_nneg⟩, x_cost⟩ := ho
  let δ : ι → D → ℚ := fun i d => x (Sum.inr ⟨i, d⟩)
  have nonneg : 0 ≤ δ := fun i d => x_nneg (Sum.inr (i, d))
  obtain ⟨m, X⟩ := convertDistribution nonneg -- TODO get more info from here
  use m
  obtain ⟨ω, valid, frpol, symmega⟩ := hΓ m
  use ω
  constructor
  · exact valid
  use X
  rw [← x_cost]
  clear x_cost
  suffices mtimes : m • (ω.tt X).summap I.evalSolution ≤ m • ω.size • Matrix.dotProduct I.RelaxBLP.c x
  · have : 0 < m := sorry -- will come from API around `convertDistribution`
    simp_all
  show       m • (ω.tt X).summap (fun s => I.summap (fun t => t.f (s ∘ t.app))) ≤ m • ω.size • (I.RelaxBLP.c ⬝ᵥ x)
  convert_to m • (ω.tt X).summap (fun s => I.summap (fun t => f (s (t.app 0)))) ≤ m • ω.size • (I.RelaxBLP.c ⬝ᵥ x)
  swap
  · intro s t
    have ht1 : t.n = 1
    · suffices : (⟨t.n, t.f⟩ : Σ (n : ℕ), (Fin n → D) → ℚ) ∈ ({⟨1, Function.OfArity.uncurry f⟩} : ValuedCSP D ℚ)
      · aesop
      convert t.inΓ
      exact hf.symm
    simp only [ht1]
    exact ⟨⟨0, (show 1 ≤ 1 by rfl)⟩⟩
  · have ht : ∀ t ∈ I, (⟨t.n, t.f⟩ : Σ (n : ℕ), (Fin n → D) → ℚ) = ⟨1, Function.OfArity.uncurry f⟩
    · intro t tin
      suffices : (⟨t.n, t.f⟩ : Σ (n : ℕ), (Fin n → D) → ℚ) ∈ ({⟨1, Function.OfArity.uncurry f⟩} : ValuedCSP D ℚ)
      · aesop
      convert t.inΓ
      exact hf.symm
    congr
    ext1 s
    congr
    ext1 t
    specialize ht t sorry
    rw [Sigma.mk.inj_iff] at ht
    sorry
  sorry

lemma ValuedCSP.Instance.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux
    (I : Γ.Instance ι) {o : ℚ} (ho : I.RelaxBLP.Reaches o)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ) :
    ∃ m : ℕ, ∃ ω : FractionalOperation D m,
      ω.IsValid ∧ ∃ X : Fin m → ι → D, (ω.tt X).summap I.evalSolution ≤ ω.size • o := by
  obtain ⟨x, ⟨x_equl, x_nneg⟩, x_cost⟩ := ho
  let δ : ι → D → ℚ := fun i d => x (Sum.inr ⟨i, d⟩)
  have nonneg : 0 ≤ δ := fun i d => x_nneg (Sum.inr (i, d))
  obtain ⟨m, X⟩ := convertDistribution nonneg -- TODO get more info from here
  use m
  obtain ⟨ω, valid, frpol, symmega⟩ := hΓ m
  use ω
  constructor
  · exact valid
  use X
  rw [← x_cost]
  clear x_cost
  suffices mtimes : m • (ω.tt X).summap I.evalSolution ≤ m • ω.size • Matrix.dotProduct I.RelaxBLP.c x
  · have : 0 < m := sorry -- will come from API around `convertDistribution`
    simp_all
  apply (frpol.onInstance I X).trans
  rw [smul_comm]
  have zero_lt_size : 0 < ω.size := valid.size
  simp_all
  simp_rw [← ValuedCSP.Instance.solutionVCSPtoBLP_cost]
  show
    Finset.univ.sum (fun j : Fin m => I.RelaxBLP.c ⬝ᵥ (I.solutionVCSPtoBLP (X j))) ≤
    m * I.RelaxBLP.c ⬝ᵥ x
  -- thanks to `symmega` we can replace a relationship between `X` and `x (Sum.inl ..)` by
  -- a relationship between `x (Sum.inr ..)` and `x (Sum.inl ..)` hopefully
  sorry

theorem ValuedCSP.Instance.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms
    (I : Γ.Instance ι) {o : ℚ} (ho : I.RelaxBLP.Reaches o)
    (hΓ : ∀ m : ℕ, ∃ ω : FractionalOperation D m, ω.IsValid ∧ ω.IsSymmetricFractionalPolymorphismFor Γ) :
    ∃ x : ι → D, I.evalSolution x ≤ o := by
  by_contra! contr
  obtain ⟨m, ω, valid, X, result⟩ := I.RelaxBLP_improved_of_allSymmetricFractionalPolymorphisms_aux ho hΓ
  have impos : (ω.tt X).summap I.evalSolution < (ω.tt X).summap I.evalSolution
  · apply result.trans_lt
    convert_to ((ω.tt X).map (fun _ => o)).sum < (ω.tt X).summap I.evalSolution
    · simp [FractionalOperation.tt]
    apply Multiset.summap_lt_summap valid.tt_nonempty
    simp [contr]
  exact impos.false
