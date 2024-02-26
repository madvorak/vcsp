import VCSP.LinearRelaxation

variable
  {D : Type} [Nonempty D] [Fintype D] [DecidableEq D]
  {ι : Type} [Nonempty ι] [Fintype ι] [DecidableEq ι]
  {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

example (δ : D → ℚ) (non_neg : 0 ≤ δ) (sum_one : Finset.univ.sum δ = 1) :
    ∃ m : ℕ, ∃ v : Fin m → D, ∀ a : D, 0 < δ a ↔ ∃ i : Fin m, v i = a := by
  let w : D → ℕ := fun a : D =>
    Finset.univ.prod (fun b : D => if a = b then (δ b).num.toNat else (δ b).den)
  use Finset.univ.sum w
  --let l : List D := List.join (Finset.univ.val.map (fun d : D => List.replicate (w d) d)).toList
  --use l.length
  sorry

-- TODO change to perhaps `∃ m : ℕ, ∃ v : Fin m → D, ` (properties of `v` wrt `δ`)
def convertDistribution {δ : ι → D → ℚ} (nonneg : 0 ≤ δ) : Σ m : ℕ, Fin m → ι → D := sorry
  -- We have a discrete probability distributions over rationals.
  -- How do we get them all to a common denominator?
  -- Furthermore, convert them to vectors!

open scoped Matrix

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
