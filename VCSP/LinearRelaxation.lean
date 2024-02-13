import VCSP.Hardness
import VCSP.LinearProgramming
import Mathlib.Data.Multiset.Fintype


variable
  {D : Type} [Nonempty D] [Fintype D] [DecidableEq D]
  {ι : Type} [Nonempty ι] [Fintype ι] [DecidableEq ι]
  {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

instance deceqInstance (I : Γ.Instance ι) : DecidableEq I :=
  inferInstanceAs (DecidableEq (Σ t : Γ.Term ι, Fin (I.count t)))

@[pp_dot]
def ValuedCSP.Instance.LPrelaxation (I : Γ.Instance ι) :
    BothieLP
      ((Σ t : I, (Fin t.fst.n → D)) ⊕ (ι × D)) -- variables
      ((Σ t : I, (Fin t.fst.n × D)) ⊕ ι) -- inequalities
      ((Σ t : I, (Fin t.fst.n → D)) ⊕ (ι × D)) -- equalities
      ℚ :=
  BothieLP.mk
    (Matrix.fromRows
      (Matrix.fromColumns
        (Matrix.of fun ⟨⟨cₜ, _⟩, cᵢ, cₐ⟩ => fun ⟨⟨t, _⟩, x⟩ =>
          if ht : cₜ.n = t.n
          then if x (Fin.cast ht cᵢ) = cₐ then 1 else 0
          else 0)
        (Matrix.of fun ⟨⟨cₜ, _⟩, cᵢ, cₐ⟩ => fun ⟨i, a⟩ => if cₜ.app cᵢ = i ∧ cₐ = a then -1 else 0))
      (Matrix.fromColumns 0 (Matrix.of fun cᵢ : ι => fun ⟨i, _⟩ => if cᵢ = i then 1 else 0)))
    (Sum.elim
      (fun _ : (Σ t : I, (Fin t.fst.n × D)) => 0)
      (fun _ : ι => 1))
    1 -- the identity matrix
    1 -- the all ones vector
    (Sum.elim
      (fun ⟨⟨t, _⟩, x⟩ => t.f x)
      (fun _ => 0))


open scoped Matrix

lemma sumType_zeroFun_dotProduct {α β : Type} [Fintype α] [Fintype β]
    (u v : α → ℚ) (v' : β → ℚ) :
    (Sum.elim u 0) ⬝ᵥ (Sum.elim v v') = u ⬝ᵥ v := by
  rw [Matrix.sum_elim_dotProduct_sum_elim, Matrix.zero_dotProduct, add_zero]

lemma zeroMat_fromColumns_mulVec {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (A₂ : Matrix α γ ℚ) (v₁ : β → ℚ) (v₂ : γ → ℚ) :
    Matrix.fromColumns 0 A₂ *ᵥ Sum.elim v₁ v₂ = A₂ *ᵥ v₂ := by
  rw [Matrix.fromColumns_mulVec_sum_elim, Matrix.zero_mulVec, zero_add]

private lemma zeroMat_fromColumns_mulVec_sumElim_index_le_one {α β γ : Type}
    (_ : Fintype α) (_ : Fintype β) (_ : Fintype γ)
    {A₂ : Matrix α γ ℚ} {v₁ : β → ℚ} {v₂ : γ → ℚ} {a : α}
    (todo : (A₂ *ᵥ v₂) a ≤ 1) :
    (Matrix.fromColumns 0 A₂ *ᵥ Sum.elim v₁ v₂) a ≤ 1 := by
  rw [zeroMat_fromColumns_mulVec]
  exact todo

@[pp_dot]
abbrev ValuedCSP.Instance.solutionVCSPtoLP (I : Γ.Instance ι) (x : ι → D) :
    ((Σ t : I, (Fin t.fst.n → D)) ⊕ (ι × D)) → ℚ :=
  Sum.elim
    (fun ⟨⟨t, _⟩, (v : (Fin t.n → D))⟩ => if ∀ i : Fin t.n, v i = x (t.app i) then 1 else 0)
    (fun ⟨i, d⟩ => if x i = d then 1 else 0)

theorem ValuedCSP.Instance.LPrelaxation_Reaches (I : Γ.Instance ι) (x : ι → D) :
    I.LPrelaxation.Reaches (I.evalSolution x) := by
  use I.solutionVCSPtoLP x
  constructor
  · sorry
  · sorry
