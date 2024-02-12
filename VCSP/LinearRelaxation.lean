import VCSP.Hardness
import VCSP.LinearProgramming
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Matrix.ColumnRowPartitioned


variable
  {D : Type} [Nonempty D] [Fintype D] [DecidableEq D]
  {ι : Type} [Nonempty ι] [Fintype ι] [DecidableEq ι]
  {Γ : ValuedCSP D ℚ} [DecidableEq (Γ.Term ι)]

@[pp_dot]
def ValuedCSP.Instance.LPvars (I : Γ.Instance ι) : Type :=
  (Σ t : I, (Fin t.fst.n → D)) ⊕ (ι × D)

@[pp_dot]
def ValuedCSP.Instance.LPconds (I : Γ.Instance ι) : Type :=
  (Σ t : I, (Fin t.fst.n × D)) ⊕ ι ⊕ LPvars I

@[pp_dot]
def ValuedCSP.Instance.LPrelaxT (I : Γ.Instance ι) (cₜ : Γ.Term ι) (cᵢ : Fin cₜ.n) (cₐ : D) : I.LPvars → ℚ :=
  Sum.elim
    (fun ⟨⟨t, _⟩, x⟩ =>
      if ht : cₜ.n = t.n
      then if x (Fin.cast ht cᵢ) = cₐ then 1 else 0
      else 0)
    (fun ⟨i, a⟩ => if cₜ.app cᵢ = i ∧ cₐ = a then -1 else 0)

@[pp_dot]
def ValuedCSP.Instance.LPrelaxJ (I : Γ.Instance ι) (cᵢ : ι) : I.LPvars → ℚ :=
  Sum.elim
    (fun _ => 0)
    (fun ⟨i, _⟩ => if cᵢ = i then 1 else 0)

@[pp_dot]
def ValuedCSP.Instance.LPrelaxM (I : Γ.Instance ι) [DecidableEq (I.LPvars)] : Matrix I.LPconds I.LPvars ℚ :=
  Matrix.fromRows
    (Matrix.of fun ⟨⟨cₜ, _⟩, cᵢ, cₐ⟩ => I.LPrelaxT cₜ cᵢ cₐ)
    (Matrix.fromRows
      (Matrix.of fun cᵢ : ι => I.LPrelaxJ cᵢ)
      1)

@[pp_dot]
def ValuedCSP.Instance.LPrelaxR (I : Γ.Instance ι) : I.LPconds → ℚ :=
  Sum.elim
    (fun _ : (Σ t : I, (Fin t.fst.n × D)) => 0)
    (fun _ : (ι ⊕ I.LPvars) => 1)

@[pp_dot]
def ValuedCSP.Instance.LPrelaxC (I : Γ.Instance ι) : I.LPvars → ℚ :=
  Sum.elim
    (fun ⟨⟨t, _⟩, x⟩ => t.f x)
    (fun _ => 0)

@[pp_dot]
def ValuedCSP.Instance.LPrelaxation (I : Γ.Instance ι)
     -- TODO the following three must be inferred automatically !!!
    [Fintype I.LPvars] [Fintype I.LPconds] [DecidableEq (I.LPvars)] :
    StandardLP I.LPconds I.LPvars ℚ :=
  StandardLP.mk I.LPrelaxM I.LPrelaxR I.LPrelaxC


open scoped Matrix

lemma sumType_zeroFun_dotProduct {α β : Type} [Fintype α] [Fintype β]
    {u v : α → ℚ} {v' : β → ℚ} :
    (Sum.elim u 0) ⬝ᵥ (Sum.elim v v') = u ⬝ᵥ v := by
  rw [Matrix.sum_elim_dotProduct_sum_elim, Matrix.zero_dotProduct, add_zero]

@[pp_dot]
abbrev ValuedCSP.Instance.solutionVCSPtoLP (I : Γ.Instance ι) (x : ι → D) :
    I.LPvars → ℚ :=
  Sum.elim
    (fun ⟨⟨t, _⟩, (v : (Fin t.n → D))⟩ => if ∀ i : Fin t.n, v i = x (t.app i) then 1 else 0)
    (fun ⟨i, d⟩ => if x i = d then 1 else 0)

lemma ValuedCSP.Instance.solutionVCSPtoLP_IsSolution_aux (I : Γ.Instance ι)
    -- TODO the following three must be inferred automatically !!!
    [Fintype I.LPvars] [Fintype I.LPconds] [DecidableEq (I.LPvars)]
    (x : ι → D) :
    I.LPrelaxM *ᵥ I.solutionVCSPtoLP x ≤ I.LPrelaxR := by
  intro c
  cases c with
  | inl val =>
    obtain ⟨⟨⟨n, f, _, ξ⟩, _⟩, (cᵢ : Fin n), cₐ⟩ := val
    show _ ≤ 0
    simp only [LPrelaxM, solutionVCSPtoLP]
    rw [Matrix.fromRows_mulVec, Sum.elim_inl]
    sorry
  | inr val =>
    cases val with
    | inl cᵢ =>
      show _ ≤ 1
      simp only [LPrelaxM, solutionVCSPtoLP]
      rw [Matrix.fromRows_mulVec, Sum.elim_inr]
      rw [Matrix.fromRows_mulVec, Sum.elim_inl]
      simp only [ValuedCSP.Instance.LPrelaxJ]
      sorry
    | inr cᵥ =>
      show _ ≤ 1
      simp only [LPrelaxM, solutionVCSPtoLP]
      rw [Matrix.fromRows_mulVec, Sum.elim_inr]
      rw [Matrix.fromRows_mulVec, Sum.elim_inr]
      rw [Matrix.one_mulVec]
      cases cᵥ <;> aesop

lemma ValuedCSP.Instance.solutionVCSPtoLP_IsSolution (I : Γ.Instance ι)
     -- TODO the following three must be inferred automatically !!!
    [Fintype I.LPvars] [Fintype I.LPconds] [DecidableEq (I.LPvars)]
    (x : ι → D) :
    StandardLP.IsSolution I.LPrelaxation (I.solutionVCSPtoLP x) := by
  simp [StandardLP.IsSolution, ValuedCSP.Instance.LPrelaxation]
  constructor
  · apply I.solutionVCSPtoLP_IsSolution_aux
  · intro v
    cases v <;> aesop

theorem ValuedCSP.Instance.LPrelaxation_Reaches (I : Γ.Instance ι)
     -- TODO the following three must be inferred automatically !!!
    [Fintype I.LPvars] [Fintype I.LPconds] [DecidableEq (I.LPvars)]
    (x : ι → D) :
    I.LPrelaxation.Reaches (I.evalSolution x) := by
  use I.solutionVCSPtoLP x
  constructor
  · apply I.solutionVCSPtoLP_IsSolution
  · simp [ValuedCSP.Instance.LPrelaxation, ValuedCSP.Instance.evalSolution]
    trans
    · convert sumType_zeroFun_dotProduct <;> infer_instance
    sorry
