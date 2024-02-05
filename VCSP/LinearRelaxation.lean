import VCSP.Hardness
import VCSP.LinearProgramming


variable {D : Type} [Nonempty D] [Fintype D] [DecidableEq D]

def ValuedCSP.Instance.LPvars {Γ : ValuedCSP D ℚ} {ι : Type} [Fintype ι] (I : Γ.Instance ι) : Type :=
  (Σ t : {_t : Γ.Term ι // _t ∈ I}, (Fin t.val.n → D)) ⊕ (ι × D)

def ValuedCSP.Instance.LPcons {Γ : ValuedCSP D ℚ} {ι : Type} [Fintype ι] (I : Γ.Instance ι) : Type :=
  (Σ t : {_t : Γ.Term ι // _t ∈ I}, (Fin t.val.n × D)) ⊕ ι ⊕ LPvars I

/-
For all `⟨t, j, a⟩` in `(Σ t ∈ I, Fin t.n × D)`, the sum of all |D| ^ (t.n - 1)
  `Sum.inl ⟨t, (x : Fin t.n → D | x j = a)⟩` must be equal to `Sum.inr (t.app j, a)`.
For all `i` in `ι`, the sum of all |D| `Sum.inr (i, _)` must be `1`.
Each `v` in `LPvars I` must be between `0` and `1`.

Ideally (--> tight relaxation)...
For each `i` in `ι`, there is exactly one `a` in `D` where
  `Sum.inr (i, a)` is `1` and all other `Sum.inr (i, _)` are `0`.
For all `⟨t, j⟩` in `(Σ t ∈ I, Fin t.n)`:
  · If `Sum.inr (t.app j, a)` is `0` then all `Sum.inl ⟨t, (x : Fin t.n → D | x j = a)⟩` are `0`.
  · If `Sum.inr (t.app j, a)` is `1` then there is exactly one `x : Fin t.n → D | x j = a` where
    `Sum.inl ⟨t, x⟩` is `1` and all other `Sum.inl ⟨t, (x : Fin t.n → D | x j = a)⟩` are `0`.
-/

def ValuedCSP.Instance.LPrelax {Γ : ValuedCSP D ℚ} {ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq (Γ.Term ι)]
    (I : Γ.Instance ι)
    [Fintype I.LPcons] [Fintype I.LPvars] : -- TODO these two must be inferred automatically!!
    StandardLP I.LPcons I.LPvars ℚ :=
  have _ : DecidableEq (I.LPvars) := instDecidableEqSum
  StandardLP.mk (
    fun
    | .inl ⟨⟨cₜ, _⟩, cᵢ, cₐ⟩ => fun
      | .inl ⟨⟨t, _⟩, x⟩ =>
        if ht : cₜ = t then
          if x (cast (congr_arg (Fin ∘ Term.n) ht) cᵢ) = cₐ
          then 1
          else 0
        else 0
      | .inr ⟨i, a⟩ => if cₜ.app cᵢ = i ∧ cₐ = a then -1 else 0
    | .inr (.inl cᵢ) => fun
      | .inl _ => 0
      | .inr ⟨i, _⟩ => if cᵢ = i then 1 else 0
    | .inr (.inr cᵥ) => fun
        v => if cᵥ = v then 1 else 0
  ) (
    fun
    | .inl _ => 0
    | .inr _ => 1
  ) (
    fun
    | .inl ⟨⟨⟨_, f, _, _⟩, _⟩, x⟩ => f x
    | .inr _ => 0
  )

theorem ValuedCSP.Instance.LPrelax_solution {Γ : ValuedCSP D ℚ} {ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq (Γ.Term ι)]
    (I : Γ.Instance ι) [Fintype I.LPcons] [Fintype I.LPvars] (x : ι → D) :
    I.LPrelax.Reaches (I.evalSolution x) := by
  let s : I.LPvars → ℚ := fun
    | .inl ⟨⟨t, tin⟩, (v : (Fin t.n → D))⟩ => if ∀ i : Fin t.n, v i = x (t.app i) then 1 else 0
    | .inr ⟨i, d⟩ => if x i = d then 1 else 0
  use s
  constructor
  · sorry
  · sorry
