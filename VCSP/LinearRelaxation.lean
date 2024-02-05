import VCSP.Hardness

variable {D C : Type*} [Nonempty D] [Fintype D] [LinearOrderedAddCommMonoid C]

def ValuedCSP.Instance.LPvars {Γ : ValuedCSP D C} {ι : Type*} [Fintype ι] (I : Γ.Instance ι) : Type _ :=
  (Π t ∈ I, Fin t.n → D) ⊕ (ι × D)

def ValuedCSP.Instance.LPcons {Γ : ValuedCSP D C} {ι : Type*} [Fintype ι] (I : Γ.Instance ι) : Type _ :=
  (Π t ∈ I, Fin t.n × D) ⊕ ι ⊕ LPvars I

/-
For all `⟨t, j, a⟩` in `(Π t ∈ I, Fin t.n × D)`, the sum of all |D| ^ (t.n - 1)
  `Sum.inl ⟨t, (x : Fin t.n → D | x j = a)⟩` must be equal to `Sum.inr (t.app j, a)`.
For all `i` in `ι`, the sum of all |D| `Sum.inr (i, _)` must be `1`.
Each `v` in `LPvars I` must be between `0` and `1`.

Ideally (--> tight relaxation)...
For each `i` in `ι`, there is exactly one `a` in `D` where
  `Sum.inr (i, a)` is `1` and all other `Sum.inr (i, _)` are `0`.
For all `⟨t, j⟩` in `(Π t ∈ I, Fin t.n)`:
  · If `Sum.inr (t.app j, a)` is `0` then all `Sum.inl ⟨t, (x : Fin t.n → D | x j = a)⟩` are `0`.
  · If `Sum.inr (t.app j, a)` is `1` then there is exactly one `x : Fin t.n → D | x j = a` where
    `Sum.inl ⟨t, x⟩` is `1` and all other `Sum.inl ⟨t, (x : Fin t.n → D | x j = a)⟩` are `0`.
-/
