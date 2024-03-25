import Mathlib.Combinatorics.Optimization.ValuedCSP


lemma FractionalOperation.IsValid.tt_nonempty {D ι : Type*} {m : ℕ} {ω : FractionalOperation D m}
    (valid : ω.IsValid) {x : Fin m → ι → D} :
    ω.tt x ≠ ∅ := by
  convert valid
  simp [FractionalOperation.tt]
