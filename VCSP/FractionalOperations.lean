import Mathlib.Combinatorics.Optimization.ValuedCSP


variable {D : Type*} {m : ℕ} {ω : FractionalOperation D m}

lemma FractionalOperation.IsValid.size_pos (valid : ω.IsValid) : 0 < ω.size := by
  rwa [FractionalOperation.size, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, Multiset.card_pos]

lemma FractionalOperation.IsValid.tt_nonempty {ι : Type*} (valid : ω.IsValid) {x : Fin m → ι → D} :
    ω.tt x ≠ ∅ := by
  convert valid
  simp [FractionalOperation.tt]
