import VCSP.LinearProgramming
import Mathlib.Tactic.Qify

open scoped Matrix


variable {n : Type} [Fintype n] [DecidableEq n]

def rationalSolutionToCommon (x : n → ℚ) : ℕ × (n → ℕ) :=
  ⟨Finset.univ.prod (fun i : n => (x i).den),
   fun j : n => Finset.univ.prod (fun i : n => if i = j then (x i).num.toNat else (x i).den)⟩

variable {m : Type} [Fintype m]

lemma CanonicalLP.IsSolution.toCommon {P : CanonicalLP n m ℚ} {x : n → ℚ} (hx : P.IsSolution x) :
    let r := rationalSolutionToCommon x ;
    P.A *ᵥ (fun j : n => mkRat (r.snd j) r.fst) = P.b := by
  ext1 j
  convert_to
    Finset.univ.sum (fun i =>
      P.A j i * mkRat
        (Finset.univ.prod fun j' => if j' = i then (x j').num else (x j').den.cast)
        (Finset.univ.prod fun j' => (x j').den)) =
      P.b j
  · simp only [Matrix.mulVec, Matrix.dotProduct, rationalSolutionToCommon, Nat.cast_prod, Nat.cast_ite]
    congr
    ext1
    congr
    ext1
    congr
    apply Int.toNat_of_nonneg
    rw [Rat.num_nonneg_iff_zero_le]
    apply hx.right
  convert_to Finset.univ.sum (fun i => P.A j i * mkRat (x i).num (x i).den) = P.b j
  · congr
    ext1 i
    apply congr_arg
    have hxiz : (x i).den.cast = 0 → (x i).num = 0
    · intro impos
      exfalso
      rw [Nat.cast_eq_zero] at impos
      exact (x i).den_nz impos
    rw [Rat.eq_iff_mul_eq_mul]
    qify
    sorry
  convert_to Finset.univ.sum (fun i => P.A j i * x i) = P.b j
  · congr
    ext1 i
    rw [Rat.mkRat_self (x i)]
  exact congr_fun hx.left j
