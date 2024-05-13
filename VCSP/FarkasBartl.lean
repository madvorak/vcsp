import Mathlib.LinearAlgebra.Matrix.DotProduct
import VCSP.Basic


class CompatiblyOrdered (R M : Type*) [OrderedSemiring R] [OrderedAddCommMonoid M] [Module R M] where
  smul_order : ∀ a : R, ∀ v : M, 0 ≤ a → 0 ≤ v → 0 ≤ a • v


variable {I : Type*} [Fintype I] -- typically `Fin m`

/- The paper by Bartl is actually more general, in particular allowing "skew fields" (`DivisionRing`),
   but Mathlib does not seem to have a definition `LinearOrderedDivisionRing`,
   so we work with `LinearOrderedField` for now. -/
theorem generalFarkasBartl {F V W : Type*} [LinearOrderedField F] -- typically `V` = `F` and `W` = `F^n`
    [LinearOrderedAddCommGroup V] [Module F V] [CompatiblyOrdered F V] [AddCommGroup W] [Module F W]
    (A : I → W →ₗ[F] F) (b : W →ₗ[F] V) :
    (∀ x : W, (∀ i : I, A i x ≤ 0) → b x ≤ 0) ↔ (∃ U : I → V, (∀ i : I, 0 ≤ U i) ∧
        (∀ w : W, b w = Finset.univ.sum (fun i : I => A i w • U i))) := by
  sorry

variable {J : Type*} [Fintype J]
open Matrix

theorem equalityFarkas (A : Matrix I J ℚ) (b : I → ℚ) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → ℚ, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  sorry -- TODO prove it follows from `generalFarkasBartl`
