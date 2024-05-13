import Mathlib.LinearAlgebra.Matrix.DotProduct
import VCSP.Basic


class CompatiblyOrdered (R M : Type*) [OrderedSemiring R] [OrderedAddCommMonoid M] [Module R M] where
  smul_order : ∀ a : R, ∀ v : M, 0 ≤ a → 0 ≤ v → 0 ≤ a • v

instance (R : Type*) [OrderedSemiring R] : CompatiblyOrdered R R := ⟨fun _ _ => smul_nonneg⟩

variable {I : Type*} [Fintype I] -- typically `Fin m`

/- The paper by Bartl is actually more general, in particular allowing "skew fields" (`DivisionRing`),
   but Mathlib does not seem to have a definition `LinearOrderedDivisionRing`,
   so we work with `LinearOrderedField` for now. -/
theorem generalizedFarkasBartl {F V W : Type*} [LinearOrderedField F] -- typically `V` = `F` and `W` = `F^n`
    [LinearOrderedAddCommGroup V] [Module F V] [CompatiblyOrdered F V] [AddCommGroup W] [Module F W]
    (A : I → W →ₗ[F] F) (b : W →ₗ[F] V) :
    (∀ x : W, (A · x) ≤ 0 → b x ≤ 0) ↔ (∃ U : I → V, 0 ≤ U ∧
        ∀ w : W, b w = Finset.univ.sum (fun i : I => A i w • U i)) := by
  sorry

variable {J : Type*} [Fintype J]
open Matrix

theorem equalityFarkas (A : Matrix I J ℚ) (b : I → ℚ) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → ℚ, -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  let A' : J → (I → ℚ) →ₗ[ℚ] ℚ := fun i : J => ⟨⟨fun z : I → ℚ => (Aᵀ *ᵥ z) i, fun x y => by sorry⟩, by sorry⟩
  let b' : (I → ℚ) →ₗ[ℚ] ℚ := sorry
  have := generalizedFarkasBartl A' b'
  sorry
