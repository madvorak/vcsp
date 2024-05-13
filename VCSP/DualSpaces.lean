import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Dual

open scoped Matrix

variable {I J R : Type*} [Fintype I] [Fintype J] [CommSemiring R]

def Matrix.dotProduct_toLinearMap (a : J → R) : Module.Dual R (J → R) := -- (J → R) →ₗ[R] R :=
  ⟨⟨(a ⬝ᵥ ·), Matrix.dotProduct_add a⟩, fun r x => Matrix.dotProduct_smul r a x⟩

def Matrix.mulVec_toLinearMap (A : Matrix I J R) : I → Module.Dual R (J → R) := -- I → (J → R) →ₗ[R] R :=
  fun i : I => Matrix.dotProduct_toLinearMap (A i)

lemma Matrix.mulVec_toLinearMap_apply (A : Matrix I J R) (x : J → R) :
    (A.mulVec_toLinearMap · x) = (A *ᵥ x) := by
  rfl
