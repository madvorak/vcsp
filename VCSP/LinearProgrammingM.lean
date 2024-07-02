import VCSP.FarkasBartl
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Analysis.InnerProductSpace.Adjoint


/-!

# Linear programming

We define linear programs in the coordinate-free form.

## Main definitions

 * `CoordinateFreeLP` defines a linear program in the coordinate-free form so that
    it resembles the standard form (maximize `c x` such that `A x ≤ b` and `x ≥ 0`).
 * `CoordinateFreeLP.IsSolution` tells if given vector is a solution satisfying given LP.
 * `CoordinateFreeLP.IsFeasible` tells if given LP has any solution.
 * `CoordinateFreeLP.Reaches` tells if given value can be obtained as a cost of any solution of given LP.

-/

structure CoordinateFreeLP (V W : Type*)
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    where
  /-- The left-hand-side linear map -/
  A : V →L[ℝ] W
  /-- The right-hand-side vector -/
  b : W
  /-- The linear function to optimize -/
  c : V →L[ℝ] ℝ
  /-- Positive directions -/
  p : PointedCone ℝ V

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedOrderedAddGroup W] [InnerProductSpace ℝ W]

def CoordinateFreeLP.IsSolution (P : CoordinateFreeLP V W) (x : V) : Prop :=
  P.A x ≤ P.b ∧ x ∈ P.p

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`. -/
def CoordinateFreeLP.IsFeasible (P : CoordinateFreeLP V W) : Prop :=
  ∃ x : V, P.IsSolution x

def CoordinateFreeLP.Reaches (P : CoordinateFreeLP V W) (r : ℝ) : Prop :=
  ∃ x : V, P.IsSolution x ∧ P.c x = r

noncomputable def CoordinateFreeLP.adjoint_map [CompleteSpace V] [CompleteSpace W] (P : CoordinateFreeLP V W) :
    W →L[ℝ] V :=
  ContinuousLinearMap.adjoint P.A
