import VCSP.FarkasBartl


import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section experimental

example {V W R : Type*} [RCLike R]
    [NormedAddCommGroup V] [InnerProductSpace R V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace R W] [CompleteSpace W]
    (f : V →L[R] W) : W →L[R] V :=
  ContinuousLinearMap.adjoint f

example {V W R : Type*} [RCLike R]
    [NormedAddCommGroup V] [InnerProductSpace R V] [FiniteDimensional R V]
    [NormedAddCommGroup W] [InnerProductSpace R W] [FiniteDimensional R W]
    (f : V →ₗ[R] W) : W →ₗ[R] V :=
  LinearMap.adjoint f

end experimental


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

structure CoordinateFreeLP (V W R : Type*) [OrderedSemiring R]
    [OrderedAddCommGroup V] [Module R V] [PosSMulMono R V]
    [OrderedAddCommGroup W] [Module R W] where
  /-- The left-hand-side linear map -/
  A : V →ₗ[R] W
  /-- The right-hand-side vector -/
  b : W
  /-- The linear function to optimize -/
  c : V →ₗ[R] R

open scoped Matrix
variable {V W R : Type*} [OrderedSemiring R]
    [OrderedAddCommGroup V] [Module R V] [PosSMulMono R V]
    [OrderedAddCommGroup W] [Module R W]

def CoordinateFreeLP.IsSolution (P : CoordinateFreeLP V W R) (x : V) : Prop :=
  P.A x ≤ P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there exists a vector `x` that is a solution to `P`. -/
def CoordinateFreeLP.IsFeasible (P : CoordinateFreeLP V W R) : Prop :=
  ∃ x : V, P.IsSolution x

def CoordinateFreeLP.Reaches (P : CoordinateFreeLP V W R) (r : R) : Prop :=
  ∃ x : V, P.IsSolution x ∧ P.c x = r
