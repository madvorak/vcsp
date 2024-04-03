import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Have

open scoped Matrix


/-- Linear program in the canonical form. Variables are of type `n`. Conditions are indexed by type `m`. -/
structure CanonicalLP (n m R : Type*)
    [Fintype n] [Fintype m] [OrderedAddCommMonoid R] [Mul R] where
  /-- Matrix of coefficients -/
  A : Matrix m n R
  /-- Right-hand side -/
  b : m → R
  /-- Objective function coefficients -/
  c : n → R

variable {n m R : Type*} [Fintype n] [Fintype m] [OrderedAddCommMonoid R] [Mul R]

def mulMatVec (M : Matrix m n R) (v : n → R) : m → R
  | i => (fun j => M i j) ⬝ᵥ v

infixr:73 " ₘ*ᵥ " => mulMatVec

def mulVecMat [Fintype m] (v : m → R) (M : Matrix m n R) : n → R
  | j => v ⬝ᵥ (fun i => M i j)

infixl:73 " ᵥ*ₘ " => mulVecMat

/-- Vector `x` is a solution to linear program `P` iff all entries of `x` are nonnegative and
its multiplication by matrix `A` from the left yields the vector `b`. -/
def CanonicalLP.IsSolution (P : CanonicalLP n m R) (x : n → R) : Prop :=
  P.A ₘ*ᵥ x = P.b ∧ 0 ≤ x

/-- Linear program `P` is feasible iff there is a vector `x` that is a solution to `P`. -/
def CanonicalLP.IsFeasible (P : CanonicalLP n m R) : Prop :=
  ∃ x : n → R, P.IsSolution x

/-- Linear program `P` reaches objective value `v` iff there is a solution `x` such that,
when its entries are elementwise multiplied by the costs (given by the vector `c`) and summed up,
the result is the value `v`. -/
def CanonicalLP.Reaches (P : CanonicalLP n m R) (v : R) : Prop :=
  ∃ x : n → R, P.IsSolution x ∧ P.c ⬝ᵥ x = v
