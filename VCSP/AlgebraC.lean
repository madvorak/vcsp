import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.CompleteLattice

/-
We define a (partially) ordered commutative monoid that has infimum for every set.
Examples of this algebra are `ENat`, `ENNReal`, `EReal`, `Bool`, and tuples made of them.
-/

class OrderedAddCommMonoidWithInfima (C : Type*)
  extends OrderedAddCommMonoid C, CompleteSemilatticeInf C

def OrderedAddCommMonoidWithInfima.toCompleteLattice (C : Type*)
    [OrderedAddCommMonoidWithInfima C] : CompleteLattice C :=
  completeLatticeOfInf C isGLB_sInf
