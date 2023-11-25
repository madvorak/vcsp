import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.CompleteLattice

class OrderedAddCommMonoidWithInfima (C : Type*)
  extends OrderedAddCommMonoid C, CompleteSemilatticeInf C

def OrderedAddCommMonoidWithInfima.toCompleteLattice (C : Type*)
    [OrderedAddCommMonoidWithInfima C] : CompleteLattice C :=
  completeLatticeOfInf C isGLB_sInf
