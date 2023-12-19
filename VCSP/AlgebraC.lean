import Mathlib.Algebra.Order.Monoid.Defs

/-
We define a (partially) ordered commutative monoid that has infimum for every nonempty finite set.
Examples of this algebra are `Bool`, `Nat`, `ENat`, `Int`, `NNRat`, `Rat`, `NNReal`, `ENNReal`, `Real`, `EReal`,
and tuples made of them.
-/

class OrderedAddCommMonoidWithInfima (C : Type*)
  extends OrderedAddCommMonoid C, SemilatticeInf C

/-
We define a cancellative (partially) ordered commutative monoid that has infimum for every nonempty finite set.
Examples of this algebra are `Nat`, `Int`, `NNRat`, `Rat`, `NNReal`, `Real`, and tuples made of them.
-/

class OrderedCancelAddCommMonoidWithInfima (C : Type*)
  extends OrderedCancelAddCommMonoid C, OrderedAddCommMonoidWithInfima C
