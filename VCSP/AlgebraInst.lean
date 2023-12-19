import Mathlib.Data.Fintype.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.NNRat
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Real.EReal
import VCSP.AlgebraC

/-
We provide `OrderedAddCommMonoidWithInfima` instances for
`Nat`, `ENat`, `Int`, `NNRat`, `Rat`, `NNReal`, `ENNReal`, `Real`, `EReal`, and
hopefully soon for `Bool` (probably "upside down") as well.
Tuples of above-mentioned types get inferred easily, as exemplified below them.
-/

instance crispCodomain : OrderedAddCommMonoid Bool where
-- https://github.com/leanprover-community/mathlib4/blob/a49e19b813838ed5c0c3bb890b077227d7b5cb96/test/ValuedCSP.lean
  __ := Bool.linearOrder
  add (a b : Bool) := a || b
  add_assoc := Bool.or_assoc
  zero := false
  zero_add (_ : Bool) := rfl
  add_zero := Bool.or_false
  add_comm := Bool.or_comm
  add_le_add_left := sorry -- proved in above-mentioned PR

macro (name := infInstTactic) "infInst" : tactic =>
    `(tactic| (constructor; apply inf_le_left; apply inf_le_right; apply le_inf))

noncomputable instance : OrderedAddCommMonoidWithInfima Bool := by
  infInst

instance : OrderedAddCommMonoidWithInfima Nat := by
  infInst

noncomputable instance : OrderedAddCommMonoidWithInfima ENat := by
  infInst

instance : OrderedAddCommMonoidWithInfima Int := by
  infInst

instance : OrderedAddCommMonoidWithInfima NNRat := by
  infInst

instance : OrderedAddCommMonoidWithInfima Rat := by
  infInst

noncomputable instance : OrderedAddCommMonoidWithInfima NNReal := by
  infInst

noncomputable instance : OrderedAddCommMonoidWithInfima ENNReal := by
  infInst

instance : OrderedAddCommMonoidWithInfima Real := by
  infInst

noncomputable instance : OrderedAddCommMonoidWithInfima EReal := by
  infInst

noncomputable instance : OrderedAddCommMonoidWithInfima (EReal × EReal) := by
  infInst

noncomputable instance : OrderedAddCommMonoidWithInfima (Unit × Bool × ENat × NNReal × EReal) := by
  infInst

/-
We provide `OrderedCancelAddCommMonoidWithInfima` instances for
`Nat`, `Int`, `NNRat`, `Rat`, `NNReal`, `Real`.
Tuples of above-mentioned types get inferred easily, as exemplified below them.
-/

instance : OrderedCancelAddCommMonoidWithInfima Nat := by
  infInst

instance : OrderedCancelAddCommMonoidWithInfima Int := by
  infInst

instance : OrderedCancelAddCommMonoidWithInfima NNRat := by
  infInst

instance : OrderedCancelAddCommMonoidWithInfima Rat := by
  infInst

noncomputable instance : OrderedCancelAddCommMonoidWithInfima NNReal := by
  infInst

instance : OrderedCancelAddCommMonoidWithInfima Real := by
  infInst

instance : OrderedCancelAddCommMonoidWithInfima (Nat × NNRat × Real) := by
  infInst
