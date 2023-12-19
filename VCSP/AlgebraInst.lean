import Mathlib.Data.Fintype.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.NNRat
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Real.EReal
import VCSP.AlgebraC

/-
We provide `OrderedAddCommMonoidWithInfima` instances for
`Nat`, `ENat`, `Int`, `NNRat`, `Rat`, `NNReal`, `ENNReal`, `Real`, `EReal`, and
hopefully soon for `Bool` ("upside down") as well.
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

noncomputable instance : OrderedAddCommMonoidWithInfima Bool := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedAddCommMonoidWithInfima Nat := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

noncomputable instance : OrderedAddCommMonoidWithInfima ENat := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedAddCommMonoidWithInfima Int := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedAddCommMonoidWithInfima NNRat := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedAddCommMonoidWithInfima Rat := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

noncomputable instance : OrderedAddCommMonoidWithInfima NNReal := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

noncomputable instance : OrderedAddCommMonoidWithInfima ENNReal := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedAddCommMonoidWithInfima Real := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

noncomputable instance : OrderedAddCommMonoidWithInfima EReal := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

noncomputable instance : OrderedAddCommMonoidWithInfima (EReal × EReal) := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

noncomputable instance : OrderedAddCommMonoidWithInfima (Unit × Bool × ENat × NNReal × EReal) := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

/-
We provide `OrderedCancelAddCommMonoidWithInfima` instances for
`Nat`, `Int`, `NNRat`, `Rat`, `NNReal`, `Real`.
Tuples of above-mentioned types get inferred easily, as exemplified below them.
-/

instance : OrderedCancelAddCommMonoidWithInfima Nat := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedCancelAddCommMonoidWithInfima Int := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedCancelAddCommMonoidWithInfima NNRat := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedCancelAddCommMonoidWithInfima Rat := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

noncomputable instance : OrderedCancelAddCommMonoidWithInfima NNReal := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedCancelAddCommMonoidWithInfima Real := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf

instance : OrderedCancelAddCommMonoidWithInfima (Nat × NNRat × Real) := by
  constructor
  · apply inf_le_left
  · apply inf_le_right
  · apply le_inf
