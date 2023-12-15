import Mathlib.Data.Fintype.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Real.EReal
import VCSP.AlgebraC

/-
We provide `OrderedAddCommMonoidWithInfima` instances for `ENat`, `ENNReal`, `EReal`, and
hopefully soon for `Bool` ("upside down") as well.
Tuples of above-mentioned types get inferred easily, as exemplified on the bottom.
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
  · apply sInf_le
  · apply le_sInf

noncomputable example : OrderedAddCommMonoidWithInfima Nat := by
  constructor
  · apply csInf_le'
  · sorry -- cannot be

noncomputable instance : OrderedAddCommMonoidWithInfima ENat := by
  constructor
  · apply sInf_le
  · apply le_sInf

noncomputable example : OrderedAddCommMonoidWithInfima NNReal := by
  constructor
  · apply csInf_le'
  · sorry -- cannot be

noncomputable instance : OrderedAddCommMonoidWithInfima ENNReal := by
  constructor
  · apply sInf_le
  · apply le_sInf

noncomputable instance : OrderedAddCommMonoidWithInfima EReal := by
  constructor
  · apply sInf_le
  · apply le_sInf

noncomputable instance : OrderedAddCommMonoidWithInfima (EReal × EReal) := by
  constructor
  · apply sInf_le
  · apply le_sInf

noncomputable instance : OrderedAddCommMonoidWithInfima (Unit × Bool × ENat × ENNReal × EReal) := by
  constructor
  · apply sInf_le
  · apply le_sInf


-----------------------------------------------------------------------------------------


theorem fuck {α : Type*} [OrderedCancelAddCommMonoidWithInfima α] :
    (∃ x y : α, x < y) → False := by

  rintro ⟨x, y, hxy⟩

  --    ⊥ ≤ ⊥ + x
  have blebpx : @sInf α _ Set.univ ≤ @sInf α _ Set.univ + x
  · exact sInf_le trivial

  --    ⊥ + x < ⊥ + y
  have bpxlbpy : @sInf α _ Set.univ + x < @sInf α _ Set.univ + y
  · exact add_lt_add_left hxy (sInf Set.univ)

  --    ⊥ < ⊥ + y
  have blbpy : @sInf α _ Set.univ < @sInf α _ Set.univ + y
  · exact blebpx.trans_lt bpxlbpy

  --    0 < y
  have zly : 0 < y
  · exact pos_of_lt_add_right blbpy

  --    ⊤ + y ≤ ⊤
  have tpylet : @sInf α _ ∅ + y ≤ @sInf α _ ∅
  · simp

  --    ⊤ + y < ⊤ + y
  have tpyltpy : @sInf α _ ∅ + y < @sInf α _ ∅ + y
  · exact lt_add_of_le_of_pos tpylet zly

  --    contradiction
  exact tpyltpy.false


#check fuck
#print axioms fuck
