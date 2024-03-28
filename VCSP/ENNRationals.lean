import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.Rat.Order
import Mathlib.Data.NNRat.Lemmas

open scoped NNRat


def ENNRat : Type := WithTop ℚ≥0 deriving
  Nontrivial, Inhabited, WellFoundedRelation, CanonicallyLinearOrderedAddCommMonoid, LinearOrderedAddCommMonoidWithTop

notation "ℚ∞" => ENNRat

def mulENNRat : ℚ∞ → ℚ∞ → ℚ∞
| some 0, _      => some 0
| _     , some 0 => some 0
| ⊤     , _      => ⊤
| _     , ⊤      => ⊤
| some a, some b => some (a * b)

def oneENNRat : ℚ∞ := some 1

lemma oneENNRat_mulENNRat (x : ℚ∞) : mulENNRat oneENNRat x = x := by
  unfold oneENNRat
  unfold mulENNRat
  split
  · exfalso
    simp at *
    have impos : (1 : ℚ≥0) = (0 : ℚ≥0) := by
      assumption
    exact one_ne_zero impos
  · simp
    rfl
  · contradiction
  · tauto
  · aesop

lemma mulENNRat_oneENNRat (x : ℚ∞) : mulENNRat x oneENNRat = x := by
  unfold oneENNRat
  unfold mulENNRat
  split
  · simp
    rfl
  · exfalso
    simp at *
    have impos : (1 : ℚ≥0) = (0 : ℚ≥0) := by
      assumption
    exact one_ne_zero impos
  · tauto
  · contradiction
  · aesop

lemma zeroENNRat_mulENNRat (x : ℚ∞) : mulENNRat (0 : ℚ∞) x = (0 : ℚ∞) := by
  unfold mulENNRat
  split
  · rfl
  · rfl
  · contradiction
  · contradiction
  · sorry

lemma mulENNRat_zeroENNRat (x : ℚ∞) : mulENNRat x (0 : ℚ∞) = (0 : ℚ∞) := by
  unfold mulENNRat
  split
  · rfl
  · rfl
  · contradiction
  · contradiction
  · sorry

lemma mulENNRat_assoc (x y z : ℚ∞) : mulENNRat (mulENNRat x y) z = mulENNRat x (mulENNRat y z) := by
  unfold mulENNRat
  sorry

lemma mulENNRat_left_distrib (x y z : ℚ∞) : mulENNRat x (y + z) = mulENNRat x y + mulENNRat x z := by
  unfold mulENNRat
  split
  · rfl
  · sorry
  · sorry
  · sorry
  · sorry

lemma mulENNRat_right_distrib (x y z : ℚ∞) : mulENNRat (x + y) z = mulENNRat x z + mulENNRat y z := by
  unfold mulENNRat
  sorry

lemma mulENNRat_comm (x y : ℚ∞) : mulENNRat x y = mulENNRat y x := by
  unfold mulENNRat
  split
  · aesop
  · aesop
  · aesop
  · aesop
  · rw [mul_comm]

lemma addENNRat_le_addENNRat_left (x y : ℚ∞) (hxy : x ≤ y) (z : ℚ∞) : z + x ≤ z + y := by
  sorry

lemma zeroENNRat_le_oneENNRat : (0 : ℚ∞) ≤ oneENNRat := by
  sorry

lemma mulENNRat_le_mulENNRat_of_nonneg_left (x y z : ℚ∞) : x ≤ y → 0 ≤ z → mulENNRat z x ≤ mulENNRat z y := by
  unfold mulENNRat
  sorry

lemma mulENNRat_le_mulENNRat_of_nonneg_right (x y z : ℚ∞) : x ≤ y → 0 ≤ z → mulENNRat x z ≤ mulENNRat y z := by
  unfold mulENNRat
  sorry

instance : OrderedCommSemiring ℚ∞ where
  mul := mulENNRat
  one := oneENNRat
  one_mul := oneENNRat_mulENNRat
  mul_one := mulENNRat_oneENNRat
  zero_mul := zeroENNRat_mulENNRat
  mul_zero := mulENNRat_zeroENNRat
  mul_assoc := mulENNRat_assoc
  left_distrib := mulENNRat_left_distrib
  right_distrib := mulENNRat_right_distrib
  mul_comm := mulENNRat_comm
  add_le_add_left := addENNRat_le_addENNRat_left
  zero_le_one := zeroENNRat_le_oneENNRat
  mul_le_mul_of_nonneg_left := mulENNRat_le_mulENNRat_of_nonneg_left
  mul_le_mul_of_nonneg_right := mulENNRat_le_mulENNRat_of_nonneg_right
