import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.NNRat.Lemmas


def ENNRat : Type := WithTop NNRat deriving
  Inhabited, Nontrivial, WellFoundedRelation,
  CanonicallyLinearOrderedAddCommMonoid, LinearOrderedAddCommMonoidWithTop,
  CanonicallyOrderedCommSemiring

instance : CharZero ENNRat := inferInstanceAs (CharZero (WithTop NNRat))

instance : BoundedOrder ENNRat := inferInstanceAs (BoundedOrder (WithTop NNRat))

instance : DenselyOrdered ENNRat := inferInstanceAs (DenselyOrdered (WithTop NNRat))

instance : Inv ENNRat where
  inv (a : ENNRat) :=
    match a with
    | ⊤ => 0
    | 0 => ⊤
    | some a => some a⁻¹

notation "ℚ≥0∞" => ENNRat
