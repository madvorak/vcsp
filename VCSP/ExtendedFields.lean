/-
Inspired by:
https://github.com/leanprover-community/mathlib4/blob/333e2d79fdaee86489af73dee919bc4b66957a52/Mathlib/Data/Real/EReal.lean
-/

import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Field.Basic

noncomputable section


/-- `Extend F` is the type of values in `F ∪ {⊥, ⊤}` where, informally speaking,
    `⊥` (negative infinity) is stronger than `⊤` (positive infinity). -/
def Extend (F : Type*) := WithBot (WithTop F)

variable {F : Type*} [LinearOrderedField F]


-- Henrik Böving helped me with this instance:
instance : LinearOrderedAddCommMonoid (Extend F) :=
  inferInstanceAs (LinearOrderedAddCommMonoid (WithBot (WithTop F)))

-- Henrik Böving helped me with this instance:
instance : AddCommMonoidWithOne (Extend F) :=
  inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop F)))

instance : ZeroLEOneClass (Extend F) := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop F)))

instance : CharZero (Extend F) := inferInstanceAs (CharZero (WithBot (WithTop F)))

instance : BoundedOrder (Extend F) := inferInstanceAs (BoundedOrder (WithBot (WithTop F)))

instance : DenselyOrdered (Extend F) := inferInstanceAs (DenselyOrdered (WithBot (WithTop F)))

instance : DecidableRel ((· < ·) : Extend F → (Extend F) → Prop) := WithBot.decidableLT

/-- The canonical inclusion from `F` to `Extend F` is registered as a coercion. -/
@[coe] def toE : F → (Extend F) := some ∘ some

instance : Coe F (Extend F) := ⟨toE⟩


namespace EF

/-! ### Coercion -/

lemma coe_strictMono : StrictMono (toE (F := F)) :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

lemma coe_injective : Function.Injective (toE (F := F)) :=
  coe_strictMono.injective

@[simp, norm_cast]
lemma coe_le_coe_iff {x y : F} : (x : Extend F) ≤ (y : Extend F) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

lemma coe_le_coe_iff_F (F : Type) [LinearOrderedField F] {x y : F} : (x : Extend F) ≤ (y : Extend F) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[simp, norm_cast]
lemma coe_lt_coe_iff {x y : F} : (x : Extend F) < (y : Extend F) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[simp, norm_cast]
lemma coe_eq_coe_iff {x y : F} : (x : Extend F) = (y : Extend F) ↔ x = y :=
  coe_injective.eq_iff

lemma coe_neq_coe_iff {x y : F} : (x : Extend F) ≠ (y : Extend F) ↔ x ≠ y :=
  coe_injective.ne_iff

@[simp, norm_cast]
lemma coe_zero : ((0 : F) : Extend F) = 0 := rfl

@[simp, norm_cast]
lemma coe_one : ((1 : F) : Extend F) = 1 := rfl

@[simp]
lemma bot_lt_coe (x : F) : (⊥ : Extend F) < x :=
  WithBot.bot_lt_coe _

@[simp]
lemma coe_neq_bot (x : F) : (x : Extend F) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
lemma bot_neq_coe (x : F) : (⊥ : Extend F) ≠ x :=
  (bot_lt_coe x).ne

@[simp]
lemma coe_lt_top (x : F) : (x : Extend F) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
lemma coe_neq_top (x : F) : (x : Extend F) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
lemma top_neq_coe (x : F) : (⊤ : Extend F) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
lemma bot_lt_zero : (⊥ : Extend F) < 0 :=
  bot_lt_coe 0

@[simp]
lemma bot_neq_zero : (⊥ : Extend F) ≠ 0 :=
  (coe_neq_bot 0).symm

@[simp]
lemma zero_neq_bot : (0 : Extend F) ≠ ⊥ :=
  coe_neq_bot 0

@[simp]
lemma zero_lt_top : (0 : Extend F) < ⊤ :=
  coe_lt_top 0

@[simp]
lemma zero_neq_top : (0 : Extend F) ≠ ⊤ :=
  coe_neq_top 0

@[simp]
lemma top_neq_zero : (⊤ : Extend F) ≠ 0 :=
  (coe_neq_top 0).symm

@[simp, norm_cast]
lemma coe_add (x y : F) : toE (x + y) = toE x + toE y :=
  rfl

@[simp, norm_cast]
lemma coe_eq_zero {x : F} : (x : Extend F) = 0 ↔ x = 0 :=
  coe_eq_coe_iff

@[simp, norm_cast]
lemma coe_eq_one {x : F} : (x : Extend F) = 1 ↔ x = 1 :=
  coe_eq_coe_iff

lemma coe_neq_zero {x : F} : (x : Extend F) ≠ 0 ↔ x ≠ 0 :=
  coe_neq_coe_iff

lemma coe_neq_one {x : F} : (x : Extend F) ≠ 1 ↔ x ≠ 1 :=
  coe_neq_coe_iff

@[simp, norm_cast]
lemma coe_nonneg {x : F} : (0 : Extend F) ≤ x ↔ 0 ≤ x :=
  coe_le_coe_iff

@[simp, norm_cast]
lemma coe_nonpos {x : F} : x ≤ (0 : Extend F) ↔ x ≤ 0 :=
  coe_le_coe_iff

@[simp, norm_cast]
lemma coe_pos {x : F} : (0 : Extend F) < x ↔ 0 < x :=
  coe_lt_coe_iff

@[simp, norm_cast]
lemma coe_neg' {x : F} : x < (0 : Extend F) ↔ x < 0 :=
  coe_lt_coe_iff

/-! ### Addition -/

@[simp]
lemma add_bot (x : Extend F) : x + ⊥ = ⊥ :=
  WithBot.add_bot x

@[simp]
lemma bot_add (x : Extend F) : ⊥ + x = ⊥ :=
  WithBot.bot_add x

@[simp]
lemma add_eq_bot_iff {x y : Extend F} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot

@[simp]
lemma top_add_top : (⊤ : Extend F) + ⊤ = ⊤ :=
  rfl

@[simp]
lemma top_add_coe (x : F) : (⊤ : Extend F) + x = ⊤ :=
  rfl

@[simp]
lemma coe_add_top (x : F) : (x : Extend F) + ⊤ = ⊤ :=
  rfl

/-! ### Negation -/

/-- Negation on `Extend F`. -/
def neg : Extend F → (Extend F)
| ⊥ => ⊤
| ⊤ => ⊥
| (x : F) => toE (-x)

instance : Neg (Extend F) := ⟨EF.neg⟩

instance : SubNegZeroMonoid (Extend F) where
  neg_zero := congr_arg toE neg_zero
  zsmul := zsmulRec

@[simp]
lemma neg_top : -(⊤ : Extend F) = ⊥ :=
  rfl

@[simp]
lemma neg_bot : -(⊥ : Extend F) = ⊤ :=
  rfl

@[simp, norm_cast]
lemma coe_neg (x : F) : toE (-x) = -(toE x) := rfl

instance : InvolutiveNeg (Extend F) where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : F) => congr_arg toE (neg_neg a)

@[simp]
lemma neg_eq_top_iff {x : Extend F} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
lemma neg_eq_bot_iff {x : Extend F} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
lemma neg_eq_zero_iff {x : Extend F} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero

end EF
