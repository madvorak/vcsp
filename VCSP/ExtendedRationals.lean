/-
Adapted from:
https://github.com/leanprover-community/mathlib4/blob/333e2d79fdaee86489af73dee919bc4b66957a52/Mathlib/Data/Real/EReal.lean

Released under Apache 2.0 license.
Authors: Kevin Buzzard
-/

import Mathlib.Data.Real.EReal

open Function Set

noncomputable section


/-- `ERat` is the type of extended rationals `[-∞, +∞]` or rather `ℚ ∪ {⊥, ⊤}` where, informally speaking,
    `⊥` (negative infinity) is stronger than `⊤` (positive infinity). -/
def ERat := WithBot (WithTop ℚ) deriving LinearOrderedAddCommMonoid, AddCommMonoidWithOne

instance : ZeroLEOneClass ERat := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop ℚ)))

instance : CharZero ERat := inferInstanceAs (CharZero (WithBot (WithTop ℚ)))

instance : BoundedOrder ERat := inferInstanceAs (BoundedOrder (WithBot (WithTop ℚ)))

instance : DenselyOrdered ERat := inferInstanceAs (DenselyOrdered (WithBot (WithTop ℚ)))

instance : DecidableRel ((· < ·) : ERat → ERat → Prop) := WithBot.decidableLT

/-- The canonical inclusion from `Rat`s to `ERat`s. Registered as a coercion. -/
@[coe] def Rat.toERat : ℚ → ERat := some ∘ some

instance : Coe ℚ ERat := ⟨Rat.toERat⟩


namespace ERat

/-! ### Coercion -/

lemma coe_strictMono : StrictMono Rat.toERat :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

lemma coe_injective : Injective Rat.toERat :=
  coe_strictMono.injective

@[simp, norm_cast]
lemma coe_le_coe_iff {x y : ℚ} : (x : ERat) ≤ (y : ERat) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[simp, norm_cast]
lemma coe_lt_coe_iff {x y : ℚ} : (x : ERat) < (y : ERat) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[simp, norm_cast]
lemma coe_eq_coe_iff {x y : ℚ} : (x : ERat) = (y : ERat) ↔ x = y :=
  coe_injective.eq_iff

lemma coe_neq_coe_iff {x y : ℚ} : (x : ERat) ≠ (y : ERat) ↔ x ≠ y :=
  coe_injective.ne_iff

@[simp, norm_cast]
lemma coe_zero : ((0 : ℚ) : ERat) = 0 := rfl

@[simp, norm_cast]
lemma coe_one : ((1 : ℚ) : ERat) = 1 := rfl

@[simp]
lemma bot_lt_coe (x : ℚ) : (⊥ : ERat) < x :=
  WithBot.bot_lt_coe _

@[simp]
lemma coe_neq_bot (x : ℚ) : (x : ERat) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
lemma bot_neq_coe (x : ℚ) : (⊥ : ERat) ≠ x :=
  (bot_lt_coe x).ne

@[simp]
lemma coe_lt_top (x : ℚ) : (x : ERat) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
lemma coe_neq_top (x : ℚ) : (x : ERat) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
lemma top_neq_coe (x : ℚ) : (⊤ : ERat) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
lemma bot_lt_zero : (⊥ : ERat) < 0 :=
  bot_lt_coe 0

@[simp]
lemma bot_neq_zero : (⊥ : ERat) ≠ 0 :=
  (coe_neq_bot 0).symm

@[simp]
lemma zero_neq_bot : (0 : ERat) ≠ ⊥ :=
  coe_neq_bot 0

@[simp]
lemma zero_lt_top : (0 : ERat) < ⊤ :=
  coe_lt_top 0

@[simp]
lemma zero_neq_top : (0 : ERat) ≠ ⊤ :=
  coe_neq_top 0

@[simp]
lemma top_neq_zero : (⊤ : ERat) ≠ 0 :=
  (coe_neq_top 0).symm

@[simp, norm_cast]
lemma coe_add (x y : ℚ) : (x + y).toERat = x.toERat + y.toERat :=
  rfl

@[norm_cast]
lemma coe_nsmul (n : ℕ) (x : ℚ) : (n • x).toERat = n • x.toERat :=
  map_nsmul (⟨⟨Rat.toERat, coe_zero⟩, coe_add⟩ : ℚ →+ ERat) _ _

@[simp, norm_cast]
lemma coe_eq_zero {x : ℚ} : (x : ERat) = 0 ↔ x = 0 :=
  ERat.coe_eq_coe_iff

@[simp, norm_cast]
lemma coe_eq_one {x : ℚ} : (x : ERat) = 1 ↔ x = 1 :=
  ERat.coe_eq_coe_iff

lemma coe_neq_zero {x : ℚ} : (x : ERat) ≠ 0 ↔ x ≠ 0 :=
  ERat.coe_neq_coe_iff

lemma coe_neq_one {x : ℚ} : (x : ERat) ≠ 1 ↔ x ≠ 1 :=
  ERat.coe_neq_coe_iff

@[simp, norm_cast]
lemma coe_nonneg {x : ℚ} : (0 : ERat) ≤ x ↔ 0 ≤ x :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
lemma coe_nonpos {x : ℚ} : x ≤ (0 : ERat) ↔ x ≤ 0 :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
lemma coe_pos {x : ℚ} : (0 : ERat) < x ↔ 0 < x :=
  ERat.coe_lt_coe_iff

@[simp, norm_cast]
lemma coe_neg' {x : ℚ} : x < (0 : ERat) ↔ x < 0 :=
  ERat.coe_lt_coe_iff

/-! ### Addition -/

@[simp]
lemma add_bot (x : ERat) : x + ⊥ = ⊥ :=
  WithBot.add_bot x

@[simp]
lemma bot_add (x : ERat) : ⊥ + x = ⊥ :=
  WithBot.bot_add x

@[simp]
lemma add_eq_bot_iff {x y : ERat} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot

@[simp]
lemma top_add_top : (⊤ : ERat) + ⊤ = ⊤ :=
  rfl

@[simp]
lemma top_add_coe (x : ℚ) : (⊤ : ERat) + x = ⊤ :=
  rfl

@[simp]
lemma coe_add_top (x : ℚ) : (x : ERat) + ⊤ = ⊤ :=
  rfl

/-! ### Negation -/

/-- Negation on `ERat`. -/
def neg : ERat → ERat
| ⊥ => ⊤
| ⊤ => ⊥
| (x : ℚ) => (-x : ℚ)

instance : Neg ERat := ⟨ERat.neg⟩

instance : SubNegZeroMonoid ERat where
  neg_zero := congr_arg Rat.toERat neg_zero
  zsmul := zsmulRec

@[simp]
lemma neg_top : -(⊤ : ERat) = ⊥ :=
  rfl

@[simp]
lemma neg_bot : -(⊥ : ERat) = ⊤ :=
  rfl

@[simp, norm_cast] lemma coe_neg (x : ℚ) : (-x).toERat = - x.toERat := rfl

instance : InvolutiveNeg ERat where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℚ) => congr_arg Rat.toERat (neg_neg a)

@[simp]
lemma neg_eq_top_iff {x : ERat} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
lemma neg_eq_bot_iff {x : ERat} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
lemma neg_eq_zero_iff {x : ERat} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero

end ERat
