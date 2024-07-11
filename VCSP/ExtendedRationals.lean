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

/-- The canonical inclusion from `Rat`s to `ERat`s. Registered as a coercion. -/
@[coe] def Rat.toERat : ℚ → ERat := some ∘ some


namespace ERat

instance decidableLT : DecidableRel ((· < ·) : ERat → ERat → Prop) :=
  WithBot.decidableLT

instance : Coe ℚ ERat := ⟨Rat.toERat⟩

lemma coe_strictMono : StrictMono Rat.toERat :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

lemma coe_injective : Injective Rat.toERat :=
  coe_strictMono.injective

@[simp, norm_cast]
protected lemma coe_le_coe_iff {x y : ℚ} : (x : ERat) ≤ (y : ERat) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[simp, norm_cast]
protected lemma coe_lt_coe_iff {x y : ℚ} : (x : ERat) < (y : ERat) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[simp, norm_cast]
protected lemma coe_eq_coe_iff {x y : ℚ} : (x : ERat) = (y : ERat) ↔ x = y :=
  coe_injective.eq_iff

protected lemma coe_ne_coe_iff {x y : ℚ} : (x : ERat) ≠ (y : ERat) ↔ x ≠ y :=
  coe_injective.ne_iff

@[simp, norm_cast]
lemma coe_zero : ((0 : ℚ) : ERat) = 0 := rfl

@[simp, norm_cast]
lemma coe_one : ((1 : ℚ) : ERat) = 1 := rfl

-- @[elab_as_elim]
-- protected def rec {C : ERat → Sort*} (hbot : C ⊥) (hcoe : ∀ a : ℚ, C a) (htop : C ⊤) : ∀ a : ERat, C a
--   | ⊥ => hbot
--   | (a : ℚ) => hcoe a
--   | ⊤ => htop

/-! ### Rat coercion -/

instance canLift : CanLift ERat ℚ Rat.toERat fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    match x with
    | ⊥ => simp at hx
    | ⊤ => simp at hx
    | (q : ℚ) => simp

/-- The map from `ERat`s to `Rat`s sending infinities to zero. -/
def toRat : ERat → ℚ
| ⊥ => 0
| ⊤ => 0
| (q : ℚ) => q

@[simp]
lemma toRat_top : toRat ⊤ = 0 :=
  rfl

@[simp]
lemma toRat_bot : toRat ⊥ = 0 :=
  rfl

@[simp]
lemma toRat_zero : toRat 0 = 0 :=
  rfl

@[simp]
lemma toRat_one : toRat 1 = 1 :=
  rfl

@[simp]
lemma toRat_coe (x : ℚ) : toRat (x : ERat) = x :=
  rfl

@[simp]
lemma bot_lt_coe (x : ℚ) : (⊥ : ERat) < x :=
  WithBot.bot_lt_coe _

@[simp]
lemma coe_ne_bot (x : ℚ) : (x : ERat) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
lemma bot_ne_coe (x : ℚ) : (⊥ : ERat) ≠ x :=
  (bot_lt_coe x).ne

@[simp]
lemma coe_lt_top (x : ℚ) : (x : ERat) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
lemma coe_ne_top (x : ℚ) : (x : ERat) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
lemma top_ne_coe (x : ℚ) : (⊤ : ERat) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
lemma bot_lt_zero : (⊥ : ERat) < 0 :=
  bot_lt_coe 0

@[simp]
lemma bot_ne_zero : (⊥ : ERat) ≠ 0 :=
  (coe_ne_bot 0).symm

@[simp]
lemma zero_ne_bot : (0 : ERat) ≠ ⊥ :=
  coe_ne_bot 0

@[simp]
lemma zero_lt_top : (0 : ERat) < ⊤ :=
  coe_lt_top 0

@[simp]
lemma zero_ne_top : (0 : ERat) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
lemma top_ne_zero : (⊤ : ERat) ≠ 0 :=
  (coe_ne_top 0).symm

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

lemma coe_ne_zero {x : ℚ} : (x : ERat) ≠ 0 ↔ x ≠ 0 :=
  ERat.coe_ne_coe_iff

lemma coe_ne_one {x : ℚ} : (x : ERat) ≠ 1 ↔ x ≠ 1 :=
  ERat.coe_ne_coe_iff

@[simp, norm_cast]
protected lemma coe_nonneg {x : ℚ} : (0 : ERat) ≤ x ↔ 0 ≤ x :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
protected lemma coe_nonpos {x : ℚ} : x ≤ (0 : ERat) ↔ x ≤ 0 :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
protected lemma coe_pos {x : ℚ} : (0 : ERat) < x ↔ 0 < x :=
  ERat.coe_lt_coe_iff

@[simp, norm_cast]
protected lemma coe_neg' {x : ℚ} : x < (0 : ERat) ↔ x < 0 :=
  ERat.coe_lt_coe_iff

lemma toRat_le_toRat {x y : ERat} (hxy : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toRat ≤ y.toRat := by
  lift x to ℚ using ⟨ne_top_of_le_ne_top hy hxy, hx⟩
  lift y to ℚ using ⟨hy, ne_bot_of_le_ne_bot hx hxy⟩
  simpa using hxy

lemma coe_toRat {x : ERat} (x_neq_top : x ≠ ⊤) (x_neq_bot : x ≠ ⊥) : x.toRat.toERat = x := by
  lift x to ℚ using ⟨x_neq_top, x_neq_bot⟩
  rfl

lemma le_coe_toRat {x : ERat} (hx : x ≠ ⊤) : x ≤ x.toRat.toERat := by
  by_cases hbot : x = ⊥
  · rw [hbot, toRat_bot, coe_zero]
    decide
  · simp only [le_refl, coe_toRat hx hbot]

lemma coe_toRat_le {x : ERat} (hx : x ≠ ⊥) : x.toRat.toERat ≤ x := by
  by_cases htop : x = ⊤
  · rw [htop, toRat_top, coe_zero]
    decide
  · simp only [le_refl, coe_toRat htop hx]

lemma eq_top_iff_forall_lt (x : ERat) : x = ⊤ ↔ ∀ y : ℚ, (y : ERat) < x := by
  constructor
  · rintro rfl
    exact ERat.coe_lt_top
  · contrapose!
    intro hx
    exact ⟨x.toRat, le_coe_toRat hx⟩

lemma eq_bot_iff_forall_lt (x : ERat) : x = ⊥ ↔ ∀ y : ℚ, x < (y : ERat) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro hx
    exact ⟨x.toRat, coe_toRat_le hx⟩

lemma exists_between_coe_Rat {x z : ERat} (hxz : x < z) : ∃ y : ℚ, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between hxz
  match a with
  | ⊥ => exact (not_lt_bot ha₁).elim
  | ⊤ => exact (not_top_lt ha₂).elim
  | (a₀ : ℚ) => exact ⟨a₀, by exact_mod_cast ha₁, by exact_mod_cast ha₂⟩

/-! ### Order -/

/-- The set of numbers in `ERat` that are not `⊥, ⊤` is equivalent to `ℚ`. -/
def neTopBotEquivRat : ({⊥, ⊤}ᶜ : Set ERat) ≃ ℚ where
  toFun x := ERat.toRat x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
    lift x to ℚ
    · simpa [not_or, and_comm] using hx
    · simp
  right_inv x := by simp

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

lemma toRat_add {x y : ERat} (x_neq_top : x ≠ ⊤) (x_neq_bot : x ≠ ⊥) (y_neq_top : y ≠ ⊤) (y_neq_bot : y ≠ ⊥) :
    toRat (x + y) = toRat x + toRat y := by
  lift x to ℚ using ⟨x_neq_top, x_neq_bot⟩
  lift y to ℚ using ⟨y_neq_top, y_neq_bot⟩
  rfl

/-! ### Negation -/

/-- Negation on `ERat`. -/
protected def neg : ERat → ERat
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

@[norm_cast]
lemma coe_zsmul (n : ℤ) (x : ℚ) : (n • x).toERat = n • x.toERat :=
  map_zsmul' (⟨⟨Rat.toERat, coe_zero⟩, coe_add⟩ : ℚ →+ ERat) coe_neg _ _

instance : InvolutiveNeg ERat where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℚ) => congr_arg Rat.toERat (neg_neg a)

@[simp]
lemma toRat_neg : ∀ {a : ERat}, toRat (-a) = -toRat a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℚ) => rfl

@[simp]
lemma neg_eq_top_iff {x : ERat} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
lemma neg_eq_bot_iff {x : ERat} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
lemma neg_eq_zero_iff {x : ERat} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero

lemma neg_strictAnti : StrictAnti (- · : ERat → ERat) :=
  WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨compare_gt_iff_gt.mp rfl, fun _ => coe_lt_top _⟩⟩

@[simp] lemma neg_le_neg_iff {a b : ERat} : -a ≤ -b ↔ b ≤ a := neg_strictAnti.le_iff_le

@[simp] lemma neg_lt_neg_iff {a b : ERat} : -a < -b ↔ b < a := neg_strictAnti.lt_iff_lt

protected lemma neg_le {a b : ERat} : -a ≤ b ↔ -b ≤ a := by
  rw [←neg_le_neg_iff, neg_neg]

end ERat
