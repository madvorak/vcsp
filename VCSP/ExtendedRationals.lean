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

instance : BoundedOrder ERat := inferInstanceAs (BoundedOrder (WithBot (WithTop ℚ)))

instance : DenselyOrdered ERat := inferInstanceAs (DenselyOrdered (WithBot (WithTop ℚ)))

instance : CharZero ERat := inferInstanceAs (CharZero (WithBot (WithTop ℚ)))

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

@[elab_as_elim]
protected def rec {C : ERat → Sort*} (h_bot : C ⊥) (h_Rat : ∀ a : ℚ, C a) (h_top : C ⊤) : ∀ a : ERat, C a
  | ⊥ => h_bot
  | (a : ℚ) => h_Rat a
  | ⊤ => h_top

/-- The multiplication on `ERat`. -/
protected def mul : ERat → ERat → ERat
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊥, (y : ℚ) => if 0 ≤ y then ⊥ else ⊤
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | ⊤, (y : ℚ) => if 0 < y then ⊤ else if y = 0 then 0 else ⊥
  | (x : ℚ), ⊤ => if 0 < x then ⊤ else if x = 0 then 0 else ⊥
  | (x : ℚ), ⊥ => if 0 ≤ x then ⊥ else ⊤
  | (x : ℚ), (y : ℚ) => (x * y : ℚ)

instance : Mul ERat := ⟨ERat.mul⟩

@[simp, norm_cast]
lemma coe_mul (x y : ℚ) : (↑(x * y) : ERat) = x * y :=
  rfl

/-- Induct on two `ERat`s by performing case splits on the sign of one whenever the other is infinite. -/
@[elab_as_elim]
lemma induction₂ {P : ERat → ERat → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℚ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : ∀ x : ℚ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℚ, 0 < x → P x ⊥) (zero_top : P 0 ⊤)
    (coe_coe : ∀ x y : ℚ, P x y) (zero_bot : P 0 ⊥) (neg_top : ∀ x : ℚ, x < 0 → P x ⊤)
    (neg_bot : ∀ x : ℚ, x < 0 → P x ⊥) (bot_top : P ⊥ ⊤) (bot_pos : ∀ x : ℚ, 0 < x → P ⊥ x)
    (bot_zero : P ⊥ 0) (bot_neg : ∀ x : ℚ, x < 0 → P ⊥ x) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : ℚ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [bot_neg y hy, bot_zero, bot_pos y hy]
  | ⊥, ⊤ => bot_top
  | (x : ℚ), ⊥ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_bot x hx, zero_bot, pos_bot x hx]
  | (x : ℚ), (y : ℚ) => coe_coe _ _
  | (x : ℚ), ⊤ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : ℚ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `ERat`s by performing case splits on the sign of one whenever the other is infinite.
    This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
lemma induction₂_symm {P : ERat → ERat → Prop} (symm : ∀ {x y}, P x y → P y x)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : ℚ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥) (pos_bot : ∀ x : ℚ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℚ, P x y) (zero_bot : P 0 ⊥) (neg_bot : ∀ x : ℚ, x < 0 → P x ⊥)
    (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
  @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

protected lemma mul_comm (x y : ERat) : x * y = y * x := by
  induction' x using ERat.rec with x <;> induction' y using ERat.rec with y <;>
    try { rfl }
  rw [←coe_mul, ←coe_mul, mul_comm]

protected lemma one_mul : ∀ x : ERat, 1 * x = x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℚ) => congr_arg Rat.toERat (one_mul x)

lemma zero_mul {x : ERat} (hx : x ≠ ⊥) : 0 * x = 0 :=
  match x with
  | ⊤ => rfl
  | ⊥ => False.elim (hx rfl)
  | (x : ℚ) => congr_arg Rat.toERat (Rat.zero_mul x)

/-! ### Rat coercion -/

instance canLift : CanLift ERat ℚ (↑) fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    induction x using ERat.rec
    · simp at hx
    · simp
    · simp at hx

/-- The map from `ERat`s to `Rat`s sending infinities to zero. -/
def toRat : ERat → ℚ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℚ) => x

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

lemma range_coe : range Rat.toERat = {⊥, ⊤}ᶜ := by
  ext x
  induction x using ERat.rec <;> simp

lemma range_coe_eq_Ioo : range Rat.toERat = Ioo ⊥ ⊤ := by
  ext x
  induction x using ERat.rec <;> simp

@[simp, norm_cast]
lemma coe_add (x y : ℚ) : (x + y).toERat = x.toERat + y.toERat :=
  rfl

@[norm_cast]
lemma coe_nsmul (n : ℕ) (x : ℚ) : (↑(n • x) : ERat) = n • (x : ERat) :=
  map_nsmul (⟨⟨Rat.toERat, coe_zero⟩, coe_add⟩ : ℚ →+ ERat) _ _

#noalign ERat.coe_bit0
#noalign ERat.coe_bit1

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
protected lemma coe_nonpos {x : ℚ} : (x : ERat) ≤ 0 ↔ x ≤ 0 :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
protected lemma coe_pos {x : ℚ} : (0 : ERat) < x ↔ 0 < x :=
  ERat.coe_lt_coe_iff

@[simp, norm_cast]
protected lemma coe_neg' {x : ℚ} : (x : ERat) < 0 ↔ x < 0 :=
  ERat.coe_lt_coe_iff

lemma toRat_le_toRat {x y : ERat} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toRat ≤ y.toRat := by
  lift x to ℚ using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to ℚ using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h

lemma coe_toRat {x : ERat} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toRat : ERat) = x := by
  lift x to ℚ using ⟨hx, h'x⟩
  rfl

lemma le_coe_toRat {x : ERat} (h : x ≠ ⊤) : x ≤ x.toRat := by
  by_cases h' : x = ⊥
  · rw [h', toRat_bot, coe_zero]
    decide
  · simp only [le_refl, coe_toRat h h']

lemma coe_toRat_le {x : ERat} (h : x ≠ ⊥) : ↑x.toRat ≤ x := by
  by_cases h' : x = ⊤
  · rw [h', toRat_top, coe_zero]
    decide
  · simp only [le_refl, coe_toRat h' h]

lemma eq_top_iff_forall_lt (x : ERat) : x = ⊤ ↔ ∀ y : ℚ, (y : ERat) < x := by
  constructor
  · rintro rfl
    exact ERat.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toRat, le_coe_toRat h⟩

lemma eq_bot_iff_forall_lt (x : ERat) : x = ⊥ ↔ ∀ y : ℚ, x < (y : ERat) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toRat, coe_toRat_le h⟩

lemma exists_between_coe_Rat {x z : ERat} (h : x < z) : ∃ y : ℚ, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction' a using ERat.rec with a₀
  · exact (not_lt_bot ha₁).elim
  · exact ⟨a₀, by exact_mod_cast ha₁, by exact_mod_cast ha₂⟩
  · exact (not_top_lt ha₂).elim

@[simp]
lemma image_coe_Icc (x y : ℚ) : Rat.toERat '' Icc x y = Icc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc, WithBot.image_coe_Icc]
  rfl

@[simp]
lemma image_coe_Ico (x y : ℚ) : Rat.toERat '' Ico x y = Ico ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico, WithBot.image_coe_Ico]
  rfl

@[simp]
lemma image_coe_Ici (x : ℚ) : Rat.toERat '' Ici x = Ico ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici, WithBot.image_coe_Ico]
  rfl

@[simp]
lemma image_coe_Ioc (x y : ℚ) : Rat.toERat '' Ioc x y = Ioc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc, WithBot.image_coe_Ioc]
  rfl

@[simp]
lemma image_coe_Ioo (x y : ℚ) : Rat.toERat '' Ioo x y = Ioo ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo, WithBot.image_coe_Ioo]
  rfl

@[simp]
lemma image_coe_Ioi (x : ℚ) : Rat.toERat '' Ioi x = Ioo ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi, WithBot.image_coe_Ioo]
  rfl

@[simp]
lemma image_coe_Iic (x : ℚ) : Rat.toERat '' Iic x = Ioc ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic, WithBot.image_coe_Iic]
  rfl

@[simp]
lemma image_coe_Iio (x : ℚ) : Rat.toERat '' Iio x = Ioo ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio, WithBot.image_coe_Iio]
  rfl

@[simp]
lemma preimage_coe_Ici (x : ℚ) : Rat.toERat ⁻¹' Ici x = Ici x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ici (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ici, WithTop.preimage_coe_Ici]

@[simp]
lemma preimage_coe_Ioi (x : ℚ) : Rat.toERat ⁻¹' Ioi x = Ioi x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi, WithTop.preimage_coe_Ioi]

@[simp]
lemma preimage_coe_Ioi_bot : Rat.toERat ⁻¹' Ioi ⊥ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi ⊥) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi_bot, preimage_univ]

@[simp]
lemma preimage_coe_Iic (y : ℚ) : Rat.toERat ⁻¹' Iic y = Iic y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iic (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iic, WithTop.preimage_coe_Iic]

@[simp]
lemma preimage_coe_Iio (y : ℚ) : Rat.toERat ⁻¹' Iio y = Iio y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio]

@[simp]
lemma preimage_coe_Iio_top : Rat.toERat ⁻¹' Iio ⊤ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some ⊤)) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio_top]

@[simp]
lemma preimage_coe_Icc (x y : ℚ) : Rat.toERat ⁻¹' Icc x y = Icc x y := by
  simp_rw [←Ici_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ico (x y : ℚ) : Rat.toERat ⁻¹' Ico x y = Ico x y := by
  simp_rw [←Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc (x y : ℚ) : Rat.toERat ⁻¹' Ioc x y = Ioc x y := by
  simp_rw [←Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo (x y : ℚ) : Rat.toERat ⁻¹' Ioo x y = Ioo x y := by
  simp_rw [←Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ico_top (x : ℚ) : Rat.toERat ⁻¹' Ico x ⊤ = Ici x := by
  rw [←Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_top (x : ℚ) : Rat.toERat ⁻¹' Ioo x ⊤ = Ioi x := by
  rw [←Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc_bot (y : ℚ) : Rat.toERat ⁻¹' Ioc ⊥ y = Iic y := by
  rw [←Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo_bot (y : ℚ) : Rat.toERat ⁻¹' Ioo ⊥ y = Iio y := by
  rw [←Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_bot_top : Rat.toERat ⁻¹' Ioo ⊥ ⊤ = univ := by
  rw [←Ioi_inter_Iio]
  simp

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
  WithBot.add_bot _

@[simp]
lemma bot_add (x : ERat) : ⊥ + x = ⊥ :=
  WithBot.bot_add _

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

lemma toRat_add {x y : ERat} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toRat (x + y) = toRat x + toRat y := by
  lift x to ℚ using ⟨hx, h'x⟩
  lift y to ℚ using ⟨hy, h'y⟩
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

@[simp, norm_cast] lemma coe_neg (x : ℚ) : (↑(-x) : ERat) = -↑x := rfl

@[norm_cast]
lemma coe_zsmul (n : ℤ) (x : ℚ) : (↑(n • x) : ERat) = n • (x : ERat) :=
  map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : ℚ →+ ERat) coe_neg _ _

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

/-!
### Subtraction

Subtraction on `ERat` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `ERat`, beyond `SubNegZeroMonoid`, because of this bad behavior.
-/

@[simp]
lemma bot_sub (x : ERat) : ⊥ - x = ⊥ :=
  bot_add x

@[simp]
lemma sub_top (x : ERat) : x - ⊤ = ⊥ :=
  add_bot x

@[simp]
lemma top_sub_bot : (⊤ : ERat) - ⊥ = ⊤ :=
  rfl

@[simp]
lemma top_sub_coe (x : ℚ) : (⊤ : ERat) - x = ⊤ :=
  rfl

@[simp]
lemma coe_sub_bot (x : ℚ) : (x : ERat) - ⊥ = ⊤ :=
  rfl

/-! ### Multiplication -/

@[simp] lemma top_mul_top : (⊤ : ERat) * ⊤ = ⊤ := rfl

@[simp] lemma top_mul_bot : (⊤ : ERat) * ⊥ = ⊥ := rfl

@[simp] lemma bot_mul_top : (⊥ : ERat) * ⊤ = ⊥ := rfl

@[simp] lemma bot_mul_bot : (⊥ : ERat) * ⊥ = ⊤ := rfl

lemma coe_mul_top_of_pos {x : ℚ} (h : 0 < x) : (x : ERat) * ⊤ = ⊤ :=
  if_pos h

lemma top_mul_coe_of_pos {x : ℚ} (h : 0 < x) : (⊤ : ERat) * x = ⊤ :=
  if_pos h

lemma coe_mul_bot_of_nneg {x : ℚ} (h : 0 ≤ x) : (x : ERat) * ⊥ = ⊥ :=
  if_pos h

lemma bot_mul_coe_of_nneg {x : ℚ} (h : 0 ≤ x) : (⊥ : ERat) * x = ⊥ :=
  if_pos h

lemma coe_mul_top_of_neg {x : ℚ} (h : x < 0) : (x : ERat) * ⊤ = ⊥ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

lemma top_mul_coe_of_neg {x : ℚ} (h : x < 0) : (⊤ : ERat) * x = ⊥ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

lemma coe_mul_bot_of_neg {x : ℚ} (h : x < 0) : (x : ERat) * ⊥ = ⊤ := by
  apply if_neg
  intro cont
  exact (h.trans_le cont).false

/-- Induct on two `ERat`s by performing case splits on the sign of one whenever the other is infinite.
    This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for all `x` and `y`. -/
@[elab_as_elim]
lemma induction₂_neg_left {P : ERat → ERat → Prop} (neg_left : ∀ {x y}, P x y → P (-x) y)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℚ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (zero_top : P 0 ⊤) (zero_bot : P 0 ⊥)
    (pos_top : ∀ x : ℚ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℚ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℚ, P x y) : ∀ x y, P x y :=
  have : ∀ y, (∀ x : ℚ, 0 < x → P x y) → ∀ x : ℚ, x < 0 → P x y := fun _ h x hx =>
    neg_neg (x : ERat) ▸ neg_left <| h _ (neg_pos_of_neg hx)
  @induction₂ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (this _ pos_top) (this _ pos_bot) (neg_left top_top)
    (fun x hx => neg_left <| top_pos x hx) (neg_left top_zero)
    (fun x hx => neg_left <| top_neg x hx) (neg_left top_bot)

/-- Induct on two `ERat`s by performing case splits on the sign of one whenever the other is infinite.
    This version eliminates some cases by assuming that `P` is symmetric and that
    `P x y` implies `P (-x) y` for all `x` and `y`. -/
@[elab_as_elim]
lemma induction₂_symm_neg {P : ERat → ERat → Prop}
    (symm : ∀ {x y}, P x y → P y x)
    (neg_left : ∀ {x y}, P x y → P (-x) y) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0) (coe_coe : ∀ x y : ℚ, P x y) :
    ∀ x y, P x y :=
  have neg_right : ∀ {x y}, P x y → P x (-y) := fun h => symm <| neg_left <| symm h
  have : ∀ x, (∀ y : ℚ, 0 < y → P x y) → ∀ y : ℚ, y < 0 → P x y := fun _ h y hy =>
    neg_neg (y : ERat) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos top_zero (this _ top_pos) (neg_right top_top)
    (symm top_zero) (symm <| neg_left top_zero) (fun x hx => symm <| top_pos x hx)
    (fun x hx => symm <| neg_left <| top_pos x hx) coe_coe

/-! ### Sign -/

open SignType (sign)

lemma sign_top : sign (⊤ : ERat) = 1 := rfl

lemma sign_bot : sign (⊥ : ERat) = -1 := rfl

@[simp]
lemma sign_coe (x : ℚ) : sign (x : ERat) = sign x := by
  simp only [sign, OrderHom.coe_mk, ERat.coe_pos, ERat.coe_neg']

@[simp, norm_cast]
lemma coe_coe_sign (x : SignType) : ((x : ℚ) : ERat) = x := by cases x <;> rfl

@[simp] lemma sign_neg : ∀ x : ERat, sign (-x) = -sign x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℚ) => by rw [←coe_neg, sign_coe, sign_coe, Left.sign_neg]

end ERat
