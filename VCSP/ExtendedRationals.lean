/-
Adapted from:
https://github.com/leanprover-community/mathlib4/blob/333e2d79fdaee86489af73dee919bc4b66957a52/Mathlib/Data/Real/EReal.lean

Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Data.Real.EReal

open Function Set

noncomputable section


/-- ERat : The type of extended rationals `[-∞, ∞]` -/
def ERat := WithBot (WithTop ℚ)
  deriving Bot, Zero, One, Nontrivial, LinearOrderedAddCommMonoid, PartialOrder

instance : ZeroLEOneClass ERat := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop ℚ)))

instance : OrderBot ERat := inferInstanceAs (OrderBot (WithBot (WithTop ℚ)))
instance : OrderTop ERat := inferInstanceAs (OrderTop (WithBot (WithTop ℚ)))
instance : BoundedOrder ERat := inferInstanceAs (BoundedOrder (WithBot (WithTop ℚ)))

instance : AddCommMonoidWithOne ERat := inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop ℚ)))

instance : DenselyOrdered ERat := inferInstanceAs (DenselyOrdered (WithBot (WithTop ℚ)))

instance : CharZero ERat := inferInstanceAs (CharZero (WithBot (WithTop ℚ)))


/-- The canonical inclusion from Rats to ERats. Registered as a coercion. -/
@[coe] def Rat.toERat : ℚ → ERat := some ∘ some

namespace ERat

-- things unify with `WithBot.decidableLT` later if we don't provide this explicitly.
instance decidableLT : DecidableRel ((· < ·) : ERat → ERat → Prop) :=
  WithBot.decidableLT

-- TODO: Provide explicitly, otherwise it is inferred noncomputably from `CompleteLinearOrder` ??????????????
instance : Top ERat := ⟨some ⊤⟩

instance : Coe ℚ ERat := ⟨Rat.toERat⟩

theorem coe_strictMono : StrictMono Rat.toERat :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

theorem coe_injective : Injective Rat.toERat :=
  coe_strictMono.injective

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℚ} : (x : ERat) ≤ (y : ERat) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : ℚ} : (x : ERat) < (y : ERat) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℚ} : (x : ERat) = (y : ERat) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : ℚ} : (x : ERat) ≠ (y : ERat) ↔ x ≠ y :=
  coe_injective.ne_iff

instance : Inhabited ERat := ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : ℚ) : ERat) = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℚ) : ERat) = 1 := rfl

/-- A recursor for `ERat` in terms of the coercion.

A typical invocation looks like `induction x using ERat.rec`. Note that using `induction`
directly will unfold `ERat` to `Option` which is undesirable.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim]
protected def rec {C : ERat → Sort*} (h_bot : C ⊥) (h_Rat : ∀ a : ℚ, C a) (h_top : C ⊤) :
    ∀ a : ERat, C a
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
theorem coe_mul (x y : ℚ) : (↑(x * y) : ERat) = x * y :=
  rfl

/-- Induct on two `ERat`s by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
theorem induction₂ {P : ERat → ERat → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x)
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

/-- Induct on two `ERat`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
theorem induction₂_symm {P : ERat → ERat → Prop} (symm : ∀ {x y}, P x y → P y x)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : ℚ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥) (pos_bot : ∀ x : ℚ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℚ, P x y) (zero_bot : P 0 ⊥) (neg_bot : ∀ x : ℚ, x < 0 → P x ⊥)
    (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
  @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

/-! `ERat` with its multiplication is a `CommMonoidWithZero`. However, the proof of
associativity by hand is extremely painful (with 125 cases...). Instead, we will deduce it later
on from the facts that the absolute value and the sign are multiplicative functions taking value
in associative objects, and that they characterize an extended Rat number. For now, we only
record more basic properties of multiplication.
-/

protected theorem mul_comm (x y : ERat) : x * y = y * x := by
  induction' x using ERat.rec with x <;> induction' y using ERat.rec with y <;>
    try { rfl }
  rw [← coe_mul, ← coe_mul, mul_comm]

protected theorem one_mul : ∀ x : ERat, 1 * x = x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℚ) => congr_arg Rat.toERat (one_mul x)

theorem zero_mul {x : ERat} (hx : x ≠ ⊥) : 0 * x = 0 :=
  match x with
  | ⊤ => rfl
  | ⊥ => False.elim (hx rfl)
  | (x : ℚ) => congr_arg Rat.toERat (Rat.zero_mul x)

/-protected theorem zero_mul : ∀ x : ERat, 0 * x = 0
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℚ) => congr_arg Rat.toERat (zero_mul x)

instance : MulZeroOneClass ERat where
  one_mul := ERat.one_mul
  mul_one := fun x => by rw [ERat.mul_comm, ERat.one_mul]
  zero_mul := ERat.zero_mul
  mul_zero := fun x => by rw [ERat.mul_comm, ERat.zero_mul]-/

/-! ### Rat coercion -/

instance canLift : CanLift ERat ℚ (↑) fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    induction x using ERat.rec
    · simp at hx
    · simp
    · simp at hx

/-- The map from extended Rats to Rats sending infinities to zero. -/
def toRat : ERat → ℚ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℚ) => x

@[simp]
theorem toRat_top : toRat ⊤ = 0 :=
  rfl

@[simp]
theorem toRat_bot : toRat ⊥ = 0 :=
  rfl

@[simp]
theorem toRat_zero : toRat 0 = 0 :=
  rfl

@[simp]
theorem toRat_one : toRat 1 = 1 :=
  rfl

@[simp]
theorem toRat_coe (x : ℚ) : toRat (x : ERat) = x :=
  rfl

@[simp]
theorem bot_lt_coe (x : ℚ) : (⊥ : ERat) < x :=
  WithBot.bot_lt_coe _

@[simp]
theorem coe_ne_bot (x : ℚ) : (x : ERat) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
theorem bot_ne_coe (x : ℚ) : (⊥ : ERat) ≠ x :=
  (bot_lt_coe x).ne

@[simp]
theorem coe_lt_top (x : ℚ) : (x : ERat) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
theorem coe_ne_top (x : ℚ) : (x : ERat) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
theorem top_ne_coe (x : ℚ) : (⊤ : ERat) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
theorem bot_lt_zero : (⊥ : ERat) < 0 :=
  bot_lt_coe 0

@[simp]
theorem bot_ne_zero : (⊥ : ERat) ≠ 0 :=
  (coe_ne_bot 0).symm

@[simp]
theorem zero_ne_bot : (0 : ERat) ≠ ⊥ :=
  coe_ne_bot 0

@[simp]
theorem zero_lt_top : (0 : ERat) < ⊤ :=
  coe_lt_top 0

@[simp]
theorem zero_ne_top : (0 : ERat) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
theorem top_ne_zero : (⊤ : ERat) ≠ 0 :=
  (coe_ne_top 0).symm

theorem range_coe : range Rat.toERat = {⊥, ⊤}ᶜ := by
  ext x
  induction x using ERat.rec <;> simp

theorem range_coe_eq_Ioo : range Rat.toERat = Ioo ⊥ ⊤ := by
  ext x
  induction x using ERat.rec <;> simp

@[simp, norm_cast]
theorem coe_add (x y : ℚ) : (x + y).toERat = x.toERat + y.toERat :=
  rfl

@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : ℚ) : (↑(n • x) : ERat) = n • (x : ERat) :=
  map_nsmul (⟨⟨Rat.toERat, coe_zero⟩, coe_add⟩ : ℚ →+ ERat) _ _

#noalign ERat.coe_bit0
#noalign ERat.coe_bit1

@[simp, norm_cast]
theorem coe_eq_zero {x : ℚ} : (x : ERat) = 0 ↔ x = 0 :=
  ERat.coe_eq_coe_iff

@[simp, norm_cast]
theorem coe_eq_one {x : ℚ} : (x : ERat) = 1 ↔ x = 1 :=
  ERat.coe_eq_coe_iff

theorem coe_ne_zero {x : ℚ} : (x : ERat) ≠ 0 ↔ x ≠ 0 :=
  ERat.coe_ne_coe_iff

theorem coe_ne_one {x : ℚ} : (x : ERat) ≠ 1 ↔ x ≠ 1 :=
  ERat.coe_ne_coe_iff

@[simp, norm_cast]
protected theorem coe_nonneg {x : ℚ} : (0 : ERat) ≤ x ↔ 0 ≤ x :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_nonpos {x : ℚ} : (x : ERat) ≤ 0 ↔ x ≤ 0 :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_pos {x : ℚ} : (0 : ERat) < x ↔ 0 < x :=
  ERat.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_neg' {x : ℚ} : (x : ERat) < 0 ↔ x < 0 :=
  ERat.coe_lt_coe_iff

/-
theorem toRat_le_toRat {x y : ERat} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toRat ≤ y.toRat := by
  lift x to ℚ using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to ℚ using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h
-/

theorem coe_toRat {x : ERat} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toRat : ERat) = x := by
  lift x to ℚ using ⟨hx, h'x⟩
  rfl

theorem le_coe_toRat {x : ERat} (h : x ≠ ⊤) : x ≤ x.toRat := by
  by_cases h' : x = ⊥
  · rw [h', toRat_bot, coe_zero]
    decide
  · simp only [le_refl, coe_toRat h h']

theorem coe_toRat_le {x : ERat} (h : x ≠ ⊥) : ↑x.toRat ≤ x := by
  by_cases h' : x = ⊤
  · rw [h', toRat_top, coe_zero]
    decide
  · simp only [le_refl, coe_toRat h' h]

theorem eq_top_iff_forall_lt (x : ERat) : x = ⊤ ↔ ∀ y : ℚ, (y : ERat) < x := by
  constructor
  · rintro rfl
    exact ERat.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toRat, le_coe_toRat h⟩

theorem eq_bot_iff_forall_lt (x : ERat) : x = ⊥ ↔ ∀ y : ℚ, x < (y : ERat) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toRat, coe_toRat_le h⟩

/-
lemma exists_between_coe_Rat {x z : ERat} (h : x < z) : ∃ y : ℚ, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction' a using ERat.rec with a₀
  · exact (not_lt_bot ha₁).elim
  · exact ⟨a₀, by exact_mod_cast ha₁, by exact_mod_cast ha₂⟩
  · exact (not_top_lt ha₂).elim
-/

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
  simp_rw [← Ici_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ico (x y : ℚ) : Rat.toERat ⁻¹' Ico x y = Ico x y := by
  simp_rw [← Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc (x y : ℚ) : Rat.toERat ⁻¹' Ioc x y = Ioc x y := by
  simp_rw [← Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo (x y : ℚ) : Rat.toERat ⁻¹' Ioo x y = Ioo x y := by
  simp_rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ico_top (x : ℚ) : Rat.toERat ⁻¹' Ico x ⊤ = Ici x := by
  rw [← Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_top (x : ℚ) : Rat.toERat ⁻¹' Ioo x ⊤ = Ioi x := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc_bot (y : ℚ) : Rat.toERat ⁻¹' Ioc ⊥ y = Iic y := by
  rw [← Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo_bot (y : ℚ) : Rat.toERat ⁻¹' Ioo ⊥ y = Iio y := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_bot_top : Rat.toERat ⁻¹' Ioo ⊥ ⊤ = univ := by
  rw [← Ioi_inter_Iio]
  simp

/-! ### Order -/

/-- The set of numbers in `ERat` that are not equal to `±∞` is equivalent to `ℚ`. -/
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
theorem add_bot (x : ERat) : x + ⊥ = ⊥ :=
  WithBot.add_bot _

@[simp]
theorem bot_add (x : ERat) : ⊥ + x = ⊥ :=
  WithBot.bot_add _

@[simp]
theorem add_eq_bot_iff {x y : ERat} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot

/-
theorem bot_lt_add_iff {x y : ERat} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot, not_or]
-/

@[simp]
theorem top_add_top : (⊤ : ERat) + ⊤ = ⊤ :=
  rfl

@[simp]
theorem top_add_coe (x : ℚ) : (⊤ : ERat) + x = ⊤ :=
  rfl

@[simp]
theorem coe_add_top (x : ℚ) : (x : ERat) + ⊤ = ⊤ :=
  rfl

theorem toRat_add {x y : ERat} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toRat (x + y) = toRat x + toRat y := by
  lift x to ℚ using ⟨hx, h'x⟩
  lift y to ℚ using ⟨hy, h'y⟩
  rfl

/-
theorem addLECancellable_coe (x : ℚ) : AddLECancellable (x : ERat)
  | _, ⊤, _ => le_top
  | ⊥, _, _ => bot_le
  | ⊤, (z : ℚ), h => by simp only [coe_add_top, ← coe_add, top_le_iff, coe_ne_top] at h
  | _, ⊥, h => by simpa using h
  | (y : ℚ), (z : ℚ), h => by
    simpa only [← coe_add, ERat.coe_le_coe_iff, add_le_add_iff_left] using h

theorem add_lt_add_right_coe {x y : ERat} (h : x < y) (z : ℚ) : x + z < y + z :=
  not_le.1 <| mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_le
#align ERat.add_lt_add_right_coe ERat.add_lt_add_right_coe

theorem add_lt_add_left_coe {x y : ERat} (h : x < y) (z : ℚ) : (z : ERat) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z
#align ERat.add_lt_add_left_coe ERat.add_lt_add_left_coe

theorem add_lt_add {x y z t : ERat} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  · simp [h1, bot_le.trans_lt h2]
  · lift x to ℚ using ⟨h1.ne_top, hx⟩
    calc (x : ERat) + z < x + t := add_lt_add_left_coe h2 _
    _ ≤ y + t := add_le_add_right h1.le _
#align ERat.add_lt_add ERat.add_lt_add

theorem add_lt_add_of_lt_of_le' {x y z t : ERat} (h : x < y) (h' : z ≤ t) (hbot : t ≠ ⊥)
    (htop : t = ⊤ → z = ⊤ → x = ⊥) : x + z < y + t := by
  rcases h'.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    · obtain rfl := htop rfl rfl
      simpa
    lift z to ℚ using ⟨hz, hbot⟩
    exact add_lt_add_right_coe h z
  · exact add_lt_add h hlt

/-- See also `ERat.add_lt_add_of_lt_of_le'` for a version with weaker but less convenient
assumptions. -/
theorem add_lt_add_of_lt_of_le {x y z t : ERat} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x + z < y + t :=
  add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') fun ht' => (ht ht').elim
#align ERat.add_lt_add_of_lt_of_le ERat.add_lt_add_of_lt_of_le

theorem add_lt_top {x y : ERat} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y < ⊤ := by
  rw [← ERat.top_add_top]
  exact ERat.add_lt_add hx.lt_top hy.lt_top
#align ERat.add_lt_top ERat.add_lt_top

/-- We do not have a notion of `LinearOrderedAddCommMonoidWithBot` but we can at least make
the order dual of the extended Rats into a `LinearOrderedAddCommMonoidWithTop`. -/
instance : LinearOrderedAddCommMonoidWithTop ERatᵒᵈ where
  le_top := by simp
  top_add' := by
    rw [OrderDual.forall]
    intro x
    rw [← OrderDual.toDual_bot, ← toDual_add, bot_add, OrderDual.toDual_bot]
-/

/-! ### Negation -/

/-- negation on `ERat` -/
protected def neg : ERat → ERat
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℚ) => (-x : ℚ)

instance : Neg ERat := ⟨ERat.neg⟩

instance : SubNegZeroMonoid ERat where
  neg_zero := congr_arg Rat.toERat neg_zero
  zsmul := zsmulRec

@[simp]
theorem neg_top : -(⊤ : ERat) = ⊥ :=
  rfl

@[simp]
theorem neg_bot : -(⊥ : ERat) = ⊤ :=
  rfl

@[simp, norm_cast] theorem coe_neg (x : ℚ) : (↑(-x) : ERat) = -↑x := rfl

/-
@[simp, norm_cast] theorem coe_sub (x y : ℚ) : (↑(x - y) : ERat) = x - y := rfl
-/

@[norm_cast]
theorem coe_zsmul (n : ℤ) (x : ℚ) : (↑(n • x) : ERat) = n • (x : ERat) :=
  map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : ℚ →+ ERat) coe_neg _ _

instance : InvolutiveNeg ERat where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℚ) => congr_arg Rat.toERat (neg_neg a)

@[simp]
theorem toRat_neg : ∀ {a : ERat}, toRat (-a) = -toRat a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℚ) => rfl

@[simp]
theorem neg_eq_top_iff {x : ERat} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
theorem neg_eq_bot_iff {x : ERat} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
theorem neg_eq_zero_iff {x : ERat} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero

theorem neg_strictAnti : StrictAnti (- · : ERat → ERat) :=
  WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨compare_gt_iff_gt.mp rfl, fun _ => coe_lt_top _⟩⟩

@[simp] theorem neg_le_neg_iff {a b : ERat} : -a ≤ -b ↔ b ≤ a := neg_strictAnti.le_iff_le

-- Porting note (#10756): new lemma
@[simp] theorem neg_lt_neg_iff {a b : ERat} : -a < -b ↔ b < a := neg_strictAnti.lt_iff_lt

/-- `-a ≤ b ↔ -b ≤ a` on `ERat`. -/
protected theorem neg_le {a b : ERat} : -a ≤ b ↔ -b ≤ a := by
  rw [← neg_le_neg_iff, neg_neg]

/-
/-- if `-a ≤ b` then `-b ≤ a` on `ERat`. -/
protected theorem neg_le_of_neg_le {a b : ERat} (h : -a ≤ b) : -b ≤ a := ERat.neg_le.mp h
#align ERat.neg_le_of_neg_le ERat.neg_le_of_neg_le

/-- `a ≤ -b → b ≤ -a` on ERat -/
theorem le_neg_of_le_neg {a b : ERat} (h : a ≤ -b) : b ≤ -a := by
  rwa [← neg_neg b, ERat.neg_le, neg_neg]
#align ERat.le_neg_of_le_neg ERat.le_neg_of_le_neg

/-- Negation as an order reversing isomorphism on `ERat`. -/
def negOrderIso : ERat ≃o ERatᵒᵈ :=
  { Equiv.neg ERat with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }
#align ERat.neg_order_iso ERat.negOrderIso

theorem neg_lt_iff_neg_lt {a b : ERat} : -a < b ↔ -b < a := by
  rw [← neg_lt_neg_iff, neg_neg]
#align ERat.neg_lt_iff_neg_lt ERat.neg_lt_iff_neg_lt

theorem neg_lt_of_neg_lt {a b : ERat} (h : -a < b) : -b < a := neg_lt_iff_neg_lt.1 h
#align ERat.neg_lt_of_neg_lt ERat.neg_lt_of_neg_lt
-/

/-!
### Subtraction

Subtraction on `ERat` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `ERat`, beyond `SubNegZeroMonoid`, because of this bad behavior.
-/

@[simp]
theorem bot_sub (x : ERat) : ⊥ - x = ⊥ :=
  bot_add x

@[simp]
theorem sub_top (x : ERat) : x - ⊤ = ⊥ :=
  add_bot x

@[simp]
theorem top_sub_bot : (⊤ : ERat) - ⊥ = ⊤ :=
  rfl

@[simp]
theorem top_sub_coe (x : ℚ) : (⊤ : ERat) - x = ⊤ :=
  rfl

@[simp]
theorem coe_sub_bot (x : ℚ) : (x : ERat) - ⊥ = ⊤ :=
  rfl

/-
theorem sub_le_sub {x y z t : ERat} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
  add_le_add h (neg_le_neg_iff.2 h')
#align ERat.sub_le_sub ERat.sub_le_sub

theorem sub_lt_sub_of_lt_of_le {x y z t : ERat} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x - t < y - z :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])
#align ERat.sub_lt_sub_of_lt_of_le ERat.sub_lt_sub_of_lt_of_le

theorem coe_Rat_ERat_eq_coe_toNNRat_sub_coe_toNNRat (x : ℚ) :
    (x : ERat) = Rat.toNNRat x - Rat.toNNRat (-x) := by
  rcases le_total 0 x with (h | h)
  · lift x to ℚ≥0 using h
    rw [Rat.toNNRat_of_nonpos (neg_nonpos.mpr x.coe_nonneg), Rat.toNNRat_coe, ENNRat.coe_zero,
      coe_ennRat_zero, sub_zero]
    rfl
  · rw [Rat.toNNRat_of_nonpos h, ENNRat.coe_zero, coe_ennRat_zero, coe_nnRat_eq_coe_Rat,
      Rat.coe_toNNRat, zero_sub, coe_neg, neg_neg]
    exact neg_nonneg.2 h
#align ERat.coe_Rat_ERat_eq_coe_to_nnRat_sub_coe_to_nnRat ERat.coe_Rat_ERat_eq_coe_toNNRat_sub_coe_toNNRat

theorem toRat_sub {x y : ERat} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toRat (x - y) = toRat x - toRat y := by
  lift x to ℚ using ⟨hx, h'x⟩
  lift y to ℚ using ⟨hy, h'y⟩
  rfl
#align ERat.to_Rat_sub ERat.toRat_sub
-/

/-! ### Multiplication -/

@[simp] theorem top_mul_top : (⊤ : ERat) * ⊤ = ⊤ := rfl

@[simp] theorem top_mul_bot : (⊤ : ERat) * ⊥ = ⊥ := rfl

@[simp] theorem bot_mul_top : (⊥ : ERat) * ⊤ = ⊥ := rfl

@[simp] theorem bot_mul_bot : (⊥ : ERat) * ⊥ = ⊤ := rfl

theorem coe_mul_top_of_pos {x : ℚ} (h : 0 < x) : (x : ERat) * ⊤ = ⊤ :=
  if_pos h

theorem top_mul_coe_of_pos {x : ℚ} (h : 0 < x) : (⊤ : ERat) * x = ⊤ :=
  if_pos h

theorem coe_mul_bot_of_nng {x : ℚ} (h : 0 ≤ x) : (x : ERat) * ⊥ = ⊥ :=
  if_pos h

theorem bot_mul_coe_of_nng {x : ℚ} (h : 0 ≤ x) : (⊥ : ERat) * x = ⊥ :=
  if_pos h

theorem coe_mul_top_of_neg {x : ℚ} (h : x < 0) : (x : ERat) * ⊤ = ⊥ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

theorem top_mul_coe_of_neg {x : ℚ} (h : x < 0) : (⊤ : ERat) * x = ⊥ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

theorem coe_mul_bot_of_neg {x : ℚ} (h : x < 0) : (x : ERat) * ⊥ = ⊤ := by
  apply if_neg
  intro cont
  exact (h.trans_le cont).false

/-
theorem mul_top_of_pos : ∀ {x : ERat}, 0 < x → x * ⊤ = ⊤
  | ⊥, h => absurd h not_lt_bot
  | (x : ℚ), h => coe_mul_top_of_pos (ERat.coe_pos.1 h)
  | ⊤, _ => rfl
#align ERat.mul_top_of_pos ERat.mul_top_of_pos

theorem mul_top_of_neg : ∀ {x : ERat}, x < 0 → x * ⊤ = ⊥
  | ⊥, _ => rfl
  | (x : ℚ), h => coe_mul_top_of_neg (ERat.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt
#align ERat.mul_top_of_neg ERat.mul_top_of_neg

theorem top_mul_of_pos {x : ERat} (h : 0 < x) : ⊤ * x = ⊤ := by
  rw [ERat.mul_comm]
  exact mul_top_of_pos h
#align ERat.top_mul_of_pos ERat.top_mul_of_pos

theorem top_mul_of_neg {x : ERat} (h : x < 0) : ⊤ * x = ⊥ := by
  rw [ERat.mul_comm]
  exact mul_top_of_neg h
#align ERat.top_mul_of_neg ERat.top_mul_of_neg

theorem bot_mul_coe_of_neg {x : ℚ} (h : x < 0) : (⊥ : ERat) * x = ⊤ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

theorem mul_bot_of_pos : ∀ {x : ERat}, 0 < x → x * ⊥ = ⊥
  | ⊥, h => absurd h not_lt_bot
  | (x : ℚ), h => coe_mul_bot_of_pos (ERat.coe_pos.1 h)
  | ⊤, _ => rfl
#align ERat.mul_bot_of_pos ERat.mul_bot_of_pos

theorem mul_bot_of_neg : ∀ {x : ERat}, x < 0 → x * ⊥ = ⊤
  | ⊥, _ => rfl
  | (x : ℚ), h => coe_mul_bot_of_neg (ERat.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt
#align ERat.mul_bot_of_neg ERat.mul_bot_of_neg

theorem bot_mul_of_pos {x : ERat} (h : 0 < x) : ⊥ * x = ⊥ := by
  rw [ERat.mul_comm]
  exact mul_bot_of_pos h
#align ERat.bot_mul_of_pos ERat.bot_mul_of_pos

theorem bot_mul_of_neg {x : ERat} (h : x < 0) : ⊥ * x = ⊤ := by
  rw [ERat.mul_comm]
  exact mul_bot_of_neg h
#align ERat.bot_mul_of_neg ERat.bot_mul_of_neg

theorem toRat_mul {x y : ERat} : toRat (x * y) = toRat x * toRat y := by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, ERat.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [coe_mul_bot_of_pos h]
  | neg_bot _ h => simp [coe_mul_bot_of_neg h]
-/

/-- Induct on two ERats by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for all
`x`, `y`. -/
@[elab_as_elim]
theorem induction₂_neg_left {P : ERat → ERat → Prop} (neg_left : ∀ {x y}, P x y → P (-x) y)
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

/-- Induct on two ERats by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P` is symmetric and `P x y` implies
`P (-x) y` for all `x`, `y`. -/
@[elab_as_elim]
theorem induction₂_symm_neg {P : ERat → ERat → Prop}
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

/-
protected theorem neg_mul (x y : ERat) : -x * y = -(x * y) := by
  induction x, y using induction₂_neg_left with
  | top_zero | zero_top | zero_bot => simp only [zero_mul, mul_zero, neg_zero]
  | top_top | top_bot => rfl
  | neg_left h => rw [h, neg_neg, neg_neg]
  | coe_coe => norm_cast; exact neg_mul _ _
  | top_pos _ h => rw [top_mul_coe_of_pos h, neg_top, bot_mul_coe_of_pos h]
  | pos_top _ h => rw [coe_mul_top_of_pos h, neg_top, ← coe_neg,
    coe_mul_top_of_neg (neg_neg_of_pos h)]
  | top_neg _ h => rw [top_mul_coe_of_neg h, neg_top, bot_mul_coe_of_neg h, neg_bot]
  | pos_bot _ h => rw [coe_mul_bot_of_pos h, neg_bot, ← coe_neg,
    coe_mul_bot_of_neg (neg_neg_of_pos h)]

instance : HasDistribNeg ERat where
  neg_mul := ERat.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm, x.mul_comm]
    exact y.neg_mul x
-/

/-! ### Sign -/

open SignType (sign)

theorem sign_top : sign (⊤ : ERat) = 1 := rfl

theorem sign_bot : sign (⊥ : ERat) = -1 := rfl

@[simp]
theorem sign_coe (x : ℚ) : sign (x : ERat) = sign x := by
  simp only [sign, OrderHom.coe_mk, ERat.coe_pos, ERat.coe_neg']

@[simp, norm_cast]
theorem coe_coe_sign (x : SignType) : ((x : ℚ) : ERat) = x := by cases x <;> rfl

@[simp] theorem sign_neg : ∀ x : ERat, sign (-x) = -sign x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℚ) => by rw [← coe_neg, sign_coe, sign_coe, Left.sign_neg]

/-
@[simp]
theorem sign_mul (x y : ERat) : sign (x * y) = sign x * sign y := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [zero_mul, mul_zero, sign_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, ERat.mul_comm]
  | coe_coe => simp only [← coe_mul, sign_coe, _root_.sign_mul]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, sign_top, one_mul, sign_pos (ERat.coe_pos.2 h)]
  | neg_left h => rw [neg_mul, sign_neg, sign_neg, h, neg_mul]
#align ERat.sign_mul ERat.sign_mul

@[simp] protected theorem sign_mul_abs : ∀ x : ERat, (sign x * x.abs : ERat) = x
  | ⊥ => by simp
  | ⊤ => by simp
  | (x : ℚ) => by rw [sign_coe, coe_abs, ← coe_coe_sign, ← coe_mul, sign_mul_abs]
#align ERat.sign_mul_abs ERat.sign_mul_abs

@[simp] protected theorem abs_mul_sign (x : ERat) : (x.abs * sign x : ERat) = x := by
  rw [ERat.mul_comm, ERat.sign_mul_abs]

theorem sign_eq_and_abs_eq_iff_eq {x y : ERat} :
    x.abs = y.abs ∧ sign x = sign y ↔ x = y := by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs, ← y.sign_mul_abs, habs, hsign]
  · rintro rfl
    exact ⟨rfl, rfl⟩
#align ERat.sign_eq_and_abs_eq_iff_eq ERat.sign_eq_and_abs_eq_iff_eq

theorem le_iff_sign {x y : ERat} :
    x ≤ y ↔ sign x < sign y ∨
      sign x = SignType.neg ∧ sign y = SignType.neg ∧ y.abs ≤ x.abs ∨
        sign x = SignType.zero ∧ sign y = SignType.zero ∨
          sign x = SignType.pos ∧ sign y = SignType.pos ∧ x.abs ≤ y.abs := by
  constructor
  · intro h
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    rw [← x.sign_mul_abs, ← y.sign_mul_abs] at h
    cases hy : sign y <;> rw [hs, hy] at h ⊢
    · simp
    · left; simpa using h
    · right; right; simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]
#align ERat.le_iff_sign ERat.le_iff_sign

instance : CommMonoidWithZero ERat :=
  { inferInstanceAs (MulZeroOneClass ERat) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, eq_self_iff_true, sign_mul, and_self_iff]
    mul_comm := ERat.mul_comm }

instance : PosMulMono ERat := posMulMono_iff_covariant_pos.2 <| .mk <| by
  rintro ⟨x, x0⟩ a b h
  simp only [le_iff_sign, ERat.sign_mul, sign_pos x0, one_mul, ERat.abs_mul] at h ⊢
  exact h.imp_right <| Or.imp (And.imp_right <| And.imp_right (mul_le_mul_left' · _)) <|
    Or.imp_right <| And.imp_right <| And.imp_right (mul_le_mul_left' · _)

instance : MulPosMono ERat := posMulMono_iff_mulPosMono.1 inferInstance

instance : PosMulReflectLT ERat := PosMulMono.toPosMulReflectLT

instance : MulPosReflectLT ERat :=
  MulPosMono.toMulPosReflectLT

@[simp, norm_cast]
theorem coe_pow (x : ℚ) (n : ℕ) : (↑(x ^ n) : ERat) = (x : ERat) ^ n :=
  map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : ℚ →* ERat) _ _
#align ERat.coe_pow ERat.coe_pow

@[simp, norm_cast]
theorem coe_ennRat_pow (x : ℚ≥0∞) (n : ℕ) : (↑(x ^ n) : ERat) = (x : ERat) ^ n :=
  map_pow (⟨⟨(↑), coe_ennRat_one⟩, coe_ennRat_mul⟩ : ℚ≥0∞ →* ERat) _ _
#align ERat.coe_ennRat_pow ERat.coe_ennRat_pow
-/

end ERat

-- Richard Copley provided:
@[simps]
def Rat.toERatAddHom : ℚ →+ ERat where
  toFun := Rat.toERat
  map_zero' := ERat.coe_zero
  map_add' := ERat.coe_add
