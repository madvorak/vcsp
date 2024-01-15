import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.List.OfFn


/-- Fractional operation is a finite unordered collection of D^m → D possibly with duplicates. -/
abbrev FractionalOperation (D : Type*) (m : ℕ) : Type _ :=
  Multiset ((Fin m → D) → D)

variable {D : Type*} {m : ℕ}

/-- Arity of the "output" of the fractional operation. -/
@[simp]
def FractionalOperation.size (ω : FractionalOperation D m) : ℕ :=
  Multiset.card.toFun ω

/-- TODO maybe change to subtype -/
def FractionalOperation.IsValid (ω : FractionalOperation D m) : Prop :=
  ω ≠ ∅

lemma FractionalOperation.IsValid.contains {ω : FractionalOperation D m} (valid : ω.IsValid) :
    ∃ g : (Fin m → D) → D, g ∈ ω :=
  Multiset.exists_mem_of_ne_zero valid

/-- TODO description -/
def FractionalOperation.tt {ι : Type*} (ω : FractionalOperation D m) (x : Fin m → ι → D) :
    Multiset (ι → D) :=
  ω.map (fun (g : (Fin m → D) → D) (i : ι) => g ((Function.swap x) i))
-- `Function.swap` notation issue: https://github.com/leanprover/lean4/issues/1629

lemma FractionalOperation.tt_singleton {m n : ℕ} {ω : FractionalOperation D m} (x : Fin m → Fin n → D)
    {g : (Fin m → D) → D} (singleto : ω = {g}) :
    ω.tt x = {fun i => g (Function.swap x i)} := by
  unfold FractionalOperation.tt
  rw [singleto, Multiset.map_singleton]

variable {C : Type*} [OrderedAddCommMonoid C]

/-- Cost function admits given fractional operation, i.e., `ω` improves `f` in the `≤` sense. -/
def Function.AdmitsFractional {n : ℕ} (f : (Fin n → D) → C) (ω : FractionalOperation D m) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • ((ω.tt x).map f).sum ≤ ω.size • (Finset.univ.val.map (fun i => f (x i))).sum

/-- Fractional operation is a fractional polymorphism for given VCSP template. -/
def FractionalOperation.IsFractionalPolymorphismFor (ω : FractionalOperation D m) (Γ : ValuedCSP D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

/-- Fractional operation is symmetric. -/
def FractionalOperation.IsSymmetric (ω : FractionalOperation D m) : Prop :=
  ∀ x y : (Fin m → D), List.Perm (List.ofFn x) (List.ofFn y) → ∀ g ∈ ω, g x = g y

/-- Fractional operation is a symmetric fractional polymorphism for given VCSP template. -/
def FractionalOperation.IsSymmetricFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : ValuedCSP D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric

/-- Operation (n-ary) is idempotent. -/
def Function.IsIdempotentNary (g : (Fin m → D) → D) : Prop :=
  ∀ a : D, ∀ v : Fin m → D, (∀ i : Fin m, v i = a) → g v = a

/-- Fractional operation is idempotent. -/
def FractionalOperation.IsIdempotent (ω : FractionalOperation D m) : Prop :=
  ∀ g ∈ ω, g.IsIdempotentNary
