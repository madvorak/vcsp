import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.List.OfFn


/-- TODO description -/
abbrev FractionalOperation (D : Type*) (m : ℕ) : Type _ :=
  Multiset ((Fin m → D) → D)

variable {D C : Type*} [OrderedAddCommMonoid C] {m : ℕ}

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
def FractionalOperation.tt {n : ℕ} (ω : FractionalOperation D m) (x : Fin m → Fin n → D) :
    Multiset (Fin n → D) :=
  ω.map (fun (g : (Fin m → D) → D) (i : Fin n) => g ((Function.swap x) i))

/-- TODO description -/
def Function.AdmitsFractional {n : ℕ} (f : (Fin n → D) → C) (ω : FractionalOperation D m) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • ((ω.tt x).map f).sum ≤ ω.size • (Finset.univ.val.map (fun i => f (x i))).sum

/-- TODO description -/
def FractionalOperation.IsFractionalPolymorphismFor (ω : FractionalOperation D m) (Γ : ValuedCsp D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

/-- TODO description -/
def FractionalOperation.IsSymmetric (ω : FractionalOperation D m) : Prop :=
  ∀ x y : (Fin m → D), List.ofFn x ~ List.ofFn y → ∀ g ∈ ω, g x = g y

/-- TODO description -/
def FractionalOperation.IsSymmetricFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : ValuedCsp D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric
