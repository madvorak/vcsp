import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.List.OfFn


/-- TODO description -/
@[reducible]
def FractionalOperation (D : Type*) (m : ℕ) : Type _ :=
  Multiset ((Fin m → D) → D)

variable {D C : Type*} [OrderedAddCommMonoid C]

/-- TODO maybe change to subtype -/
def FractionalOperation.IsValid {m : ℕ} (ω : FractionalOperation D m) : Prop :=
  ω ≠ ∅

/-- TODO description -/
def FractionalOperation.tt {m n : ℕ} (ω : FractionalOperation D m) (x : Fin m → Fin n → D) :
    Multiset (Fin n → D) :=
  ω.map (fun (g : (Fin m → D) → D) (i : Fin n) => g ((Function.swap x) i))

/-- TODO description -/
def Function.AdmitsFractional {n m : ℕ} (f : (Fin n → D) → C) (ω : FractionalOperation D m) :
    Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • ((ω.tt x).map f).sum ≤ Multiset.card.toFun ω • (Finset.univ.val.map (fun i => f (x i))).sum
  --m • ((ω.tt x).map f).sum ≤ Multiset.card.toFun ω • (Finset.univ.val.map (f ∘ x)).sum

/-- TODO description -/
def FractionalOperation.IsFractionalPolymorphismFor {m : ℕ}
    (ω : FractionalOperation D m) (Γ : ValuedCsp D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

/-- TODO description -/
def FractionalOperation.IsSymmetric {m : ℕ} (ω : FractionalOperation D m) : Prop :=
  ∀ x y : (Fin m → D), List.ofFn x ~ List.ofFn y → ∀ g ∈ ω, g x = g y

/-- TODO description -/
def FractionalOperation.IsSymmetricFractionalPolymorphismFor {m : ℕ}
    (ω : FractionalOperation D m) (Γ : ValuedCsp D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric
