import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.List.OfFn


/-- TODO description -/
@[reducible]
def FractionalOperation (D : Type*) (m : ℕ) : Type _ :=
  Multiset (((Fin m → D) → D) × ℕ)

variable {D C : Type*} [OrderedAddCommMonoid C]

/-- TODO maybe change to subtype -/
def FractionalOperation.IsValid {m : ℕ} (ω : FractionalOperation D m) : Prop :=
  ω ≠ ∅ ∧ ∀ g ∈ ω, g.snd ≠ 0

/-- TODO description -/
def weightedApplication {m n : ℕ} (g : ((Fin m → D) → D) × ℕ) (x' : Fin n → Fin m → D) :
    (Fin n → D) × ℕ :=
  ⟨fun i => g.fst (x' i), g.snd⟩

/-- TODO description -/
def FractionalOperation.tt {m n : ℕ} (ω : FractionalOperation D m) (x : Fin m → Fin n → D) :
    Multiset ((Fin n → D) × ℕ) :=
  ω.map (fun g => weightedApplication g (Function.swap x))

lemma weightedApplication_in {m n : ℕ} {ω : FractionalOperation D m} {g : ((Fin m → D) → D) × ℕ}
    (hg : g ∈ ω) (x : Fin m → Fin n → D) :
    weightedApplication g (Function.swap x) ∈ FractionalOperation.tt ω x := by
  rw [FractionalOperation.tt, Multiset.mem_map]
  exact ⟨g, hg, rfl⟩

/-- TODO description -/
def Function.AdmitsFractional {n m : ℕ} (f : (Fin n → D) → C) (ω : FractionalOperation D m) :
    Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • ((ω.tt x).map (fun r => r.snd • f r.fst)).sum ≤
    (ω.map Prod.snd).sum • (Finset.univ.val.map (fun i => f (x i))).sum

/-- TODO description -/
def FractionalOperation.IsFractionalPolymorphismFor {m : ℕ}
    (ω : FractionalOperation D m) (Γ : ValuedCsp D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

/-- TODO description -/
def FractionalOperation.IsSymmetric {m : ℕ} (ω : FractionalOperation D m) : Prop :=
  ∀ x y : (Fin m → D), List.ofFn x ~ List.ofFn y → ∀ g ∈ ω, g.fst x = g.fst y

/-- TODO description -/
def FractionalOperation.IsSymmetricFractionalPolymorphismFor {m : ℕ}
    (ω : FractionalOperation D m) (Γ : ValuedCsp D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric
