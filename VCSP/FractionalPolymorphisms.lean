import VCSP.Definition
import Mathlib.Data.Finsupp.Defs


def FractionalOperation (D : Type) (m k : ℕ) : Type :=
  (Fin m → D) → (Fin k → D)

/-
For documentation purposes, here is a "less compact" version of the upcoming two definitions:

[import Mathlib.Data.Matrix.Basic]

def FractionalOperation.tt {D : Type} {m k n : ℕ}
    (ω : FractionalOperation D m k) (x : (Fin m → (Fin n → D))) :
    (Fin k → (Fin n → D)) :=
  Matrix.transpose (fun (i : Fin n) => ω ((Matrix.transpose x) i))

def Function.AdmitsFractional {D C : Type} [OrderedAddCommMonoid C] {n m k : ℕ}
    (f : (Fin n → D) → C) (ω : FractionalOperation D m k) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • List.sum (List.map (fun i => f ((ω.tt x) i)) (List.finRange k)) ≤
    k • List.sum (List.map (fun i => f (      x  i)) (List.finRange m))

They should be defeq to the definitions below.
-/

def FractionalOperation.tt {D : Type} {m k n : ℕ}
    (ω : FractionalOperation D m k) (x : (Fin m → (Fin n → D)))
    (a : Fin k) (b : Fin n) : D :=
  (ω (fun (i : Fin m) => x i b)) a

def Function.AdmitsFractional {D C : Type} [OrderedAddCommMonoid C] {n m k : ℕ}
    (f : (Fin n → D) → C) (ω : FractionalOperation D m k) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • List.sum (List.map (f ∘ (ω.tt x)) (List.finRange k)) ≤
    k • List.sum (List.map (f ∘ x) (List.finRange m))

def FractionalOperation.IsFractionalPolymorphismFor
    {D C : Type} [Nonempty D] [OrderedAddCommMonoid C] {m k : ℕ}
    (ω : FractionalOperation D m k) (Γ : ValuedCspTemplate D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

def FractionalOperation.IsSymmetric
    {D : Type} [Nonempty D] {m k : ℕ} (ω : FractionalOperation D m k) : Prop :=
  ∀ x y : (Fin m → D), List.ofFn x ~ List.ofFn y → ω x = ω y

def FractionalOperation.IsSymmetricFractionalPolymorphismFor
    {D C : Type} [Nonempty D] [OrderedAddCommMonoid C] {m k : ℕ}
    (ω : FractionalOperation D m k) (Γ : ValuedCspTemplate D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric


def FractionalOperationAbstract (D : Type) (m : ℕ) : Type :=
  ((Fin m → D) → D) →₀ ℕ -- TODO at least one output `> 0`


def FractionalOperationEnumerative (D : Type) (m : ℕ) : Type :=
  (Fin m → D) → List (D × ℕ)

-- For `ω` to be valid, it must be a nonempty `List` and furthermore `.snd ≠ 0`
def FractionalOperationEnumerative.IsValid {D : Type} {m : ℕ}
    (ω : FractionalOperationEnumerative D m) : Prop :=
  ∀ a : (Fin m → D), ω a ≠ [] ∧ ∀ o ∈ ω a, o.snd ≠ 0


def WeightedOperation (D C : Type) [OrderedRing C] (m : ℕ) : Type :=
  ((Fin m → D) → D) →₀ C -- TODO all outputs nonnegative and sum up to one

def Function.AdmitsWeighted {D C : Type} [OrderedRing C] {n m : ℕ}
    (f : (Fin n → D) → C) (ω : WeightedOperation D C m) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    -- TODO apply `ω` and divide by the sum of its weights
    m • Finset.sum (List.finRange m).toFinset (fun i => f (x i)) ≤
    Finset.sum Finset.univ (f ∘ x)

def WeightedOperation.IsWeightedPolymorphism
    {D C : Type} [Nonempty D] [OrderedRing C] {m : ℕ}
    (Γ : ValuedCspTemplate D C) (ω : WeightedOperation D C m) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsWeighted ω
