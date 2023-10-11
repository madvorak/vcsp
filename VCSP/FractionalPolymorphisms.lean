import VCSP.Definition
import Mathlib.Data.Matrix.Basic -- not really necessary


def FractionalOperation (D : Type) (m k : ℕ) : Type :=
  (Fin m → D) → (Fin k → D)

def FractionalOperation.tt {D : Type} {m k n : ℕ}
    (ω : FractionalOperation D m k) (x : (Fin m → (Fin n → D))) :
    (Fin k → (Fin n → D)) :=
  Matrix.transpose (fun (i : Fin n) => ω ((Matrix.transpose x) i))

def FractionalOperation.tt' {D : Type} {m k n : ℕ}
    (ω : FractionalOperation D m k) (x : (Fin m → (Fin n → D)))
    (a : Fin k) (b : Fin n) : D :=
  (ω (fun (i : Fin m) => x i b)) a

def Function.admits {D C : Type} [OrderedAddCommMonoid C] {n m k : ℕ}
    (f : (Fin n → D) → C) (ω : FractionalOperation D m k) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • List.sum (List.map (fun i => f ((ω.tt x) i)) (List.finRange k)) ≤
    k • List.sum (List.map (fun i => f (      x  i)) (List.finRange m))

def FractionalOperation.IsFractionalPolymorphism
    {D C : Type} [Nonempty D] [OrderedAddCommMonoid C] {m k : ℕ}
    (Γ : ValuedCspTemplate D C) (ω : FractionalOperation D m k) : Prop :=
  ∀ f ∈ Γ, f.snd.admits ω
