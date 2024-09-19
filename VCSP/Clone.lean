import VCSP.Basic

structure Set.IsClone
{D: Type}
(S : Set ( Σ n : ℕ, (Fin n → D) → D)) where
  projections_exist : ∀ k : ℕ, ∀ i : Fin k, ⟨k, (fun x : Fin k → D => x i)⟩ ∈ S
  closed_under_comp : ∀ k m : ℕ, ∀ f : (Fin k → D) → D , ∀ z : Fin k → _,
    (∀ i : Fin k, ⟨m, z i⟩ ∈ S) → (⟨k, f⟩ ∈ S) →
      ⟨m, fun x : (Fin m → D) => f (z · x)⟩  ∈ S
