import VCSP.Basic


structure Set.IsClone {D: Type} (S : Set ( Σ n : ℕ, (Fin n → D) → D)) : Prop where
  projections_exist : ∀ k : ℕ, ∀ i : Fin k, ⟨k, (fun x : Fin k → D => x i)⟩ ∈ S
  closed_under_comp : ∀ k m : ℕ, ∀ f : (Fin k → D) → D , ∀ z : Fin k → _,
    (∀ i : Fin k, ⟨m, z i⟩ ∈ S) → (⟨k, f⟩ ∈ S) →
      ⟨m, fun x : (Fin m → D) => f (z · x)⟩ ∈ S

def proj (D : Type) : Set ( Σ n : ℕ, (Fin n → D) → D) :=
  { ⟨n, f⟩ | ∃ i : Fin n, ∀ x, f x = x i }

theorem proj_is_clone (D : Type) : (proj D).IsClone := by
  constructor
  · intro k i
    use i
    intro x
    rfl
  · intro k m f z hz hf
    obtain ⟨i, hi⟩ := hf
    obtain ⟨j, hj⟩ := hz i
    use j
    intro y
    simp [hi, hj]
