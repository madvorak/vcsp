import VCSP.Basic


structure Set.IsClone {D: Type*} (S : Set (Σ n : ℕ, (Fin n → D) → D)) : Prop where
  projections_exist : ∀ k : ℕ, ∀ i : Fin k, ⟨k, (fun x : Fin k → D => x i)⟩ ∈ S
  closed_under_comp : ∀ k m : ℕ, ∀ f : (Fin k → D) → D, ∀ g : Fin k → ((Fin m → D) → D),
    (⟨k, f⟩ ∈ S) → (∀ i : Fin k, ⟨m, g i⟩ ∈ S) → ⟨m, fun x : (Fin m → D) => f (g · x)⟩ ∈ S

def proj (D : Type*) : Set (Σ n : ℕ, (Fin n → D) → D) :=
  { ⟨n, f⟩ | ∃ i : Fin n, ∀ x, f x = x i }

theorem proj_is_clone (D : Type*) : (proj D).IsClone := by
  constructor
  · intro k i
    use i
    intro
    rfl
  · intro k m f g hf hg
    obtain ⟨i, hi⟩ := hf
    obtain ⟨j, hj⟩ := hg i
    use j
    intro
    simp [hi, hj]
