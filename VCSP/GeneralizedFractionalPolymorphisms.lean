import VCSP.FractionalPolymorphisms
import Mathlib.Data.List.FinRange

theorem Equiv.Perm.ofFn_perm_iff {n : ℕ} {α : Type*} (f g : Fin n → α) :
    List.ofFn f ~ List.ofFn g ↔ ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  constructor
  · intro hyp
    sorry
  · intro ⟨σ, hg⟩
    rw [← hg]
    exact (ofFn_comp_perm σ f).symm

abbrev GeneralizedOperation (D : Type*) (m : ℕ) : Type _ :=
  (Fin m → D) → (Fin m → D)

abbrev GeneralizedFractionalOperation (D : Type*) (m : ℕ) : Type _ :=
  Multiset (GeneralizedOperation D m)

variable {D : Type*} {m : ℕ}

def GeneralizedOperation.IsSymmetric (G : GeneralizedOperation D m) : Prop :=
  ∀ x y : (Fin m → D), List.ofFn x ~ List.ofFn y → List.ofFn (G x) ~ List.ofFn (G y)

lemma GeneralizedOperation.compose_symmetric (G H : GeneralizedOperation D m) :
    H.IsSymmetric → GeneralizedOperation.IsSymmetric (G ∘ H) := by
  intro sym x y ass
  sorry
