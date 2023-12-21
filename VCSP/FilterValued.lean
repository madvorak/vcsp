import Mathlib.Order.PFilter
import VCSP.FractionalPolymorphisms


abbrev FilterValuedCsp (D C : Type*) [OrderedAddCommMonoid C] :=
  Set (Σ (n : ℕ), (Fin n → D) → Order.PFilter C)

variable {D C : Type*} [OrderedAddCommMonoid C]

/-- A term in a valued CSP instance over the template `Γ`. -/
structure FilterValuedCsp.Term (Γ : FilterValuedCsp D C) (ι : Type*) where
  /-- Arity of the function -/
  n : ℕ
  /-- Which cost function is instantiated -/
  f : (Fin n → D) → Order.PFilter C
  /-- The cost function comes from the template -/
  inΓ : ⟨n, f⟩ ∈ Γ
  /-- Which variables are plugged as arguments to the cost function -/
  app : Fin n → ι

/-- Evaluation of a `Γ` term `t` for given solution `x`. -/
def FilterValuedCsp.Term.evalSolution {Γ : FilterValuedCsp D C} {ι : Type*}
    (t : Γ.Term ι) (x : ι → D) : Order.PFilter C :=
  t.f (x ∘ t.app)

/-- A valued CSP instance over the template `Γ` with variables indexed by `ι`.-/
abbrev FilterValuedCsp.Instance (Γ : FilterValuedCsp D C) (ι : Type*) : Type _ :=
  Multiset (Γ.Term ι)

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
def FilterValuedCsp.Instance.evalSolution {Γ : FilterValuedCsp D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : Order.PFilter C := sorry
  -- (I.map (fun t : Γ.Term => t.evalSolution x)).sum -- TODO Minkowski sum

/-- Condition for `x` being an optimum solution (min) to given `Γ` instance `I`.-/
def FilterValuedCsp.Instance.IsOptimumSolution {Γ : FilterValuedCsp D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : Prop :=
  -- `≤` means `⊆` which means "larger" (i.e. "less optimal") for us
  ∀ y : ι → D, I.evalSolution y ≤ I.evalSolution x

variable {m : ℕ}

def Function.AdmitsFilterFractional {n : ℕ}
    (f : (Fin n → D) → Order.PFilter C) (ω : FractionalOperation D m) : Prop :=
  ∀ x : (Fin m → (Fin n → D)), sorry
  -- ω.size • (Finset.univ.val.map (fun i => f (x i))).sum ≤ m • ((ω.tt x).map f).sum -- TODO Minkowski sum

/-- Fractional operation is a fractional polymorphism for given VCSP template. -/
def FractionalOperation.IsFilterFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : FilterValuedCsp D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFilterFractional ω

/-- Fractional operation is a symmetric fractional polymorphism for given VCSP template. -/
def FractionalOperation.IsFilterSymmetricFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : FilterValuedCsp D C) : Prop :=
  ω.IsFilterFractionalPolymorphismFor Γ ∧ ω.IsSymmetric
