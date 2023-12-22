import Mathlib.Order.PFilter
import Mathlib.Data.Set.Pointwise.Basic
import VCSP.FractionalPolymorphisms


abbrev FilterValuedCsp (D C : Type*) [OrderedAddCommMonoid C] :=
  Set (Σ (n : ℕ), (Fin n → D) → Order.PFilter C)


variable {C : Type*} [OrderedAddCommMonoid C]

def addMink_aux (x y : Order.Ideal C) : Order.Ideal C :=
  let z := { a + b | (a ∈ x) (b ∈ y) }
  have hz : Order.IsIdeal z := by
    constructor
    · sorry -- TODO `IsLowerSet`
    · obtain ⟨x₁, hx₁⟩ := x.nonempty
      obtain ⟨y₁, hy₁⟩ := y.nonempty
      exact ⟨x₁ + y₁, x₁, hx₁, y₁, hy₁, rfl⟩
    · sorry -- TODO `DirectedOn`
  hz.toIdeal

def addMink (x y : Order.PFilter C) : Order.PFilter C :=
  ⟨addMink_aux x.dual y.dual⟩

instance : Zero (Order.PFilter C) where
  zero := ⟨⟨{0}, sorry⟩, Set.zero_nonempty, directedOn_singleton IsRefl.reflexive 0⟩

def Multiset.sumMink (s : Multiset (Order.PFilter C)) : Order.PFilter C :=
  s.foldl addMink sorry 0

instance : HSMul ℕ (Order.PFilter C) (Order.PFilter C) where
  hSMul := fun
  | .zero => 0
  | .succ n => fun x => addMink x sorry -- add `(n • x)` from induction


variable {D : Type*}

/-- A term in a filter-valued CSP instance over the template `Γ`. -/
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

/-- A filter-valued CSP instance over the template `Γ` with variables indexed by `ι`. -/
abbrev FilterValuedCsp.Instance (Γ : FilterValuedCsp D C) (ι : Type*) : Type _ :=
  Multiset (Γ.Term ι)

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
def FilterValuedCsp.Instance.evalSolution {Γ : FilterValuedCsp D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : Order.PFilter C :=
  (I.map (fun t : Γ.Term ι => t.evalSolution x)).sumMink

/-- Condition for `x` being an optimum solution (min) to given `Γ` instance `I`. -/
def FilterValuedCsp.Instance.IsOptimumSolution {Γ : FilterValuedCsp D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : Prop :=
  -- `≤` means `⊆` which, ironically, means "larger" (i.e. "less optimal") for us
  ∀ y : ι → D, I.evalSolution y ≤ I.evalSolution x

/-- Partial evaluation of a `Γ` instance `I` for given partial solution `x` waiting for rest. -/
def FilterValuedCsp.Instance.evalPartial {Γ : FilterValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : (μ → D) → Order.PFilter C :=
  fun r => I.evalSolution (Sum.elim x r)

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, union over the rest. -/
def FilterValuedCsp.Instance.evalMinimize {Γ : FilterValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : Order.PFilter C :=
  sorry -- Union (I.evalPartial x)

/-- A new VCSP template made of all functions expressible by `Γ`. -/
def FilterValuedCsp.expressivePower (Γ : FilterValuedCsp D C) : FilterValuedCsp D C :=
  { ⟨n, I.evalMinimize⟩ | (n : ℕ) (m : ℕ) (I : Γ.Instance (Fin n ⊕ Fin m)) }

variable {m : ℕ}

def Function.AdmitsFilterFractional {n : ℕ}
    (f : (Fin n → D) → Order.PFilter C) (ω : FractionalOperation D m) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    ω.size • (Finset.univ.val.map (fun i => f (x i))).sumMink ≤ m • ((ω.tt x).map f).sumMink

/-- Fractional operation is a fractional polymorphism for given VCSP template. -/
def FractionalOperation.IsFilterFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : FilterValuedCsp D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFilterFractional ω

/-- Fractional operation is a symmetric fractional polymorphism for given VCSP template. -/
def FractionalOperation.IsFilterSymmetricFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : FilterValuedCsp D C) : Prop :=
  ω.IsFilterFractionalPolymorphismFor Γ ∧ ω.IsSymmetric

def FilterValuedCsp.allFractionalPolymorphisms (Γ : FilterValuedCsp D C) :
    Set (Σ (m : ℕ), FractionalOperation D m) :=
  { ⟨m, ω⟩ | (m : ℕ) (ω : FractionalOperation D m) (_ : ω.IsFilterFractionalPolymorphismFor Γ) }

def Set.largestFilterValuedCsp (S : Set (Σ (m : ℕ), FractionalOperation D m)) :
    FilterValuedCsp D C :=
  { ⟨n, f⟩ | (n : ℕ) (f : (Fin n → D) → Order.PFilter C) (_ : ∀ ω ∈ S, f.AdmitsFilterFractional ω.snd) }

def FilterValuedCsp.closure (Γ : FilterValuedCsp D C) : FilterValuedCsp D C :=
  Γ.allFractionalPolymorphisms.largestFilterValuedCsp

lemma FilterValuedCsp.allFractionalPolymorphisms_mem (Γ : FilterValuedCsp D C)
    (ω : FractionalOperation D m) :
    ⟨m, ω⟩ ∈ Γ.allFractionalPolymorphisms ↔ ∀ f ∈ Γ, f.snd.AdmitsFilterFractional ω := by
  unfold FilterValuedCsp.allFractionalPolymorphisms
  unfold FractionalOperation.IsFilterFractionalPolymorphismFor
  aesop
