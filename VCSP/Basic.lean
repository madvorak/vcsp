import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Fin.VecNotation

/-!

# General-Valued Constraint Satisfaction Problems

General-Valued CSP is a very broad class of problems in discrete optimization.
General-Valued CSP subsumes Min-Cost-Hom (including 3-SAT for example) and Finite-Valued CSP.

## Main definitions
* `ValuedCspTemplate`: A VCSP template; fixes a domain, a codomain, and allowed cost functions.
* `ValuedCspTerm`: One summand in a VCSP instance; calls a concrete function from given template.
* `ValuedCspTerm.evalSolution`: An evaluation of the VCSP term for given solution.
* `ValuedCspInstance`: An instance of a VCSP problem over given template.
* `ValuedCspInstance.evalSolution`: An evaluation of the VCSP instance for given solution.
* `ValuedCspInstance.optimumSolution`: Is given solution a minimum of the VCSP instance?

-/

def n1ary_of_unary {α β : Type} (f : α → β) : (Fin 1 → α) → β :=
  fun a => f (a 0)

def n2ary_of_binary {α β : Type} (f : α → α → β) : (Fin 2 → α) → β :=
  fun a => f (a 0) (a 1)

/-- A template for a valued CSP problem with domain `D` and costs in `C`. -/
@[reducible]
def ValuedCspTemplate (D C : Type) [Nonempty D] [OrderedAddCommMonoid C] : Type :=
  Set (Σ (k : ℕ), (Fin k → D) → C) -- Cost functions from `D^k` to `C` for any `k`

variable {D C : Type} [Nonempty D] [OrderedAddCommMonoid C]

/-- A term in a valued CSP instance over the template `Γ`. -/
structure ValuedCspTerm (Γ : ValuedCspTemplate D C) (ι : Type) where
  /-- Arity of the function -/
  k : ℕ
  /-- Which cost function is instantiated -/
  f : (Fin k → D) → C
  /-- The cost function comes from the template -/
  inΓ : ⟨k, f⟩ ∈ (Γ : Set (Σ (k : ℕ), (Fin k → D) → C))
  /-- Which variables are plugged as arguments to the cost function -/
  app : Fin k → ι

def valuedCspTerm_of_unary {Γ : ValuedCspTemplate D C} {ι : Type} {f₁ : D → C}
    (ok : ⟨1, n1ary_of_unary f₁⟩ ∈ Γ) (i : ι) : ValuedCspTerm Γ ι :=
  ⟨1, n1ary_of_unary f₁, ok, ![i]⟩

def valuedCspTerm_of_binary {Γ : ValuedCspTemplate D C} {ι : Type} {f₂ : D → D → C}
    (ok : ⟨2, n2ary_of_binary f₂⟩ ∈ Γ) (i j : ι) : ValuedCspTerm Γ ι :=
  ⟨2, n2ary_of_binary f₂, ok, ![i, j]⟩

/-- Evaluation of a `Γ` term `t` for given solution `x`. -/
def ValuedCspTerm.evalSolution {Γ : ValuedCspTemplate D C} {ι : Type}
    (t : ValuedCspTerm Γ ι) (x : ι → D) : C :=
  t.f (x ∘ t.app)

/-- A valued CSP instance over the template `Γ` with variables indexed by `ι`.-/
def ValuedCspInstance (Γ : ValuedCspTemplate D C) (ι : Type) : Type :=
  List (ValuedCspTerm Γ ι)

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
def ValuedCspInstance.evalSolution {Γ : ValuedCspTemplate D C} {ι : Type}
    (I : ValuedCspInstance Γ ι) (x : ι → D) : C :=
  (I.map (fun t => t.evalSolution x)).sum

/-- Condition for `x` being an optimum solution (min) to given `Γ` instance `I`.-/
def ValuedCspInstance.optimumSolution {Γ : ValuedCspTemplate D C} {ι : Type}
    (I : ValuedCspInstance Γ ι) (x : ι → D) : Prop :=
  ∀ y : ι → D, I.evalSolution x ≤ I.evalSolution y
