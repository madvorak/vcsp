import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Pointwise.Basic
import VCSP.FractionalPolymorphisms


abbrev FilterValuedCsp (D C : Type*) [OrderedAddCommMonoid C] :=
  Set (Σ (n : ℕ), (Fin n → D) → UpperSet C)


variable {C : Type*} [OrderedAddCommMonoid C]

def addMink (x y : UpperSet C) : UpperSet C :=
  ⟨{ a + b | (a ∈ x) (b ∈ y) }, by
    intro c d cd hc
    rw [Set.mem_setOf_eq] at hc ⊢
    obtain ⟨a, ha, b, hb, eq_c⟩ := hc
    -- ??
    sorry⟩

lemma addMink_right_comm : RightCommutative (@addMink C _) := by
  intro x y z
  simp [addMink]
  apply Set.eq_of_subset_of_subset <;>
  · intro d hd
    rw [Set.mem_setOf_eq] at hd ⊢
    obtain ⟨a, ha, b, hb, c, hc, eq_d⟩ := hd
    use a, ha, c, hc, b, hb
    rw [add_right_comm]
    exact eq_d

def Multiset.sumMink (s : Multiset (UpperSet C)) : UpperSet C :=
  s.foldl addMink addMink_right_comm ⊥ -- OK for `CanonicallyOrderedAddCommMonoid`

instance : HSMul ℕ (UpperSet C) (UpperSet C) where
  hSMul := fun
  | .zero => ⊥ -- this is `Set.univ` but we should rather use `{ x | 0 ≤ x }`
  | .succ n => fun x => addMink x sorry -- add `(n • x)` from induction


variable {D : Type*}

/-- A term in a filter-valued CSP instance over the template `Γ`. -/
structure FilterValuedCsp.Term (Γ : FilterValuedCsp D C) (ι : Type*) where
  /-- Arity of the function -/
  n : ℕ
  /-- Which cost function is instantiated -/
  f : (Fin n → D) → UpperSet C
  /-- The cost function comes from the template -/
  inΓ : ⟨n, f⟩ ∈ Γ
  /-- Which variables are plugged as arguments to the cost function -/
  app : Fin n → ι

/-- Evaluation of a `Γ` term `t` for given solution `x`. -/
def FilterValuedCsp.Term.evalSolution {Γ : FilterValuedCsp D C} {ι : Type*}
    (t : Γ.Term ι) (x : ι → D) : UpperSet C :=
  t.f (x ∘ t.app)

/-- A filter-valued CSP instance over the template `Γ` with variables indexed by `ι`. -/
abbrev FilterValuedCsp.Instance (Γ : FilterValuedCsp D C) (ι : Type*) : Type _ :=
  Multiset (Γ.Term ι)

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
def FilterValuedCsp.Instance.evalSolution {Γ : FilterValuedCsp D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : UpperSet C :=
  (I.map (fun t : Γ.Term ι => t.evalSolution x)).sumMink

/-- Condition for `x` being an optimum solution (min) to given `Γ` instance `I`. -/
def FilterValuedCsp.Instance.IsOptimumSolution {Γ : FilterValuedCsp D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : Prop :=
  -- `≤` means `⊆` which, ironically, means "larger" (i.e. "less optimal") for us
  ∀ y : ι → D, I.evalSolution y ≤ I.evalSolution x

/-- Partial evaluation of a `Γ` instance `I` for given partial solution `x` waiting for rest. -/
def FilterValuedCsp.Instance.evalPartial {Γ : FilterValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : (μ → D) → UpperSet C :=
  fun r => I.evalSolution (Sum.elim x r)

/-- Evaluation of a `Γ` instance `I` for given partial solution `x`, union over the rest. -/
def FilterValuedCsp.Instance.evalMinimize {Γ : FilterValuedCsp D C} {ι μ : Type*}
    (I : Γ.Instance (ι ⊕ μ)) (x : ι → D) : UpperSet C :=
  sorry -- ⟨Set.iUnion (I.evalPartial x), sorry⟩

/-- A new VCSP template made of all functions expressible by `Γ`. -/
def FilterValuedCsp.expressivePower (Γ : FilterValuedCsp D C) : FilterValuedCsp D C :=
  { ⟨n, I.evalMinimize⟩ | (n : ℕ) (m : ℕ) (I : Γ.Instance (Fin n ⊕ Fin m)) }


variable {m : ℕ}

def Function.AdmitsFilterFractional {n : ℕ}
    (f : (Fin n → D) → UpperSet C) (ω : FractionalOperation D m) : Prop :=
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
  { ⟨n, f⟩ | (n : ℕ) (f : (Fin n → D) → UpperSet C) (_ : ∀ ω ∈ S, f.AdmitsFilterFractional ω.snd) }

def FilterValuedCsp.closure (Γ : FilterValuedCsp D C) : FilterValuedCsp D C :=
  Γ.allFractionalPolymorphisms.largestFilterValuedCsp

lemma FilterValuedCsp.allFractionalPolymorphisms_mem (Γ : FilterValuedCsp D C)
    (ω : FractionalOperation D m) :
    ⟨m, ω⟩ ∈ Γ.allFractionalPolymorphisms ↔ ∀ f ∈ Γ, f.snd.AdmitsFilterFractional ω := by
  unfold FilterValuedCsp.allFractionalPolymorphisms
  unfold FractionalOperation.IsFilterFractionalPolymorphismFor
  aesop
