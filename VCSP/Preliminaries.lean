import Mathlib.Data.List.Basic

variable {α β : Type}


def n1ary_of_unary (f : α → β) : (Fin 1 → α) → β :=
  fun a => f (a 0)

def n2ary_of_binary (f : α → α → β) : (Fin 2 → α) → β :=
  fun a => f (a 0) (a 1)

lemma List.map_append' (f : α → β) (l₁ l₂ : List α) :
    List.map f (List.append l₁ l₂) = l₁.map f ++ l₂.map f := by
  induction l₁ <;> simp_all
