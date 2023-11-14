import Mathlib.Combinatorics.SimpleGraph.Basic

def SimpleGraph.cutSize {α : Type} {U V : Finset α} (G : SimpleGraph V) (hu : U ⊆ V) : ℕ :=
sorry -- TODO  ((V ×ˢ V).filter (fun (e : V ×ˢ V) => e.1.fst ∈ U ∧ e.1.snd ∉ U)).card
