import VCSP.AlgebraInst
import VCSP.Hardness


private lemma broken {C D : Type} [OrderedAddCommMonoid C] [CompleteLattice C] {T M : Type}
    (W : Multiset T) (S : Multiset M) (f : T → D → C) (g : M → D → C)
    (hfg : ∀ d : D,
      W.summap (fun i : T => f i d) ≤
      S.summap (fun i : M => g i d) ):
    W.summap (fun i : T => sInf { f i a | a : D }) ≤
    S.summap (fun i : M => sInf { g i a | a : D }) := by
  sorry

example : False := by -- based on Yury G. Kudryashov's example
  let A : Multiset Unit := {()}
  let B : Multiset Bool := {true, false}
  let f : Unit → Bool → ENNReal := 1
  let g : Bool → Bool → ENNReal := fun x y => if xor x y then 1 else 0
  have contr :
    ¬ A.summap (fun a => sInf { f a d | d : Bool }) ≤
      B.summap (fun b => sInf { g b d | d : Bool })
  · simp [eq_comm, Set.setOf_or]
  exact contr (broken A B f g (by simp))
