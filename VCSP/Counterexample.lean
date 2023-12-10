import VCSP.AlgebraInst


private lemma broken {C D : Type} [OrderedAddCommMonoidWithInfima C] {T M : Type}
    (W : Multiset T) (S : Multiset M) (f : T → D → C) (g : M → D → C)
    (hfg : ∀ d : D,
      (W.map (fun i : T => f i d)).sum ≤
      (S.map (fun i : M => g i d)).sum ):
    (W.map (fun i : T => sInf { f i a | a : D })).sum ≤
    (S.map (fun i : M => sInf { g i a | a : D })).sum := by
  sorry

example : False := by -- based on Yury G. Kudryashov's example
  let A : Multiset Unit := {()}
  let B : Multiset Bool := {true, false}
  let f : Unit → Bool → ENNReal := 1
  let g : Bool → Bool → ENNReal := fun x y => if xor x y then 1 else 0
  have contr :
    ¬ (A.map (fun a => sInf { f a d | d : Bool })).sum ≤
      (B.map (fun b => sInf { g b d | d : Bool })).sum
  · simp [eq_comm, Set.setOf_or]
  exact contr (broken A B f g (by simp))
