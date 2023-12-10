import VCSP.Hardness
import VCSP.AlgebraInst


example : False := by -- based on Yury G. Kudryashov's example
  let B : Multiset Bool := {true, false}
  let S : Multiset Bool := {false}
  let f : Bool → Bool → ENNReal := fun _ _ => 1
  let g : Bool → Bool → Bool → ENNReal := fun x _ y => if xor x y then 1 else 0
  have contr :
    ¬ sInf { S.summap (f · d) | d : Bool } ≤
      (B.map (fun b => sInf { S.summap (g b · d) | d : Bool })).sum
  · simp [eq_comm, Set.setOf_or, Multiset.summap]
  apply contr
  apply sInf_summap_le_summap_sInf_summap
  intro d z
  cases z <;> simp_all [Multiset.summap]
