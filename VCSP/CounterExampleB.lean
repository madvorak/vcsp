import VCSP.Hardness
import VCSP.AlgebraInst


example : False := by -- based on Yury G. Kudryashov's example
  let B : Multiset Bool := {true, false}
  let S : Multiset Bool := {false}
  let f : Bool → Bool → ENNReal := fun _ _ => 1
  let g : Bool → Bool → Bool → ENNReal := fun x _ y => if xor x y then 1 else 0
  have contr :
    ¬ sInf { S.summap (f · d) | d : Bool } ≤
      B.summap (fun b => sInf { S.summap (g b · d) | d : Bool })
  · simp [eq_comm, Set.setOf_or, Multiset.summap]
  apply contr
  apply sInf_summap_le_summap_sInf_summap
  intro d z
  cases z <;> simp_all [Multiset.summap]

example : False := by
  let B : Multiset Bool := {true, false}
  let S : Multiset Bool := {false}
  let f : Bool → Bool → ENNReal := fun _ _ => 1
  let g : Bool → Bool → Bool → ENNReal := fun x _ y => if xor x y then 2 else 0
  have contr :
    ¬ 2 • sInf { S.summap (f · d) | d : Bool } ≤
      B.summap (fun b => sInf { S.summap (g b · d) | d : Bool })
  · simp [eq_comm, Set.setOf_or, Multiset.summap]
  apply contr
  have size2 : 2 = Multiset.card.toFun B
  · simp
  rw [size2]
  apply nsmul_sInf_summap_le_summap_sInf_summap
  intro d z
  cases z <;> simp_all [Multiset.summap] <;> norm_num
