import VCSP.ExtendedRationals
import VCSP.FarkasBasic


variable {F : Type*} [LinearOrderedField F]

-- Henrik Böving wrote this entire section:
section notation_EF

syntax:max ident noWs "∞" : term

macro_rules
| `($F:ident∞) => `(Extend $F)

@[app_unexpander Extend]
def unexpandExtend : Lean.PrettyPrinter.Unexpander
  | `($(_) $F:ident) => `($F:ident∞)
  | _ => throw ()

end notation_EF


section extras_EF

def EF.smulNN (c : { a : F // 0 ≤ a }) : F∞ → F∞
| ⊥ => ⊥
| ⊤ => if c = 0 then 0 else ⊤
| (f : F) => toE (c.val * f)

instance : SMulZeroClass { a : F // 0 ≤ a } F∞ where
  smul := EF.smulNN
  smul_zero (c : { a : F // 0 ≤ a }) := EF.coe_eq_coe_iff.mpr (mul_zero c.val)

lemma EF.pos_smul_top {c : { a : F // 0 ≤ a }} (hc : 0 < c) : c • (⊤ : F∞) = ⊤ := by
  show EF.smulNN c ⊤ = ⊤
  simp [EF.smulNN]
  exact hc.ne.symm

lemma EF.smul_top_neq_bot (c : { a : F // 0 ≤ a }) : c • (⊤ : F∞) ≠ ⊥ := by
  show EF.smulNN c ⊤ ≠ ⊥
  by_cases hc0 : c = 0 <;> simp [EF.smulNN, hc0]

lemma EF.smul_coe_neq_bot (c : { a : F // 0 ≤ a }) (f : F) : c • toE f ≠ (⊥ : F∞) :=
  EF.coe_neq_bot (c * f)

lemma EF.smul_bot (c : { a : F // 0 ≤ a }) : c • (⊥ : F∞) = ⊥ :=
  rfl

lemma EF.smul_nonbot_neq_bot (c : { a : F // 0 ≤ a }) {r : F∞} (hr : r ≠ ⊥) : c • r ≠ ⊥ := by
  match r with
  | ⊥ => simp at hr
  | ⊤ => apply EF.smul_top_neq_bot
  | (f : F) => apply EF.smul_coe_neq_bot

lemma EF.zero_smul_nonbot {r : F∞} (hr : r ≠ ⊥) : (0 : { a : F // 0 ≤ a }) • r = 0 := by
  show EF.smulNN 0 r = 0
  simp [EF.smulNN]
  match r with
  | ⊥ => simp at hr
  | ⊤ => rfl
  | (f : F) => rfl

lemma EF.zero_smul_coe {f : F} : (0 : { a : F // 0 ≤ a }) • toE f = 0 :=
  EF.zero_smul_nonbot (EF.coe_neq_bot f)


-- Richard Copley pointed out that we need this homomorphism:
def RatAddHom : F →+ F∞ := ⟨⟨toE, EF.coe_zero⟩, EF.coe_add⟩

lemma Finset.sum_toE {ι : Type*} [Fintype ι] (s : Finset ι) (f : ι → F) :
    toE (s.sum f) = s.sum (fun i : ι => toE (f i)) :=
  map_sum RatAddHom f s

lemma Multiset.sum_eq_EF_bot_iff (s : Multiset F∞) : s.sum = (⊥ : F∞) ↔ ⊥ ∈ s := by
  constructor <;> intro hs
  · induction s using Multiset.induction with
    | empty =>
      exfalso
      rw [Multiset.sum_zero] at hs
      exact EF.zero_neq_bot hs
    | cons a m ih =>
      rw [Multiset.mem_cons]
      rw [Multiset.sum_cons] at hs
      match a with
      | ⊥ =>
        left
        rfl
      | ⊤ =>
        match hm : m.sum with
        | ⊥ =>
          right
          exact ih hm
        | ⊤ =>
          exfalso
          rw [hm] at hs
          change hs to ⊤ + ⊤ = ⊥
          rw [EF.top_add_top] at hs
          exact top_ne_bot hs
        | (f : F) =>
          exfalso
          rw [hm] at hs
          change hs to ⊤ + toE f = ⊥
          rw [EF.top_add_coe] at hs
          exact top_ne_bot hs
      | (f : F) =>
        match hm : m.sum with
        | ⊥ =>
          right
          exact ih hm
        | ⊤ =>
          exfalso
          rw [hm] at hs
          change hs to toE f + ⊤ = ⊥
          rw [EF.coe_add_top] at hs
          exact top_ne_bot hs
        | (_ : F) =>
          exfalso
          rw [hm] at hs
          exact EF.coe_neq_bot _ hs
  · induction s using Multiset.induction with
    | empty =>
      exfalso
      exact Multiset.not_mem_zero ⊥ hs
    | cons a m ih =>
      rw [Multiset.sum_cons]
      rw [Multiset.mem_cons] at hs
      cases hs with
      | inl ha => rw [←ha, EF.bot_add]
      | inr hm => rw [ih hm, EF.add_bot]

lemma Multiset.sum_eq_EF_top {s : Multiset F∞} (htop : ⊤ ∈ s) (hbot : ⊥ ∉ s) :
    s.sum = (⊤ : F∞) := by
  induction s using Multiset.induction with
  | empty =>
    exfalso
    exact Multiset.not_mem_zero ⊤ htop
  | cons a m ih =>
    rw [Multiset.sum_cons]
    rw [Multiset.mem_cons] at htop
    cases htop with
    | inl ha =>
      rw [←ha]
      match hm : m.sum with
      | (f : F) => rfl
      | ⊤ => rfl
      | ⊥ =>
        exfalso
        apply hbot
        rw [Multiset.mem_cons]
        right
        rw [←Multiset.sum_eq_EF_bot_iff]
        exact hm
    | inr hm =>
      rw [ih hm ((hbot ∘ mem_cons_of_mem) ·)]
      match a with
      | (f : F) => rfl
      | ⊤ => rfl
      | ⊥ => simp at hbot

end extras_EF


open scoped Matrix
variable {I J : Type*} [Fintype I] [Fintype J]


section hetero_matrix_products_defs
variable {α γ : Type*} [AddCommMonoid α] [SMul γ α] -- elements come from `α` but weights (coefficients) from `γ`

/-- `Matrix.dotProd v w` is the sum of the element-wise products `w i • v i` akin the dot product but heterogeneous
    (mnemonic: "vector times weights").
    Note that the order of arguments (also with the infix notation) is opposite than in the `SMul` it builds upon. -/
def Matrix.dotProd (v : I → α) (w : I → γ) : α := ∑ i : I, w i • v i

infixl:72 " ᵥ⬝ " => Matrix.dotProd

/-- `Matrix.mulWeig M w` is the heterogeneous analogue of the matrix-vector product `Matrix.mulVec M v`
    (mnemonic: "matrix times weights").
    Note that the order of arguments (also with the infix notation) is opposite than in the `SMul` it builds upon. -/
def Matrix.mulWeig (M : Matrix I J α) (w : J → γ) (i : I) : α :=
  M i ᵥ⬝ w

infixr:73 " ₘ* " => Matrix.mulWeig

end hetero_matrix_products_defs


section hetero_matrix_products_EF

lemma Matrix.no_bot_dotProd_zero {v : I → F∞} (hv : ∀ i, v i ≠ ⊥) :
    v ᵥ⬝ (0 : I → { a : F // 0 ≤ a }) = (0 : F∞) := by
  apply Finset.sum_eq_zero
  intro i _
  match hvi : v i with
  | ⊤ => -- TODO refactor
    show EF.smulNN 0 ⊤ = 0
    simp [EF.smulNN]
  | ⊥ =>
    exfalso
    exact False.elim (hv i hvi)
  | (f : F) =>
    apply EF.zero_smul_coe

lemma Matrix.has_bot_dotProd_nneg {v : I → F∞} {i : I} (hvi : v i = ⊥) (w : I → { a : F // 0 ≤ a }) :
    v ᵥ⬝ w = (⊥ : F∞) := by
  simp only [Matrix.dotProd, Finset.sum, Multiset.sum_eq_EF_bot_iff, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  use i
  rw [hvi]
  rfl

lemma Matrix.no_bot_dotProd_nneg {v : I → F∞} (hv : ∀ i, v i ≠ ⊥) (w : I → { a : F // 0 ≤ a }) :
    v ᵥ⬝ w ≠ (⊥ : F∞) := by
  simp only [Matrix.dotProd, Finset.sum]
  intro contr
  simp only [Multiset.sum_eq_EF_bot_iff, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at contr
  obtain ⟨i, hi⟩ := contr
  match hvi : v i with
  | ⊥ => exact hv i hvi
  | ⊤ => rw [hvi] at hi; exact EF.smul_top_neq_bot (w i) hi
  | (f : F) => rw [hvi] at hi; exact EF.smul_coe_neq_bot (w i) f hi

lemma Matrix.no_bot_has_top_dotProd_pos {v : I → F∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    (w : I → { a : F // 0 ≤ a }) (hwi : 0 < w i) :
    v ᵥ⬝ w = ⊤ := by
  apply Multiset.sum_eq_EF_top
  · rw [Multiset.mem_map]
    use i
    constructor
    · rw [Finset.mem_val]
      apply Finset.mem_univ
    · rw [hvi]
      exact EF.pos_smul_top hwi
  · intro contr
    rw [Multiset.mem_map] at contr
    obtain ⟨b, -, hb⟩ := contr
    exact EF.smul_nonbot_neq_bot (w b) (hv b) hb

lemma Matrix.no_bot_has_top_dotProd_le {v : I → F∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    (w : I → { a : F // 0 ≤ a }) {f : F} (hq : v ᵥ⬝ w ≤ f) :
    w i ≤ 0 := by
  by_contra! contr
  rw [Matrix.no_bot_has_top_dotProd_pos hv hvi w contr, top_le_iff] at hq
  exact EF.coe_neq_top f hq

lemma Matrix.no_bot_has_top_dotProd_nneg_le {v : I → F∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    (w : I → { a : F // 0 ≤ a }) {f : F} (hq : v ᵥ⬝ w ≤ f) :
    w i = 0 :=
  eq_of_le_of_le (Matrix.no_bot_has_top_dotProd_le hv hvi w hq) (w i).property

lemma Matrix.dotProd_zero_le_zero (v : I → F∞) :
    v ᵥ⬝ (0 : I → { a : F // 0 ≤ a }) ≤ (0 : F∞) := by
  if hv : ∀ i, v i ≠ ⊥ then
    rw [Matrix.no_bot_dotProd_zero hv]
  else
    push_neg at hv
    rw [Matrix.has_bot_dotProd_nneg]
    · apply bot_le
    · exact hv.choose_spec

lemma Matrix.mulWeig_zero_le_zero (M : Matrix I J F∞) :
    M ₘ* (0 : J → { a : F // 0 ≤ a }) ≤ (0 : I → F∞) := by
  intro i
  apply Matrix.dotProd_zero_le_zero

end hetero_matrix_products_EF


section extended_Farkas

set_option maxHeartbeats 666666 in
/-- Just like `inequalityFarkas_neg` but for `A` and `b` over extended rationals;
    neither is a generalization of the other. -/
theorem extendedFarkas [DecidableEq I]
    -- The matrix (LHS)
    (A : Matrix I J F∞)
    -- The upper-bounding vector (RHS)
    (b : I → F∞)
    -- `A` must not have both `⊥` and `⊤` in the same row
    (hA : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤))
    -- `A` must not have both `⊥` and `⊤` in the same column
    (hAT : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤))
    -- `A` must not have `⊤` on any row where `b` has `⊤`
    (hAb : ¬∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤)
    -- `A` must not have `⊥` on any row where `b` has `⊥`
    (hAb' : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥) :
    --
    (∃ x : J → { a : F // 0 ≤ a }, A ₘ* x ≤ b) ≠ (∃ y : I → { a : F // 0 ≤ a }, -Aᵀ ₘ* y ≤ 0 ∧ b ᵥ⬝ y < 0) := by
    --
  if hbot : ∃ i : I, b i = ⊥ then
    obtain ⟨i, hi⟩ := hbot
    if hi' : (∀ j : J, A i j ≠ ⊥) then
      convert false_ne_true
      · rw [iff_false, not_exists]
        intro x hAxb
        specialize hAxb i
        rw [hi, le_bot_iff] at hAxb
        refine Matrix.no_bot_dotProd_nneg hi' x hAxb
      · rw [iff_true]
        use 0
        constructor
        · apply Matrix.mulWeig_zero_le_zero
        · rw [Matrix.has_bot_dotProd_nneg hi]
          exact EF.bot_lt_zero
    else
      push_neg at hi'
      exfalso
      apply hAb'
      exact ⟨i, hi', hi⟩
  else
    let I' : Type _ := { i : I // b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥ } -- non-tautological rows
    let J' : Type _ := { j : J // ∀ i' : I', A i'.val j ≠ ⊤ } -- columns that allow non-zero values
    let A' : Matrix I' J' F := -- the new matrix
      Matrix.of (fun i' : I' => fun j' : J' =>
        match matcha : A i'.val j'.val with
        | (f : F) => f
        | ⊥ => False.elim (i'.property.right j' matcha)
        | ⊤ => False.elim (j'.property i' matcha)
      )
    let b' : I' → F := -- the new RHS
      fun i' : I' =>
        match hbi : b i'.val with
        | (f : F) => f
        | ⊥ => False.elim (hbot ⟨i', hbi⟩)
        | ⊤ => False.elim (i'.property.left hbi)
    convert inequalityFarkas_neg A' b'
    · constructor
      · intro ⟨x, ineqalities⟩
        use (fun j' : J' => x j'.val)
        constructor
        · intro j'
          exact (x j'.val).property
        intro i'
        rw [←EF.coe_le_coe_iff]
        convert ineqalities i'.val; swap
        · simp only [b']
          split <;> rename_i hbi <;> simp only [hbi]
          · rfl
          · exfalso
            apply hbot
            use i'
            exact hbi
          · exfalso
            apply i'.property.left
            exact hbi
        simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.mulWeig, Matrix.dotProd]
        rw [Finset.sum_toE, Finset.univ_sum_of_zero_when_neg (fun j : J => ∀ i' : I', A i'.val j ≠ ⊤)]
        · congr
          ext j'
          rw [mul_comm]
          simp only [A', Matrix.of_apply]
          congr
          split <;> rename_i hAij <;> simp only [hAij]
          · rfl
          · exfalso
            apply i'.property.right
            exact hAij
          · exfalso
            apply j'.property
            exact hAij
        · intro j where_top
          push_neg at where_top
          obtain ⟨t, ht⟩ := where_top
          have hxj : x j = 0
          · obtain ⟨q, hq⟩ : ∃ q : F, b t = q
            · match hbt : b t.val with
              | (f : F) =>
                exact ⟨_, rfl⟩
              | ⊥ =>
                exfalso
                apply hbot
                use t
                exact hbt
              | ⊤ =>
                exfalso
                apply t.property.left
                exact hbt
            exact Matrix.no_bot_has_top_dotProd_nneg_le (t.property.right) ht x (hq ▸ ineqalities t.val)
          rw [hxj]
          apply EF.zero_smul_nonbot
          apply i'.property.right
      · intro ⟨x, hx, ineqalities⟩
        use (fun j : J => if hj : (∀ i' : I', A i'.val j ≠ ⊤) then ⟨x ⟨j, hj⟩, hx ⟨j, hj⟩⟩ else 0)
        intro i
        if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then
          convert EF.coe_le_coe_iff.mpr (ineqalities ⟨i, hi⟩)
          · unfold Matrix.mulVec Matrix.dotProduct Matrix.mulWeig Matrix.dotProd
            simp_rw [dite_smul]
            rw [Finset.sum_dite]
            convert add_zero _
            · apply Finset.sum_eq_zero
              intro j _
              apply EF.zero_smul_nonbot
              exact hi.right j.val
            · rw [←Finset.sum_coe_sort_eq_attach, Finset.sum_toE]
              apply Finset.subtype_univ_sum_eq_subtype_univ_sum
              · simp [Finset.mem_filter]
              · intro j hj _
                rw [mul_comm]
                simp only [A', Matrix.of_apply]
                split <;> rename_i hAij <;> simp only [hAij]
                · rfl
                · exfalso
                  apply hi.right
                  exact hAij
                · exfalso
                  exact hj ⟨i, hi⟩ hAij
          · simp only [b']
            split <;> rename_i hbi <;> simp only [hbi]
            · rfl
            · exfalso
              apply hbot
              use i
              exact hbi
            · exfalso
              apply hi.left
              exact hbi
        else
          push_neg at hi
          if hbi : b i = ⊤ then
            rw [hbi]
            apply le_top
          else
            obtain ⟨j, hAij⟩ := hi hbi
            convert_to ⊥ ≤ b i
            · apply Matrix.has_bot_dotProd_nneg hAij
            apply bot_le
    · constructor
      · intro ⟨y, ineqalities, sharpine⟩
        use (fun i' : I' => y i'.val)
        constructor
        · intro i'
          exact (y i'.val).property
        have h0 (i : I) (i_not_I' : ¬ (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥)) : y i = 0
        · by_contra contr
          have hyi : 0 < y i
          · cases lt_or_eq_of_le (y i).property with
            | inl hpos =>
              exact hpos
            | inr h0 =>
              exfalso
              apply contr
              ext
              exact h0.symm
          if bi_top : b i = ⊤ then
            have impos : b ᵥ⬝ y = ⊤
            · push_neg at hbot
              exact Matrix.no_bot_has_top_dotProd_pos hbot bi_top y hyi
            rw [impos] at sharpine
            exact not_top_lt sharpine
          else
            push_neg at i_not_I'
            obtain ⟨j, Aij_eq_bot⟩ := i_not_I' bi_top
            have htop : ((-Aᵀ) j) ᵥ⬝ y = ⊤
            · refine Matrix.no_bot_has_top_dotProd_pos ?_ (by simpa using Aij_eq_bot) y hyi
              intro k hk
              exact hAT ⟨j, ⟨i, Aij_eq_bot⟩, ⟨k, by simpa using hk⟩⟩
            have ineqality : ((-Aᵀ) j) ᵥ⬝ y ≤ 0 := ineqalities j
            rw [htop, top_le_iff] at ineqality
            exact EF.zero_neq_top ineqality
        constructor
        · have hnb (i : I) (i_not_I' : ¬ (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥)) (j : J) : (-Aᵀ) j i ≠ ⊥
          · intro contr
            have btop : ∃ j : J, A i j = ⊤
            · use j
              simpa using contr
            refine hA ⟨i, ?_, btop⟩
            push_neg at i_not_I'
            apply i_not_I'
            intro bi_eq_top
            apply hAb
            use i
          intro j'
          have inequality : ∑ i : I, y i • (-Aᵀ) j'.val i ≤ 0 := ineqalities j'
          rw [Finset.univ_sum_of_zero_when_neg (fun i : I => b i ≠ ⊤ ∧ ∀ (j : J), A i j ≠ ⊥)] at inequality
          · rw [←EF.coe_le_coe_iff]
            convert inequality
            simp only [Matrix.mulVec, Matrix.dotProduct]
            rw [Finset.sum_toE]
            congr
            ext i'
            simp only [A', Matrix.neg_apply, Matrix.transpose_apply, Matrix.of_apply]
            congr
            split <;> rename_i hAij <;> simp only [hAij]
            · rewrite [mul_comm]
              rfl
            · exfalso
              apply i'.property.right
              exact hAij
            · exfalso
              apply j'.property
              exact hAij
          · intro i hi
            rw [h0 i hi]
            apply EF.zero_smul_nonbot
            apply hnb
            exact hi
        · unfold Matrix.dotProd at sharpine
          rw [Finset.univ_sum_of_zero_when_neg (fun i : I => b i ≠ ⊤ ∧ ∀ (j : J), A i j ≠ ⊥)] at sharpine
          · unfold Matrix.dotProduct
            rw [←EF.coe_lt_coe_iff, Finset.sum_toE]
            convert sharpine with i'
            simp only [b']
            split <;> rename_i hbi <;> simp only [hbi]
            · rewrite [mul_comm]
              rfl
            · exfalso
              apply hbot
              use i'
              exact hbi
            · exfalso
              apply i'.property.left
              exact hbi
          · intro i hi
            rw [h0 i hi]
            apply EF.zero_smul_nonbot
            intro contr
            exact hbot ⟨i, contr⟩
      · intro ⟨y, hy, ineqalities, sharpine⟩
        use (fun i : I => if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then ⟨y ⟨i, hi⟩, hy ⟨i, hi⟩⟩ else 0)
        constructor
        · intro j
          if hj : (∀ i : I, A i j ≠ ⊤) then
            convert EF.coe_le_coe_iff.mpr (ineqalities ⟨j, fun i' => hj i'.val⟩)
            simp only [Matrix.mulWeig, Matrix.neg_apply, Matrix.transpose_apply, Pi.zero_apply]
            simp only [Matrix.dotProd, dite_smul]
            rw [Finset.sum_dite]
            convert add_zero _
            · apply Finset.sum_eq_zero
              intro i _
              apply EF.zero_smul_nonbot
              intro contr
              rw [Matrix.neg_apply, EF.neg_eq_bot_iff] at contr
              exact hj i contr
            · simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.neg_apply, Matrix.transpose_apply, EF.coe_neg]
              rw [Finset.sum_toE]
              apply Finset.subtype_univ_sum_eq_subtype_univ_sum
              · ext i
                simp
              · intro i hi hif
                rw [mul_comm]
                simp only [A', Matrix.neg_apply, Matrix.of_apply]
                congr
                split <;> rename_i hAij <;> simp only [hAij]
                · rfl
                · exfalso
                  apply hi.right
                  exact hAij
                · exfalso
                  apply hj
                  exact hAij
          else
            push_neg at hj
            obtain ⟨i, Aij_eq_top⟩ := hj
            unfold Matrix.mulWeig
            rw [Matrix.has_bot_dotProd_nneg]
            · apply bot_le
            · rwa [Matrix.neg_apply, Matrix.transpose_apply, EF.neg_eq_bot_iff]
        · convert EF.coe_lt_coe_iff.mpr sharpine
          unfold Matrix.dotProduct Matrix.dotProd
          simp_rw [dite_smul]
          rw [Finset.sum_dite]
          convert add_zero _
          · apply Finset.sum_eq_zero
            intro j _
            apply EF.zero_smul_nonbot
            intro contr
            exact hbot ⟨j.val, contr⟩
          · rw [←Finset.sum_coe_sort_eq_attach, Finset.sum_toE]
            apply Finset.subtype_univ_sum_eq_subtype_univ_sum
            · simp [Finset.mem_filter]
            · intro i hi _
              rw [mul_comm]
              simp only [b', Matrix.of_apply]
              split <;> rename_i hbi <;> simp only [hbi]
              · rfl
              · exfalso
                exact hbot ⟨i, hbi⟩
              · exfalso
                exact hi.left hbi

end extended_Farkas

#print axioms extendedFarkas
