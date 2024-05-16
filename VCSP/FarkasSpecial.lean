import VCSP.ExtendedRationals
import VCSP.FarkasBartl


section extrasERat

notation "ℚ∞" => ERat

-- Richard Copley pointed out that we need this homomorphism:
def Rat.toERatAddHom : ℚ →+ ℚ∞ := ⟨⟨Rat.toERat, ERat.coe_zero⟩, ERat.coe_add⟩

instance : SMulZeroClass ℚ ℚ∞ where
  smul (c : ℚ) (a : ℚ∞) := c.toERat * a
  smul_zero (c : ℚ) := by
    show (c * 0).toERat = (0 : ℚ∞)
    rewrite [mul_zero]
    rfl

lemma zero_smul_ERat_neq_bot {a : ℚ∞} (ha : a ≠ ⊥) : (0 : ℚ) • a = 0 := ERat.zero_mul ha

lemma smul_eq_ERat_bot_iff_of_nng {c : ℚ} {a : ℚ∞} (hc : 0 ≤ c) : c • a = ⊥ ↔ a = ⊥ := by
  constructor
  · intro hca
    change hca to c.toERat * a = ⊥
    match a with
    | ⊥ => rfl
    | ⊤ =>
      exfalso
      cases lt_or_eq_of_le hc with
      | inl c_pos =>
        rw [ERat.coe_mul_top_of_pos c_pos] at hca
        exact top_ne_bot hca
      | inr c_zero =>
        rw [←c_zero, ERat.coe_zero, ERat.zero_mul top_ne_bot] at hca
        exact ERat.bot_ne_zero hca.symm
    | (q : ℚ) =>
      exfalso
      change hca to (c * q).toERat = ⊥
      exact ERat.coe_ne_bot _ hca
  · intro ha
    rw [ha]
    exact ERat.coe_mul_bot_of_nng hc

lemma Finset.sum_toERat {ι : Type*} [Fintype ι] (s : Finset ι) (f : ι → ℚ) :
    (s.sum f).toERat = s.sum (fun i : ι => (f i).toERat) :=
  map_sum Rat.toERatAddHom f s

lemma Multiset.sum_eq_ERat_bot_iff (s : Multiset ℚ∞) : s.sum = (⊥ : ℚ∞) ↔ ⊥ ∈ s := by
  constructor <;> intro hs
  · induction s using Multiset.induction with
    | empty =>
      exfalso
      rw [Multiset.sum_zero] at hs
      exact ERat.zero_ne_bot hs
    | @cons a m ih =>
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
          rw [ERat.top_add_top] at hs
          exact top_ne_bot hs
        | (q : ℚ) =>
          exfalso
          rw [hm] at hs
          change hs to ⊤ + q.toERat = ⊥
          rw [ERat.top_add_coe] at hs
          exact top_ne_bot hs
      | (q : ℚ) =>
        match hm : m.sum with
        | ⊥ =>
          right
          exact ih hm
        | ⊤ =>
          exfalso
          rw [hm] at hs
          change hs to q.toERat + ⊤ = ⊥
          rw [ERat.coe_add_top] at hs
          exact top_ne_bot hs
        | (_ : ℚ) =>
          exfalso
          rw [hm] at hs
          exact ERat.coe_ne_bot _ hs
  · induction s using Multiset.induction with
    | empty =>
      exfalso
      exact Multiset.not_mem_zero ⊥ hs
    | @cons a m ih =>
      rw [Multiset.sum_cons]
      rw [Multiset.mem_cons] at hs
      cases hs with
      | inl ha => rw [←ha, ERat.bot_add]
      | inr hm => rw [ih hm, ERat.add_bot]

lemma Multiset.sum_eq_ERat_top {s : Multiset ℚ∞} (htop : ⊤ ∈ s) (hbot : ⊥ ∉ s) :
    s.sum = (⊤ : ℚ∞) := by
  induction s using Multiset.induction with
  | empty =>
    exfalso
    exact Multiset.not_mem_zero ⊤ htop
  | @cons a m ih =>
    rw [Multiset.sum_cons]
    rw [Multiset.mem_cons] at htop
    cases htop with
    | inl ha =>
      rw [←ha]
      match hm : m.sum with
      | (q : ℚ) => rfl
      | ⊤ => rfl
      | ⊥ =>
        exfalso
        apply hbot
        rw [Multiset.mem_cons]
        right
        rw [←Multiset.sum_eq_ERat_bot_iff]
        exact hm
    | inr hm =>
      rw [ih hm (by aesop)]
      match a with
      | (q : ℚ) => rfl
      | ⊤ => rfl
      | ⊥ => simp at hbot

end extrasERat


open scoped Matrix
variable {I J : Type} [Fintype I] [Fintype J]


section heteroMatrixProductsDefs
variable {α γ : Type*} [AddCommMonoid α] [SMul γ α] -- elements come from `α` but weights (coefficients) from `γ`

/-- `Matrix.dotProd v w` is the sum of the element-wise products `w i • v i` akin the dot product but heterogeneous
    (mnemonic: "vector times weights").
    Note that the order of arguments (also with the infix notation) is opposite than in the `SMul` it builds upon. -/
def Matrix.dotProd (v : I → α) (w : I → γ) : α :=
  Finset.univ.sum (fun i : I => w i • v i)

infixl:72 " ᵥ⬝ " => Matrix.dotProd

/-- `Matrix.mulWeig M w` is the heterogeneous analogue of the matrix-vector product `Matrix.mulVec M v`
    (mnemonic: "matrix times weights").
    Note that the order of arguments (also with the infix notation) is opposite than in the `SMul` it builds upon. -/
def Matrix.mulWeig (M : Matrix I J α) (w : J → γ) (i : I) : α :=
  M i ᵥ⬝ w

infixr:73 " ₘ* " => Matrix.mulWeig

end heteroMatrixProductsDefs


section heteroMatrixProductsLemmasERat

lemma Matrix.no_bot_dotProd_zero {v : I → ℚ∞} (hv : ∀ i, v i ≠ ⊥) :
    v ᵥ⬝ (0 : I → ℚ) = (0 : ℚ∞) := by
  apply Finset.sum_eq_zero
  intro i _
  rw [Pi.zero_apply]
  match hvi : v i with
  | ⊤ => rfl
  | ⊥ => exact False.elim (hv i hvi)
  | (q : ℚ) =>
    show (0 * q).toERat = (0 : ℚ∞)
    rewrite [zero_mul]
    rfl

lemma Matrix.has_bot_dotProd_nng {v : I → ℚ∞} {i : I} (hvi : v i = ⊥) {w : I → ℚ} (hw : 0 ≤ w) :
    v ᵥ⬝ w = (⊥ : ℚ∞) := by
  simp only [Matrix.dotProd, Finset.sum, Multiset.sum_eq_ERat_bot_iff, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  use i
  rw [hvi]
  apply ERat.bot_mul_coe_of_nng
  apply hw

lemma Matrix.no_bot_dotProd_nng {v : I → ℚ∞} (hv : ∀ i, v i ≠ ⊥) {w : I → ℚ} (hw : 0 ≤ w) :
    v ᵥ⬝ w ≠ (⊥ : ℚ∞) := by
  simp only [Matrix.dotProd, Finset.sum]
  intro contr
  simp only [Multiset.sum_eq_ERat_bot_iff, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at contr
  obtain ⟨i, hi⟩ := contr
  rw [smul_eq_ERat_bot_iff_of_nng (hw i)] at hi
  apply hv
  exact hi

lemma Matrix.no_bot_has_top_dotProd_pos {v : I → ℚ∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    {w : I → ℚ} (hw : 0 ≤ w) (hwi : 0 < w i) :
    v ᵥ⬝ w = ⊤ := by
  apply Multiset.sum_eq_ERat_top
  · rw [Multiset.mem_map]
    use i
    constructor
    · rw [Finset.mem_val]
      apply Finset.mem_univ
    · rw [hvi]
      exact ERat.coe_mul_top_of_pos hwi
  · intro contr
    rw [Multiset.mem_map] at contr
    obtain ⟨b, -, hb⟩ := contr
    change hb to (w b).toERat * v b = ⊥
    match hvb : v b with
    | ⊥ =>
      apply hv
      exact hvb
    | ⊤ =>
      rw [hvb] at hb
      change hb to (w b).toERat * ⊤ = ⊥
      if hwb : 0 < w b then
        rw [ERat.coe_mul_top_of_pos hwb] at hb
        exact top_ne_bot hb
      else
        rw [←eq_of_le_of_not_lt (hw b) hwb, Pi.zero_apply, ERat.coe_zero, ERat.zero_mul top_ne_bot] at hb
        exact ERat.zero_ne_bot hb
    | (q : ℚ) =>
      rw [hvb] at hb
      exact ERat.coe_ne_bot (w b * q) hb

lemma Matrix.no_bot_has_top_dotProd_le {v : I → ℚ∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    {w : I → ℚ} (hw : 0 ≤ w) {q : ℚ} (hq : v ᵥ⬝ w ≤ q.toERat) :
    w i ≤ 0 := by
  by_contra! contr
  rw [Matrix.no_bot_has_top_dotProd_pos hv hvi hw contr, top_le_iff] at hq
  exact ERat.coe_ne_top q hq

lemma Matrix.no_bot_has_top_dotProd_nng_le {v : I → ℚ∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    {w : I → ℚ} (hw : 0 ≤ w) {q : ℚ} (hq : v ᵥ⬝ w ≤ q.toERat) :
    w i = 0 :=
  eq_of_le_of_le (Matrix.no_bot_has_top_dotProd_le hv hvi hw hq) (hw i)

lemma Matrix.dotProd_zero_le_zero (v : I → ℚ∞) :
    v ᵥ⬝ (0 : I → ℚ) ≤ (0 : ℚ∞) := by
  if hv : ∀ i, v i ≠ ⊥ then
    rw [Matrix.no_bot_dotProd_zero hv]
  else
    push_neg at hv
    rw [Matrix.has_bot_dotProd_nng]
    · apply bot_le
    · exact hv.choose_spec
    · rfl

lemma Matrix.no_bot_mulWeig_zero {A : Matrix I J ℚ∞} (hA : ∀ i, ∀ j, A i j ≠ ⊥) :
    A ₘ* (0 : J → ℚ) = (0 : I → ℚ∞) := by
  ext
  apply Matrix.no_bot_dotProd_zero
  apply hA

lemma Matrix.mulWeig_zero_le_zero (A : Matrix I J ℚ∞) :
    A ₘ* (0 : J → ℚ) ≤ (0 : I → ℚ∞) := by
  intro i
  apply Matrix.dotProd_zero_le_zero

end heteroMatrixProductsLemmasERat


section specialFarkas

/-- `A` must not have both `⊥` and `⊤` on the same row. -/
def Matrix.Good (A : Matrix I J ℚ∞) : Prop :=
  ¬ (∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤))

/-- `A` must not have `⊥` on any row where `b` has `⊥`. -/
def Matrix.Good' (A : Matrix I J ℚ∞) (b : I → ℚ∞) : Prop :=
  ¬ (∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥)

/-- `A` must not have `⊤` on any row where `b` has `⊤`. -/
def Matrix.Good'' (A : Matrix I J ℚ∞) (b : I → ℚ∞) : Prop :=
  ¬ (∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤)

set_option maxHeartbeats 666666 in
/-- Just like `mainFarkas` but for `A` and `b` over extended rationals; neither is generalization of the other. -/
theorem extendedFarkas {A : Matrix I J ℚ∞} {b : I → ℚ∞}
    (hA : A.Good) (hAT : Aᵀ.Good) (hAb' : A.Good' b) (hAb : A.Good'' b) :
    (∃ x : J → ℚ, 0 ≤ x ∧ A ₘ* x ≤ b) ≠ (∃ y : I → ℚ, 0 ≤ y ∧ -Aᵀ ₘ* y ≤ 0 ∧ b ᵥ⬝ y < 0) := by
  if hbot : ∃ i : I, b i = ⊥ then
    obtain ⟨i, hi⟩ := hbot
    if hi' : (∀ j : J, A i j ≠ ⊥) then
      convert false_ne_true
      · rw [iff_false, not_exists]
        intro x ⟨hx, hAxb⟩
        specialize hAxb i
        rw [hi, le_bot_iff] at hAxb
        refine Matrix.no_bot_dotProd_nng hi' hx hAxb
      · rw [iff_true]
        use 0
        constructor
        · rfl
        constructor
        · apply Matrix.mulWeig_zero_le_zero
        · rw [Matrix.has_bot_dotProd_nng hi (by rfl)]
          exact ERat.bot_lt_zero
    else
      push_neg at hi'
      exfalso
      apply hAb'
      exact ⟨i, hi', hi⟩
  else
    let I' : Type _ := { i : I // b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥ } -- non-tautological rows
    let J' : Type _ := { j : J // ∀ i' : I', A i'.val j ≠ ⊤ } -- columns that allow non-zero values
    let A' : Matrix I' J' ℚ := -- the new matrix
      Matrix.of (fun i' : I' => fun j' : J' =>
        match matcha : A i'.val j'.val with
        | (q : ℚ) => q
        | ⊥ => False.elim (i'.property.right j' matcha)
        | ⊤ => False.elim (j'.property i' matcha)
      )
    let b' : I' → ℚ := -- the new RHS
      fun i' : I' =>
        match hbi : b i'.val with
        | (q : ℚ) => q
        | ⊥ => False.elim (hbot ⟨i', hbi⟩)
        | ⊤ => False.elim (i'.property.left hbi)
    convert mainFarkas A' b'
    · constructor <;> intro ⟨x, hx, ineqalities⟩
      · use (fun j' : J' => x j'.val)
        constructor
        · intro j'
          exact hx j'.val
        intro i'
        rw [←ERat.coe_le_coe_iff]
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
        rw [Finset.sum_toERat]
        show
          Finset.univ.sum (fun j' : J' => (A' i' j' * x j'.val).toERat) =
          Finset.univ.sum (fun j : J => (x j).toERat * A i'.val j)
        rw [Finset.univ_sum_of_zero_when_neg (fun j : J => ∀ i' : I', A i'.val j ≠ ⊤)]
        · congr
          ext j'
          rw [mul_comm]
          simp only [A', Matrix.of_apply, ERat.coe_mul]
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
          · obtain ⟨q, hq⟩ : ∃ q : ℚ, b t = q.toERat
            · match hbt : b t.val with
              | (q : ℚ) =>
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
            exact Matrix.no_bot_has_top_dotProd_nng_le (t.property.right) ht hx (hq ▸ ineqalities t.val)
          rw [hxj]
          apply ERat.zero_mul
          apply i'.property.right
      · use (fun j : J => if hj : (∀ i' : I', A i'.val j ≠ ⊤) then x ⟨j, hj⟩ else 0)
        constructor
        · intro j
          if hj : (∀ i' : I', A i'.val j ≠ ⊤) then
            convert hx ⟨j, hj⟩
            simp [hj]
          else
            aesop
        intro i
        if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then
          convert ERat.coe_le_coe_iff.mpr (ineqalities ⟨i, hi⟩)
          · unfold Matrix.mulVec Matrix.dotProduct Matrix.mulWeig Matrix.dotProd
            simp_rw [dite_smul]
            rw [Finset.sum_dite]
            convert add_zero _
            · apply Finset.sum_eq_zero
              intro j _
              apply zero_smul_ERat_neq_bot
              exact hi.right j.val
            · rw [←Finset.sum_coe_sort_eq_attach, Finset.sum_toERat]
              apply Finset.subtype_univ_sum_eq_subtype_univ_sum
              · simp [Finset.mem_filter]
              · intro j hj _
                rw [mul_comm, ERat.coe_mul]
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
            · apply Matrix.has_bot_dotProd_nng hAij
              intro _
              aesop
            apply bot_le
    · constructor <;> intro ⟨y, hy, ineqalities, sharpine⟩
      · use (fun i' : I' => y i'.val)
        constructor
        · intro i'
          exact hy i'.val
        have h0 (i : I) (i_not_I' : ¬ (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥)) : y i = 0
        · by_contra contr
          have hyi : 0 < y i
          · cases lt_or_eq_of_le (hy i) with
            | inl hpos =>
              exact hpos
            | inr h0 =>
              exfalso
              apply contr
              exact h0.symm
          if bi_top : b i = ⊤ then
            have impos : b ᵥ⬝ y = ⊤
            · push_neg at hbot
              exact Matrix.no_bot_has_top_dotProd_pos hbot bi_top hy hyi
            rw [impos] at sharpine
            exact not_top_lt sharpine
          else
            push_neg at i_not_I'
            obtain ⟨j, Aij_eq_bot⟩ := i_not_I' bi_top
            have htop : ((-Aᵀ) j) ᵥ⬝ y = ⊤
            · refine Matrix.no_bot_has_top_dotProd_pos ?_ (by simpa using Aij_eq_bot) hy hyi
              intro k hk
              exact hAT ⟨j, ⟨i, Aij_eq_bot⟩, ⟨k, by simpa using hk⟩⟩
            have ineqality : ((-Aᵀ) j) ᵥ⬝ y ≤ 0 := ineqalities j
            rw [htop, top_le_iff] at ineqality
            exact ERat.top_ne_zero ineqality.symm
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
          have inequality : Finset.univ.sum (fun i : I => y i • (-Aᵀ) j'.val i) ≤ 0 := ineqalities j'
          rw [Finset.univ_sum_of_zero_when_neg (fun i : I => b i ≠ ⊤ ∧ ∀ (j : J), A i j ≠ ⊥)] at inequality
          · rw [←ERat.coe_le_coe_iff]
            convert inequality
            simp only [Matrix.mulVec, Matrix.dotProduct]
            rw [Finset.sum_toERat]
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
            apply ERat.zero_mul
            apply hnb
            exact hi
        · unfold Matrix.dotProd at sharpine
          rw [Finset.univ_sum_of_zero_when_neg (fun i : I => b i ≠ ⊤ ∧ ∀ (j : J), A i j ≠ ⊥)] at sharpine
          · unfold Matrix.dotProduct
            rw [←ERat.coe_lt_coe_iff, Finset.sum_toERat]
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
            apply ERat.zero_mul
            intro contr
            exact hbot ⟨i, contr⟩
      · use (fun i : I => if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then y ⟨i, hi⟩ else 0)
        have nonneg : 0 ≤ (fun i : I => if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then y ⟨i, hi⟩ else 0)
        · intro i
          if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then
            convert hy ⟨i, hi⟩
            simp [hi]
          else
            aesop
        constructor
        · exact nonneg
        constructor
        · intro j
          if hj : (∀ i : I, A i j ≠ ⊤) then
            convert ERat.coe_le_coe_iff.mpr (ineqalities ⟨j, fun i' => hj i'.val⟩)
            simp only [Matrix.mulWeig, Matrix.neg_apply, Matrix.transpose_apply, Pi.zero_apply]
            simp only [Matrix.dotProd, dite_smul]
            rw [Finset.sum_dite]
            convert add_zero _
            apply Finset.sum_eq_zero
            intro i _
            apply zero_smul_ERat_neq_bot
            intro contr
            save
            rw [Matrix.neg_apply, ERat.neg_eq_bot_iff] at contr
            exact hj i contr
            · simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.neg_apply, Matrix.transpose_apply, ERat.coe_neg]
              rw [Finset.sum_toERat]
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
            rw [Matrix.has_bot_dotProd_nng]
            · apply bot_le
            · rwa [Matrix.neg_apply, Matrix.transpose_apply, ERat.neg_eq_bot_iff]
            · exact nonneg
        · convert ERat.coe_lt_coe_iff.mpr sharpine
          unfold Matrix.dotProduct Matrix.dotProd
          simp_rw [dite_smul]
          rw [Finset.sum_dite]
          convert add_zero _
          · apply Finset.sum_eq_zero
            intro j _
            apply zero_smul_ERat_neq_bot
            intro contr
            exact hbot ⟨j.val, contr⟩
          · rw [←Finset.sum_coe_sort_eq_attach, Finset.sum_toERat]
            apply Finset.subtype_univ_sum_eq_subtype_univ_sum
            · simp [Finset.mem_filter]
            · intro i hi _
              rw [mul_comm, ERat.coe_mul]
              simp only [b', Matrix.of_apply]
              split <;> rename_i hbi <;> simp only [hbi]
              · rfl
              · exfalso
                exact hbot ⟨i, hbi⟩
              · exfalso
                exact hi.left hbi

#print axioms extendedFarkas

end specialFarkas
