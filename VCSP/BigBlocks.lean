import Mathlib.Data.Matrix.Block


def BigBlockMatrix {R α β : Type*} [Fintype α] [Fintype β] {m : α → Type*} {n : β → Type*}
    (M : Π a : α, Π b : β, Matrix (m a) (n b) R) :
    Matrix (Σ a : α, m a) (Σ b : β, n b) R :=
  Matrix.of
    (fun (i : (Σ a : α, m a)) (j : (Σ b : β, n b)) => M i.fst j.fst i.snd j.snd)

private def exampleBigBlockMatrix {R m₀ m₁ n₀ n₁ : Type}
    (A : Matrix m₀ n₀ R) (B : Matrix m₀ n₁ R) (C : Matrix m₁ n₀ R) (D : Matrix m₁ n₁ R) :=
    @BigBlockMatrix R (Fin 2) (Fin 2) (Fin.fintype 2) (Fin.fintype 2) ![m₀, m₁] ![n₀, n₁]
      (fun m : Fin 2 => fun n : Fin 2 =>
        if hm : m = 0 then
          if hn : n = 0 then
            (by convert A; simp [hm]; simp [hn])
          else
            (by convert B; simp [hm]; simp [Fin.eq_one_of_neq_zero n hn])
        else
          if hn : n = 0 then
            (by convert C; simp [Fin.eq_one_of_neq_zero m hm]; simp [hn])
          else
            (by convert D; simp [Fin.eq_one_of_neq_zero m hm]; simp [Fin.eq_one_of_neq_zero n hn])
      )
