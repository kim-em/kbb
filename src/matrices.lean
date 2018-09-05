import algebra.big_operators data.set.finite

def matrix (m n : ℕ) (α : Type*) := fin m → fin n → α

namespace matrix
variables {l m n o : ℕ}
variables {α : Type*} [ring α]

instance : has_zero (matrix m n α) :=
⟨λ _ _, 0⟩

instance : has_neg (matrix m n α) :=
⟨λ M x y, - M x y⟩

instance : has_add (matrix m n α) :=
⟨λ M N x y, M x y + N x y⟩

@[simp] theorem add_val {M N : matrix m n α} {x : fin m} {y : fin n} : (M + N) x y = M x y + N x y :=
rfl

theorem add_assoc (L : matrix m n α) (M : matrix m n α) (N : matrix m n α) :
  L + (M + N) = (L + M) + N :=
funext $ λ x, funext $ λ y, by simp

def mul (M : matrix l m α) (N : matrix m n α) : matrix l n α :=
λ x z, finset.univ.sum (λ y, M x y * N y z)

@[simp] theorem mul_val {M : matrix l m α} {N : matrix m n α} {x : fin l} {z : fin n} :
  (M.mul N) x z = finset.univ.sum (λ y, M x y * N y z) :=
rfl

theorem mul_assoc (L : matrix l m α) (M : matrix m n α) (N : matrix n o α) :
  L.mul (M.mul N) = (L.mul M).mul N :=
funext $ λ x, funext $ λ z,
  calc finset.univ.sum (λ (y₁ : fin m), L x y₁ * finset.univ.sum (λ (y₂ : fin n), M y₁ y₂ * N y₂ z))
    = finset.univ.sum (λ (y₁ : fin m), finset.univ.sum (λ (y₂ : fin n), L x y₁ * M y₁ y₂ * N y₂ z)) :
      by congr; funext; rw finset.mul_sum; congr; funext; rw mul_assoc
    ... = finset.univ.sum (λ (y₂ : fin n), finset.univ.sum (λ (y₁ : fin m), L x y₁ * M y₁ y₂ * N y₂ z)) :
      by rw finset.sum_comm
    ... = finset.univ.sum (λ (y₂ : fin n), finset.univ.sum (λ (y₁ : fin m), L x y₁ * M y₁ y₂) * N y₂ z) :
      by congr; funext; rw ←finset.sum_mul

instance (n : ℕ) : ring (matrix n n α) := sorry

end matrix
