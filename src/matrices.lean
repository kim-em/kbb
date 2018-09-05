import algebra.big_operators data.set.finite

def {u} matrix (m n : ℕ) (α : Type u) : Type u := fin m → fin n → α

namespace matrix
variables {l m n o : ℕ}
variables {α : Type*}

def ext {M N : matrix m n α} : (∀ i j, M i j = N i j) ↔ M = N :=
⟨λ h, funext $ λ i, funext $ λ j, h i j, λ h, by simp [h]⟩

@[extensionality] theorem ext' {M N : matrix m n α} : (∀ i j, M i j = N i j) → M = N :=
ext.mp

instance [has_zero α] : has_zero (matrix m n α) :=
⟨λ _ _, 0⟩

@[simp] theorem zero_val [has_zero α] {i j} : (0 : matrix m n α) i j = 0 :=
rfl

instance [has_zero α] [has_one α] : has_one (matrix n n α) :=
⟨λ i j, if i = j then 1 else 0⟩

theorem one_val [has_zero α] [has_one α] {i j} : (1 : matrix n n α) i j = if i = j then 1 else 0 :=
rfl

@[simp] theorem one_val_eq [has_zero α] [has_one α] {i} : (1 : matrix n n α) i i = 1 :=
by simp [one_val]

@[simp] theorem one_val_ne [has_zero α] [has_one α] {i j} (h : i ≠ j) : (1 : matrix n n α) i j = 0 :=
by simp [one_val, h]

instance [has_neg α] : has_neg (matrix m n α) :=
⟨λ M i j, - M i j⟩

instance [has_add α] : has_add (matrix m n α) :=
⟨λ M N i j, M i j + N i j⟩

@[simp] theorem add_val [has_add α] {M N : matrix m n α} {i j} :
  (M + N) i j = M i j + N i j :=
rfl

instance [add_semigroup α] : add_semigroup (matrix m n α) :=
{ add_assoc := λ L M N, ext' $ by simp,
  ..matrix.has_add }

instance [add_comm_semigroup α] : add_comm_semigroup (matrix m n α) :=
{ add_comm := λ M N, ext' $ by simp,
  ..matrix.add_semigroup }

instance [add_monoid α] : add_monoid (matrix m n α) :=
{ zero_add := λ M, ext' $ by simp,
  add_zero := λ M, ext' $ by simp,
  ..matrix.has_zero,
  ..matrix.has_add,
  ..matrix.add_semigroup }

instance [add_comm_monoid α] : add_comm_monoid (matrix m n α) :=
{ ..matrix.add_monoid,
  ..matrix.add_comm_semigroup }

protected def mul [has_mul α] [add_comm_monoid α] (M : matrix l m α) (N : matrix m n α) :
  matrix l n α :=
λ i k, finset.univ.sum (λ j, M i j * N j k)

@[simp] theorem mul_val [has_mul α] [add_comm_monoid α] {M : matrix l m α} {N : matrix m n α} {i k} :
  (M.mul N) i k = finset.univ.sum (λ j, M i j * N j k) :=
rfl

instance [has_mul α] [add_comm_monoid α] : has_mul (matrix n n α) :=
⟨matrix.mul⟩

@[simp] theorem mul_val' [has_mul α] [add_comm_monoid α] {M N : matrix n n α} {i k} :
  (M * N) i k = finset.univ.sum (λ j, M i j * N j k) :=
rfl

theorem mul_assoc [semiring α] (L : matrix l m α)
  (M : matrix m n α) (N : matrix n o α) : L.mul (M.mul N) = (L.mul M).mul N :=
funext $ λ i, funext $ λ k,
  calc finset.univ.sum (λ (j₁ : fin m), L i j₁ * finset.univ.sum (λ (j₂ : fin n), M j₁ j₂ * N j₂ k))
    = finset.univ.sum (λ (j₁ : fin m), finset.univ.sum (λ (j₂ : fin n), L i j₁ * M j₁ j₂ * N j₂ k)) :
      by congr; funext; rw finset.mul_sum; congr; funext; rw mul_assoc
    ... = finset.univ.sum (λ (j₂ : fin n), finset.univ.sum (λ (j₁ : fin m), L i j₁ * M j₁ j₂ * N j₂ k)) :
      by rw finset.sum_comm
    ... = finset.univ.sum (λ (j₂ : fin n), finset.univ.sum (λ (j₁ : fin m), L i j₁ * M j₁ j₂) * N j₂ k) :
      by congr; funext; rw ←finset.sum_mul

instance [semiring α] : semigroup (matrix n n α) :=
{ mul_assoc := λ L M N, (mul_assoc L M N).symm,
  ..matrix.has_mul }

theorem one_mul [semiring α] (M : matrix n n α) : (1 : matrix n n α).mul M = M :=
ext' $ λ i j,
have h : ∀ (j' : fin n), j' ∈ (finset.univ : finset (fin n)) → j' ∉ finset.singleton i → (1 : matrix n n α) i j' * M j' j = 0 :=
  λ j' h₁ h₂, by simp at h₂; simp [ne.symm h₂],
calc finset.univ.sum (λ i', (1 : matrix n n α) i i' * M i' j)
  = (finset.singleton i).sum (λ i', (1 : matrix n n α) i i' * M i' j) :
    (finset.sum_subset (finset.subset_univ (finset.singleton i)) h).symm
  ... = M i j :
    by simp

theorem mul_one [semiring α] (M : matrix n n α) : M.mul (1 : matrix n n α) = M :=
ext' $ λ i j,
have h : ∀ (j' : fin n), j' ∈ (finset.univ : finset (fin n)) → j' ∉ finset.singleton j → M i j' * (1 : matrix n n α) j' j = 0 :=
  λ j' h₁ h₂, by simp at h₂; simp [h₂],
calc finset.univ.sum (λ j',  M i j' * (1 : matrix n n α) j' j)
  = (finset.singleton j).sum (λ j', M i j' * (1 : matrix n n α) j' j) :
    (finset.sum_subset (finset.subset_univ (finset.singleton j)) h).symm
  ... = M i j :
    by simp

instance [semiring α] : monoid (matrix n n α) :=
{ one_mul := one_mul,
  mul_one := mul_one,
  ..matrix.has_one,
  ..matrix.has_mul,
  ..matrix.semigroup }

instance [ring α] : ring (matrix n n α) :=
{ add_left_neg := sorry,
  one := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  ..matrix.has_neg,
  ..matrix.has_zero,
  ..matrix.add_comm_monoid,
  ..matrix.monoid }

end matrix
