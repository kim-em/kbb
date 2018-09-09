import tactic.ring
import tactic.tidy
import group_theory.group_action
import .matrix_groups

@[tidy] meta def tidy_ring := `[ring]

structure integral_matrices_with_determinant (m : ℤ) :=
(a b c d : ℤ)
(det : a * d - b * c = m)

@[extensionality]
theorem integral_matrices_with_determinant.ext (m : ℤ) :
  ∀ (A B : integral_matrices_with_determinant m)
  (H1 : A.a = B.a) (H2 : A.b = B.b) (H3 : A.c = B.c) (H4 : A.d = B.d),
  A = B
| ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ rfl rfl rfl rfl := rfl

def SL2Z := integral_matrices_with_determinant 1

instance : group SL2Z :=
{ mul := λ A B, ⟨A.a * B.a + A.b * B.c,
                A.a * B.b + A.b * B.d,
                A.c * B.a + A.d * B.c,
                A.c * B.b + A.d * B.d,
    calc  (A.a * B.a + A.b * B.c) * (A.c * B.b + A.d * B.d) - (A.a * B.b + A.b * B.d) * (A.c * B.a + A.d * B.c)
        = (A.a * A.d - A.b * A.c) * (B.a * B.d - B.b * B.c) : by ring
    ... = 1 : by rw [A.det, B.det, mul_one]⟩,
  mul_assoc := λ A B C, by cases A; cases B; cases C; ext; dsimp; ring,
  one := ⟨1, 0, 0, 1, rfl⟩,
  one_mul := λ A, by cases A; ext; change _ + _ = _; simp,
  mul_one := λ A, by cases A; ext; change _ + _ = _; simp,
  inv := λ A, ⟨A.d, -A.b, -A.c, A.a, by simpa [mul_comm] using A.det⟩,
  mul_left_inv := λ A, by cases A; ext; change _ + _ = _; simp at A_det; simp [mul_comm, A_det]; refl }

def SL2Z_M_ (m : ℤ) : SL2Z → integral_matrices_with_determinant m → integral_matrices_with_determinant m :=
λ X Y, {  a := X.a * Y.a + X.b * Y.c,
          b := X.a * Y.b + X.b * Y.d,
          c := X.c * Y.a + X.d * Y.c,
          d := X.c * Y.b + X.d * Y.d,
          det := begin
            conv { to_rhs, rw ← one_mul m, congr, rw ← X.det, skip, rw ← Y.det }, 
            ring
          end }

instance (m : ℤ) : is_group_action (SL2Z_M_ m) := sorry
