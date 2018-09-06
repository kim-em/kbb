import tactic.ring
import tactic.tidy
import group_theory.group_action
import .matrix_groups

@[tidy] meta def tidy_ring := `[ring]

structure integral_matrices_with_determinant (m : ℤ) :=
(a b c d : ℤ)
(det : a * d - b * c = m)

def SL2Z := integral_matrices_with_determinant 1

instance : group SL2Z := sorry

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
