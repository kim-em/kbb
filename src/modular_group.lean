import tactic.ring
import tactic.tidy

@[tidy] meta def tidy_ring := `[ring]

structure SL2Z :=
(a b c d : ℤ)
(det : a * d - b * c = 1)

lemma one_one : (1 : ℤ) * 1 = 1 := by simp

instance : group SL2Z :=
begin refine
{ one := { a := 1, b := 0, c := 0, d := 1, det := by ring },
  mul := λ X Y, { a := X.a * Y.a + X.b * Y.c,
                  b := X.a * Y.b + X.b * Y.d,
                  c := X.c * Y.a + X.d * Y.c,
                  d := X.c * Y.b + X.d * Y.d,
                  det := begin 
                           conv { to_rhs, rw ← one_one, congr, rw ← X.det, skip, rw ← Y.det, }, 
                           ring 
                         end },
  inv := λ X, { a := X.d, b := - X.c, c := - X.b, d := X.a, det := begin rw ← X.det, ring end },
  ..
} ; tidy
end