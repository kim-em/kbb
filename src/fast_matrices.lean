import tactic.tidy
import data.vector
import .matrices

def vector.mk {α : Type*} {n : ℕ} (l : list α) (pr : l.length = n) :
  vector α n := ⟨l, pr⟩

notation `![` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) :=
  vector.mk l rfl

def {u} fast_matrix (m n : ℕ) (α : Type u) : Type u := vector (vector α n) m

example : fast_matrix 2 3 ℤ := 
![![ 1 , 1,  5 ],
  ![ 0 , 1, -2 ]]
