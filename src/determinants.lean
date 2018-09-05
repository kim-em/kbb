import tactic.subtype_instance
import .matrices

universes u v

variables {R : Type u} [ring R]

def matrix.det {n : ℕ} : matrix R n n → R := sorry

open matrix

class is_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) : Prop :=
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_one : f 1 = 1)

instance det_homomorphic (n : ℕ) : is_monoid_hom (@det R _ n) := sorry

variables (R)

def GL (n : ℕ) (R : Type u) [ring R] := units (matrix R n n)

instance GL_group (n : ℕ) (R : Type u) [ring R] : group (GL n R) := by unfold GL; apply_instance

def SL (n : ℕ) (R : Type u) [ring R] := {M : GL n R // det M.val = (1 : R)}

instance SL_group (n : ℕ) (R : Type u) [ring R] : group (SL n R) := sorry
