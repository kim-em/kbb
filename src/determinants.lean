import group_theory.subgroup
import .matrices

universes u v

section
variables {R : Type u} [ring R]

def matrix.det {n : ℕ} : matrix R n n → R := sorry

open matrix

class is_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) : Prop :=
(map_mul : ∀ (x y), f (x * y) = f x * f y)
(map_one : f 1 = 1)

instance det_homomorphic (n : ℕ) : is_monoid_hom (@det R _ n) := sorry
end

section
open matrix
variables (n : ℕ) (R : Type u) [ring R]

def GL  := units (matrix R n n)

instance GL_group : group (GL n R) := by unfold GL; apply_instance

def SL := {M : GL n R | det M.val = (1 : R)}

instance SL_subgroup : is_subgroup (SL n R) :=
begin
  refine_struct {..},
  { exact is_monoid_hom.map_one det },
  { intros a b a_in b_in,
    have := is_monoid_hom.map_mul det a.val b.val,
    dsimp [SL] at *,
    rw [a_in, b_in] at this,
    simpa using this },
  { intros a a_in,
    have := is_monoid_hom.map_mul det a.val a⁻¹.val,
    dsimp [SL] at *,
    rw [a_in] at this,
    simp at this,
    rw ←this,
    sorry}
end

instance SL_group (n : ℕ) (R : Type u) [ring R] : group (SL n R) := 
by apply_instance
end