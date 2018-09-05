import tactic.tidy
import group_theory.subgroup
import .matrices

universes u v

class is_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) : Prop :=
(map_one : f 1 = 1)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)

definition units.map {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f] :
units α → units β :=
λ u, ⟨f u.val, f u.inv,
by rw [← is_monoid_hom.map_mul f, u.val_inv, is_monoid_hom.map_one f],
by rw [← is_monoid_hom.map_mul f, u.inv_val, is_monoid_hom.map_one f] ⟩

instance units.map_is_group_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f] :
is_group_hom (units.map f) :=
⟨λ a b, begin
ext,
exact is_monoid_hom.map_mul f,
end⟩

namespace matrix
variables {n : ℕ} {R : Type u} [ring R]

definition det : matrix n n R → R := sorry

@[simp] lemma det_zero : det (0 : matrix n n R) = (0 : R) := sorry

@[simp] lemma det_one : det (1 : matrix n n R) = (1 : R) := sorry

@[simp] lemma det_mul (M : matrix n n R) (N : matrix n n R) : det (M * N) = det M * det N := sorry

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

end matrix

def GL (n : ℕ) (R : Type u) [ring R] := units (matrix n n R)

namespace GL

variables {n : ℕ} {R : Type u} [ring R]

instance : group (GL n R) := by unfold GL; apply_instance

def det : GL n R → units R := units.map matrix.det

instance : is_group_hom (det : GL n R → units R) := units.map_is_group_hom matrix.det

@[simp] lemma det_one : det (1 : GL n R) = 1 := is_group_hom.one det

@[simp] lemma det_mul (M : GL n R) (N : GL n R) : det (M * N) = det M * det N := is_group_hom.mul det M N

end GL

def SL (n : ℕ) (R : Type u) [ring R] := is_group_hom.ker (GL.det : GL n R → units R)
