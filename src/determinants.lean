import tactic.tidy
import group_theory.subgroup
import .matrices

universes u v

class is_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) : Prop :=
(map_one : f 1 = 1)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)

definition units.map {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f] :
units α → units β :=
λ u, ⟨f u.val, f u.inv, sorry, sorry⟩

instance units.map_is_group_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f] :
is_group_hom (units.map f) :=
⟨λ a b, begin
ext,
exact is_monoid_hom.map_mul f,
end⟩

namespace matrix
variables {R : Type u} [ring R]

def det {n : ℕ} : matrix R n n → R := sorry

lemma det_zero {n : ℕ} : det (0 : matrix R n n) = 0 := sorry

lemma det_one {n : ℕ} : det (1 : matrix R n n) = 1 := sorry

lemma det_mul {n : ℕ} (M : matrix R n n) (N : matrix R n n) : det (M * N) = det M * det N := sorry

instance det_homomorphic (n : ℕ) : is_monoid_hom (det : matrix R n n → R) :=
{ map_one := det_one,
  map_mul := det_mul }

end matrix

def GL (n : ℕ) (R : Type u) [ring R] := units (matrix R n n)

namespace GL

variables {n : ℕ} {R : Type u} [ring R]

instance : group (GL n R) := by unfold GL; apply_instance

def det : GL n R → units R := units.map matrix.det

instance : is_group_hom (det : GL n R → units R) := units.map_is_group_hom matrix.det

lemma det_one : det (1 : GL n R) = 1 := is_group_hom.one det

lemma det_mul (M : GL n R) (N : GL n R) : det (M * N) = det M * det N := is_group_hom.mul det M N

end GL

def SL (n : ℕ) (R : Type u) [ring R] := is_group_hom.ker (GL.det : GL n R → units R)
