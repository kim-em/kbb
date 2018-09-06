import tactic.tidy
import group_theory.subgroup
import .matrices

universes u v

class is_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) : Prop :=
(map_one : f 1 = 1)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)

namespace matrix
variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [ring R]

definition det : matrix n n R → R := sorry

@[simp] lemma det_zero : det (0 : matrix n n R) = (0 : R) := sorry

@[simp] lemma det_one : det (1 : matrix n n R) = (1 : R) := sorry

@[simp] lemma det_mul (M : matrix n n R) (N : matrix n n R) : det (M * N) = det M * det N := sorry

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

end matrix
