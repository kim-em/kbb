import .matrices

universes u v

variables {R : Type u} [ring R]

def det {n : ℕ} : matrix R n n → R := sorry

class is_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) : Prop :=
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_one : f 1 = 1)

instance det_homomorphic (n : ℕ) : is_monoid_hom (@det R _ n) := sorry

def GL (n:ℕ) (R : Type) [ring R] := units (matrix R n n)

instance GL_group (n:ℕ ) ( R : Type) [ring R] : group (GL n R):=
begin
  unfold GL,
  apply_instance,
end 


