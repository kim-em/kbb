import .determinants

universes u v

namespace units
variables {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

definition map : units α → units β :=
λ u, ⟨f u.val, f u.inv,
by rw [← is_monoid_hom.map_mul f, u.val_inv, is_monoid_hom.map_one f],
by rw [← is_monoid_hom.map_mul f, u.inv_val, is_monoid_hom.map_one f] ⟩

instance : is_group_hom (units.map f) :=
⟨λ a b, by ext; exact is_monoid_hom.map_mul f ⟩

end units

def GL (n : ℕ) (R : Type u) [ring R] := units (matrix (fin n) (fin n) R)

namespace GL

variables {n : ℕ} {R : Type u} [ring R]

instance : group (GL n R) := by unfold GL; apply_instance

def det : GL n R → units R := units.map matrix.det

instance : is_group_hom (det : GL n R → units R) := by unfold det; apply_instance

@[simp] lemma det_one : det (1 : GL n R) = 1 := is_group_hom.one det

@[simp] lemma det_mul (M : GL n R) (N : GL n R) : det (M * N) = det M * det N := is_group_hom.mul det M N

end GL

def SL (n : ℕ) (R : Type u) [ring R] := is_group_hom.ker (GL.det : GL n R → units R)
