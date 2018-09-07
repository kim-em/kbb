import group_theory.subgroup

universes u v

class is_monoid_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) : Prop :=
(map_one : f 1 = 1)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)

namespace units
variables {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

definition map : units α → units β :=
λ u, ⟨f u.val, f u.inv,
by rw [← is_monoid_hom.map_mul f, u.val_inv, is_monoid_hom.map_one f],
by rw [← is_monoid_hom.map_mul f, u.inv_val, is_monoid_hom.map_one f] ⟩

instance : is_group_hom (units.map f) :=
⟨λ a b, by ext; exact is_monoid_hom.map_mul f ⟩

end units