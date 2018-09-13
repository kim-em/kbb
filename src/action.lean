import group_theory.group_action

variables {X : Type*} {G : Type*} [group G] (ρ : G → X → X) [is_group_action ρ]

lemma is_group_action.inverse_left (g : G) : (ρ g⁻¹) ∘ ρ g = id :=
begin
  ext x,
  change ρ g⁻¹ (ρ g x) =  x,
  rw ← is_monoid_action.mul ρ g⁻¹ g x,
  simp [is_monoid_action.one ρ]
end

lemma is_group_action.inverse_right (g : G) : (ρ g) ∘ ρ g⁻¹ = id :=
by simpa using is_group_action.inverse_left ρ g⁻¹

def action_rel : setoid X :=
⟨λ x y, ∃ g, ρ g x = y, ⟨λ x, ⟨(1 : G),  is_monoid_action.one ρ x⟩,
  begin
  { split,
    { rintros x y ⟨g, h⟩,
      existsi g⁻¹,
      rw ←h,
      exact congr_fun (is_group_action.inverse_left ρ g) x },
    { rintros x y z ⟨g, h⟩ ⟨g', h'⟩,
      existsi g'*g,
      rw [is_monoid_action.mul ρ, h, h'] } }
  end⟩⟩