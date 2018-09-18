/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

More stuff for Principal Ideal Domains and Unique Factorization Domains

- PIDs are Noetherian
- PIDs are UFDs

-/
import
  ring_theory.principal_ideal_domain
  ring_theory.noetherian
  ring_theory.unique_factorization_domain

variables {α : Type*}

lemma associated_mul_mul [comm_monoid α] {a₁ a₂ b₁ b₂ : α} :
  associated a₁ b₁ → associated a₂ b₂ → associated (a₁ * a₂) (b₁ * b₂)
| ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ := ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩

namespace submodule
variables {β : Type*} [ring α] [module α β]
include α

lemma span_singleton_subset {b : β} {s : submodule α β}: span {b} ⊆ s ↔ b ∈ s :=
by rw [submodule.span_subset_iff, set.singleton_subset_iff]; refl

lemma mem_span_singleton {b₁ b₂ : β} : b₁ ∈ span ({b₂} : set β) ↔ ∃c, b₁ = c • b₂ :=
show b₁ ∈ _root_.span ({b₂} : set β) ↔ ∃c, b₁ = c • b₂,
  by simp [_root_.span_singleton, eq_comm]

end submodule

namespace principal_ideal_domain
variables [principal_ideal_domain α]

lemma is_noetherian_ring : is_noetherian_ring α :=
assume ⟨s, hs⟩,
begin
  letI := classical.dec_eq α,
  have : is_ideal s := {.. hs},
  rcases (principal s).principal with ⟨a, rfl⟩,
  refine ⟨{a}, show span (↑({a} : finset α)) = {x : α | a ∣ x}, from _⟩,
  simp [span_singleton, set.range, has_dvd.dvd, eq_comm, mul_comm]
end

section
local attribute [instance] classical.prop_decidable
open submodule

lemma factors_decreasing (b₁ b₂ : α) (h₁ : b₁ ≠ 0) (h₂ : ¬ is_unit b₂) :
  submodule.span {b₁} > submodule.span ({b₁ * b₂} : set α) :=
lt_of_le_not_le (span_singleton_subset.2 $ mem_span_singleton.2 $ ⟨b₂, by simp [mul_comm]⟩) $
assume (h : submodule.span {b₁} ⊆ submodule.span ({b₁ * b₂} : set α)),
have ∃ (c : α), b₁ * (b₂ * c) = b₁ * 1,
{ simpa [span_singleton_subset, mem_span_singleton, mul_left_comm, mul_comm, mul_assoc, eq_comm] using h },
let ⟨c, eq⟩ := this in
have b₂ * c = 1, from eq_of_mul_eq_mul_left h₁ eq,
h₂ ⟨units.mk_of_mul_eq_one _ _ this, rfl⟩

lemma exists_factors (a : α) : a ≠ 0 → ∃f:multiset α, (∀b∈f, irreducible b) ∧ associated a f.prod :=
have well_founded (inv_image (>) (λb, submodule.span ({b} : set α))), from
  inv_image.wf _ $ is_noetherian_iff_well_founded.1 $ is_noetherian_ring,
this.induction a
begin
  assume a ih ha,
  by_cases h_unit : is_unit a,
  { exact match a, h_unit with _, ⟨u, rfl⟩ := ⟨∅, by simp, u⁻¹, by simp⟩ end },
  by_cases h_irreducible : irreducible a,
  { exact ⟨{a}, by simp [h_irreducible]⟩ },

  have : ∃b₁ b₂, a = b₁ * b₂ ∧ ¬ is_unit b₁ ∧ ¬ is_unit b₂,
  { simp [irreducible, not_or_distrib, not_forall] at h_irreducible; from h_irreducible h_unit },
  rcases this with ⟨b₁, b₂, eq, h₁, h₂⟩,

  have hb₁ : b₁ ≠ 0, { assume eq, simp * at * },
  have : submodule.span {b₁} > submodule.span ({a} : set α),
    by rw [eq]; from factors_decreasing b₁ b₂ hb₁ h₂,
  rcases ih b₁ this hb₁ with ⟨f₁, hf₁, ha₁⟩,

  have hb₂ : b₂ ≠ 0, { assume eq, simp * at * },
  have : submodule.span {b₂} > submodule.span ({a} : set α),
    by rw [eq, mul_comm]; from factors_decreasing b₂ b₁ hb₂ h₁,
  rcases ih b₂ this hb₂ with ⟨f₂, hf₂, ha₂⟩,

  refine ⟨f₁ + f₂, _⟩,
  simpa [or_imp_distrib, forall_and_distrib, eq, associated_mul_mul ha₁ ha₂] using and.intro hf₁ hf₂
end



end

end principal_ideal_domain
