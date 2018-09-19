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

lemma is_unit_of_dvd_one [comm_semiring α] : ∀a ∣ 1, is_unit (a:α)
| a ⟨b, eq⟩ := ⟨units.mk_of_mul_eq_one a b eq.symm, rfl⟩

def prime [comm_semiring α] (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ (∀a b, p ∣ a * b → p ∣ a ∨ p ∣ b)

lemma exists_mem_multiset_dvd_of_prime [comm_semiring α] {s : multiset α} {p : α} (hp : prime p) :
  p ∣ s.prod → ∃a∈s, p ∣ a :=
multiset.induction_on s (assume h, (hp.2.1 $ is_unit_of_dvd_one _ h).elim) $
assume a s ih h,
  have p ∣ a * s.prod, by simpa using h,
  match hp.2.2 a s.prod this with
  | or.inl h := ⟨a, multiset.mem_cons_self a s, h⟩
  | or.inr h := let ⟨a, has, h⟩ := ih h in ⟨a, multiset.mem_cons_of_mem has, h⟩
  end

lemma associated_mul_mul [comm_monoid α] {a₁ a₂ b₁ b₂ : α} :
  associated a₁ b₁ → associated a₂ b₂ → associated (a₁ * a₂) (b₁ * b₂)
| ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ := ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩

lemma not_prime_zero [integral_domain α] : ¬ prime (0 : α)
| ⟨h, _⟩ := h rfl

namespace associates
instance [comm_monoid α] : has_dvd (associates α) := ⟨(≤)⟩

lemma dvd_eq_le [comm_monoid α] : ((∣) : associates α → associates α → Prop) = (≤) := rfl

section comm_semiring
variables [comm_semiring α]

def prime (p : associates α) : Prop := p ≠ 0 ∧ p ≠ 1 ∧ (∀a b, p ≤ a * b → p ≤ a ∨ p ≤ b)

lemma exists_mem_multiset_le_of_prime {s : multiset (associates α)} {p : associates α}
  (hp : prime p) :
  p ≤ s.prod → ∃a∈s, p ≤ a :=
multiset.induction_on s (assume ⟨d, eq⟩, (hp.2.1 (mul_eq_one_iff.1 eq).1).elim) $
assume a s ih h,
  have p ≤ a * s.prod, by simpa using h,
  match hp.2.2 a s.prod this with
  | or.inl h := ⟨a, multiset.mem_cons_self a s, h⟩
  | or.inr h := let ⟨a, has, h⟩ := ih h in ⟨a, multiset.mem_cons_of_mem has, h⟩
  end

lemma prime_mk (p : α) : prime (associates.mk p) ↔ _root_.prime p :=
begin
  rw [associates.prime, _root_.prime, forall_associated],
  transitivity,
  { apply and_congr, refl,
    apply and_congr, refl,
    apply forall_congr, assume a,
    exact forall_associated },
  apply and_congr,
  { rw [(≠), mk_zero_eq] },
  apply and_congr,
  { rw [(≠), ← is_unit_iff_eq_one, is_unit_mk], },
  apply forall_congr, assume a,
  apply forall_congr, assume b,
  rw [mk_mul_mk, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff]
end

end comm_semiring

lemma eq_of_mul_eq_mul_left [integral_domain α] :
  ∀(a b c : associates α), a ≠ 0 → a * b = a * c → b = c :=
begin
  rintros ⟨a⟩ ⟨b⟩ ⟨c⟩ ha h,
  rcases quotient.exact' h with ⟨u, hu⟩,
  have hu : a * (b * ↑u) = a * c, { rwa [← mul_assoc] },
  exact quotient.sound' ⟨u, eq_of_mul_eq_mul_left (mt (mk_zero_eq a).2 ha) hu⟩
end

lemma le_of_mul_le_mul_left [integral_domain α] (a b c : associates α) (ha : a ≠ 0) :
  a * b ≤ a * c → b ≤ c
| ⟨d, hd⟩ := ⟨d, eq_of_mul_eq_mul_left a _ _ ha $ by rwa ← mul_assoc⟩

lemma one_or_eq_of_le_of_prime [integral_domain α] :
  ∀(p m : associates α), prime p → m ≤ p → (m = 1 ∨ m = p)
| _ m ⟨hp0, hp1, h⟩ ⟨d, rfl⟩ :=
match h m d (le_refl _) with
| or.inl h := classical.by_cases (assume : m = 0, by simp [this]) $
  assume : m ≠ 0,
  have m * d ≤ m * 1, by simpa using h,
  have d ≤ 1, from associates.le_of_mul_le_mul_left m d 1 ‹m ≠ 0› this,
  have d = 1, from lattice.bot_unique this,
  by simp [this]
| or.inr h := classical.by_cases (assume : d = 0, by simp [this] at hp0; contradiction) $
  assume : d ≠ 0,
  have d * m ≤ d * 1, by simpa [mul_comm] using h,
  or.inl $ lattice.bot_unique $ associates.le_of_mul_le_mul_left d m 1 ‹d ≠ 0› this
end

end associates

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

lemma is_maximal_ideal_of_irreducible {p : α} (hp : irreducible p) :
  is_maximal_ideal {a | p ∣ a} :=
begin
  letI h : is_ideal {a | p ∣ a} := @is_principal_ideal.to_is_ideal _ _ _ ⟨⟨p, rfl⟩⟩,
  refine is_maximal_ideal.mk _ (assume ⟨q, hq⟩, hp.1 ⟨units.mk_of_mul_eq_one _ q hq.symm, rfl⟩) _,
  assume x T i hT hxp hx,
  rcases (principal T).principal with ⟨q, rfl⟩,
  rcases hT (dvd_refl p) with ⟨c, rfl⟩,
  rcases hp.2 _ _ rfl with ⟨q, rfl⟩ | ⟨c, rfl⟩,
  { exact units.coe_dvd _ _ },
  { simp at hxp hx, exact (hxp hx).elim }
end

lemma prime_of_irreducible {p : α} (hp : irreducible p) : prime p :=
have is_prime_ideal {a | p ∣ a}, from
  @is_maximal_ideal.is_prime_ideal α _ _ (is_maximal_ideal_of_irreducible hp),
⟨assume h, not_irreducible_zero (show irreducible (0:α), from h ▸ hp), hp.1, this.mem_or_mem_of_mul_mem⟩

lemma associates_prime_of_irreducible : ∀{p : associates α}, irreducible p → p.prime :=
associates.forall_associated.2 $ assume a,
begin
  rw [associates.irreducible_mk_iff, associates.prime_mk],
  exact prime_of_irreducible
end

lemma eq_of_prod_eq_associates {s : multiset (associates α)} :
  ∀{t:multiset (associates α)}, (∀a∈s, irreducible a) → (∀a∈t, irreducible a) → s.prod = t.prod →
  s = t :=
begin
  letI := classical.dec_eq (associates α),
  refine s.induction_on _ _,
  { assume t _ ht eq,
    have : ∀a∈t, (a:associates α) = 1, from associates.prod_eq_one_iff.1 eq.symm,
    have : ∀a∈t, irreducible (1 : associates α), from assume a ha, this a ha ▸ ht a ha,
    exact (multiset.eq_zero_of_forall_not_mem $ assume a ha, not_irreducible_one $ this a ha).symm },
  { assume a s ih t hs ht h,
    have ha : a.prime, from associates_prime_of_irreducible (hs a $ multiset.mem_cons_self a s),
    rcases associates.exists_mem_multiset_le_of_prime ha ⟨s.prod, by simpa using h⟩
      with ⟨x, hx, hxa⟩,
    have : x.prime, from associates_prime_of_irreducible (ht x hx),
    have : a = x := (associates.one_or_eq_of_le_of_prime _ _ this hxa).resolve_left ha.2.1,
    subst this,
    have : s.prod = (t.erase a).prod,
    { rw ← multiset.cons_erase hx at h,
      simp at h,
      exact associates.eq_of_mul_eq_mul_left a _ _ ha.1 h },
    have : s = t.erase a, from ih
      (assume x hxs, hs x $ multiset.mem_cons_of_mem hxs)
      (assume x hxt, ht x $ classical.by_cases
        (assume h : x = a, h.symm ▸ hx)
        (assume ne, (multiset.mem_erase_of_ne ne).1 hxt))
      this,
    rw [this, multiset.cons_erase hx] }
end

lemma associated_of_associated_prod_prod {s t : multiset α}
  (hs : ∀a∈s, irreducible a) (ht : ∀a∈t, irreducible a) (h : associated s.prod t.prod) :
  multiset.rel associated s t :=
begin
  refine (associates.rel_associated_iff_map_eq_map.2 $ eq_of_prod_eq_associates _ _ _),
  { assume a ha,
    rcases multiset.mem_map.1 ha with ⟨x, hx, rfl⟩,
    simpa [associates.irreducible_mk_iff] using hs x hx },
  { assume a ha,
    rcases multiset.mem_map.1 ha with ⟨x, hx, rfl⟩,
    simpa [associates.irreducible_mk_iff] using ht x hx },
  rwa [associates.prod_mk, associates.prod_mk, associates.mk_eq_mk_iff_associated]
end

section
local attribute [instance] classical.prop_decidable

noncomputable def factors (a : α) : multiset α :=
if h : a = 0 then ∅ else classical.some (exists_factors a h)

lemma factors_spec (a : α) (h : a ≠ 0) :
  (∀b∈factors a, irreducible b) ∧ associated a (factors a).prod :=
begin
  unfold factors, rw [dif_neg h],
  exact classical.some_spec (exists_factors a h)
end

/-- The unique factorization domain structure given by the principal ideal domain.

This is not added as type class instance, since the `factors` might be computed in a different way.
E.g. factors could return normalized values.
-/
noncomputable def to_unique_factorization_domain : unique_factorization_domain α :=
{ factors := factors,
  factors_prod := assume a ha, associated.symm (factors_spec a ha).2,
  irreducible_factors := assume a ha, (factors_spec a ha).1,
  unique := assume s t, associated_of_associated_prod_prod }

end

end principal_ideal_domain
