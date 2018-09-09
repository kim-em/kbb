import tactic.tidy
import group_theory.subgroup
import group_theory.perm
import data.finset
import .monoid_stuff
import .matrices

noncomputable theory

local attribute [instance] classical.prop_decidable

universes u v

namespace matrix
variables {n : Type u} [fintype n] {R : Type v} [comm_ring R]

instance : group (equiv.perm n) := by apply_instance

instance bij_fintype : fintype {f : n → n // function.bijective f} := 
set_fintype _

instance equiv_perm_fin_finite : fintype (equiv.perm n):=
fintype.of_surjective (λ (f : {f : n → n // function.bijective f}), equiv.of_bijective f.2) 
begin 
  unfold function.surjective,
  simp,
  intro b,
  let f : {f : n → n // function.bijective f} := ⟨b.1, b.bijective⟩,
  existsi f.1,
  existsi  f.2,
  apply equiv.ext,
  intro x,
  rw equiv.of_bijective_to_fun,
  refl
end

def e (σ : equiv.perm n) : R := ((equiv.perm.sign σ : ℤ) : R)

@[simp] lemma e_mul (σ τ : equiv.perm n) : (e (σ * τ) : R) = e σ * e τ :=
by unfold e; rw ← int.cast_mul; congr; rw ← units.mul_coe; congr; apply is_group_hom.mul

@[simp] lemma e_one : (e (1 : equiv.perm n) : R) = 1 :=
by unfold e; rw is_group_hom.one equiv.perm.sign; simp <|> apply_instance

definition det (M : matrix n n R) : R :=
finset.univ.sum (λ (σ : equiv.perm n),
(e σ) * finset.univ.prod (λ (i:n), M (σ i) i))

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = finset.univ.prod d :=
begin
  transitivity finset.sum (finset.singleton (1 : equiv.perm n)) _,
  { symmetry,
    apply finset.sum_subset (finset.subset_univ _),
    intros σ h1 h2,
    simp at h2,
    have h3 := mt (equiv.ext _ _) h2,
    simp [not_forall] at h3,
    cases h3 with x h3,
    convert mul_zero _,
    apply finset.prod_eq_zero,
    { change x ∈ _, simp },
    simp [diagonal, h3] },
  simp
end

@[simp] lemma det_scalar {r : R} : det (scalar r : matrix n n R) = r^(fintype.card n) :=
by simp [scalar, fintype.card]

-- Useful lemma by Chris
lemma zero_pow {n : ℕ} : 0 < n → (0 : R) ^ n = 0 :=
by cases n; simp [_root_.pow_succ, lt_irrefl]

@[simp] lemma det_zero (h : nonempty n) : det (0 : matrix n n R) = (0 : R) :=
by rw ← scalar_zero; simp [-scalar_zero, zero_pow, fintype.card_pos_iff.mpr h]

@[simp] lemma det_one : det (1 : matrix n n R) = (1 : R) :=
by rw ← scalar_one; simp [-scalar_one]

--set_option trace.simplify.rewrite true

@[simp] lemma det_mul (M : matrix n n R) (N : matrix n n R) :
det (M * N) = det M * det N :=
begin
  simp [det],
  conv {
    to_lhs,
    simp [finset.prod_sum, finset.prod_mul_distrib, finset.mul_sum],
    rw finset.sum_comm,
    congr, skip, funext,
    simp only [mul_comm],
    simp only [mul_comm (e _) _ ],
    simp only [_root_.mul_assoc _ _ (e _)],
    rw ← finset.mul_sum,
    simp only [mul_comm (_) (e _)],
  },
  -- trying to follow the argument outlined in
  -- https://math.stackexchange.com/questions/177560/proving-determinant-product-rule-combinatorially
  sorry
end

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

end matrix
