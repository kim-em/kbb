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

definition det (M : matrix n n R) : R :=
finset.univ.sum (λ (σ : equiv.perm n),
(e σ) * finset.univ.prod (λ (i:n), M (σ i) i))

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = finset.univ.prod d :=
begin
  have H : ∀ σ : equiv.perm n,
    finset.univ.prod (λ i : n, diagonal d (σ i) i) =
    ite (σ = 1) (finset.univ.prod d) 0,
  begin
    intro σ,
    split_ifs,
    { apply finset.prod_congr rfl,
      intros i hi,
      rw [h],
      simp },
    { have : ∃ i : n, σ.to_fun i ≠ i :=
      begin
        by_contra,
        simp at a,
        suffices : σ = 1,
        exact h this,
        apply equiv.ext,
        simp [a],
        exact a
      end,
      cases this with i hi,
      rw ← @finset.prod_sdiff _ _ (singleton i),
      tidy,
      rw show finset.prod {i} (λ (i : n), diagonal d (σ i) i) = 0,
      begin
        change (σ i) ≠ i at hi,
        simp [hi]
      end,
      simp }
  end,
  simp [det, H], clear H,
  transitivity finset.sum (finset.singleton 1 : finset (equiv.perm n)) _,
  { symmetry,
    apply finset.sum_subset,
    { intros i H, simp },
    { intros, simp at a, split_ifs,
      { exfalso, exact a h },
      { simp } } },
  simp [e],
  rw is_group_hom.one equiv.perm.sign,
  simp,
  apply_instance
end

@[simp] lemma det_scalar {r : R} : det (scalar r : matrix n n R) = r^(fintype.card n) :=
by simp [scalar, fintype.card]

-- Useful lemma by Chris
lemma zero_pow {n : ℕ} : 0 < n → (0 : R) ^ n = 0 :=
by cases n; simp [_root_.pow_succ, lt_irrefl]

-- Useful lemma by Kenny
@[simp] lemma card_nonempty (h : nonempty n) : 0 < fintype.card n :=
begin
  by_contra H,
  rw [not_lt, nat.le_zero_iff, fintype.card_eq_zero_iff] at H,
  exact h.rec_on H
end

@[simp] lemma det_zero (h : nonempty n) : det (0 : matrix n n R) = (0 : R) :=
by rw ← scalar_zero; simp [-scalar_zero, zero_pow, h]

@[simp] lemma det_one : det (1 : matrix n n R) = (1 : R) :=
by rw ← scalar_one; simp [-scalar_one]

@[simp] lemma det_mul (M : matrix n n R) (N : matrix n n R) :
det (M * N) = det M * det N := sorry

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

end matrix
