import tactic.tidy
import group_theory.subgroup
import group_theory.perm
import data.finset
import .monoid_stuff
import .matrices

universes u v

namespace matrix
variables {n : ℕ} {R : Type v} [comm_ring R]

instance {n : ℕ} : group (equiv.perm (fin n)) := by apply_instance

instance bij_fintype {n : ℕ} : fintype {f : fin n → fin n // function.bijective f} := 
set_fintype _

noncomputable instance equiv_perm_fin_finite {n:ℕ} : fintype (equiv.perm(fin n)):=
fintype.of_surjective (λ (f : {f : fin n → fin n // function.bijective f}), equiv.of_bijective f.2) 
begin 
  unfold function.surjective,
  simp,
  intro b,
  let f : {f : fin n → fin n // function.bijective f} := ⟨b.1, b.bijective⟩,
  existsi f.1,
  existsi  f.2,
  apply equiv.ext,
  intro x,
  rw equiv.of_bijective_to_fun,
  refl
end

def e (σ : equiv.perm (fin n)) : R := ((equiv.perm.sign σ : ℤ) : R)

noncomputable definition det (M : matrix (fin n) (fin n) R) : R :=
finset.univ.sum (λ (σ : equiv.perm (fin n)),
(e σ) * finset.univ.prod (λ (i:fin n), M (σ.1 i) i))

@[simp] lemma det_zero : det (0 : matrix (fin n.succ) (fin n.succ) R) = (0 : R) :=
begin
  simp [det],
  have H : ∀ σ : equiv.perm (fin n.succ), e σ * (0 : R) ^ (finset.univ : finset (fin n.succ)).card = 0,
  begin
    intro x,
    suffices : (0 : R) ^ (finset.univ : finset (fin n.succ)).card = 0,
    rw this, simp,
    suffices : (finset.univ : finset (fin n.succ)).card = n.succ,
    rw [this, pow_succ], simp,
    exact fintype.card_fin n.succ
  end,
  conv {
    to_lhs, congr, skip, funext,
    rw H
  },
  simp
end

#print equiv.perm.sign.is_group_hom

@[simp] lemma det_one : det (1 : matrix (fin n) (fin n) R) = (1 : R) :=
begin
  simp [det],
  have H : ∀ σ : equiv.perm (fin n),
    finset.univ.prod (λ (i : fin n), (1 : matrix _ _ R) (σ.1 i) i) =
    ite (σ = 1) 1 0,
  begin
    intro σ,
    split_ifs,
    { conv {
        to_lhs, congr, skip, funext,
        rw [h, one_val],
      },
      conv {
        to_rhs,
        rw ← @finset.prod_const_one (fin n) R finset.univ _
      },
      apply finset.prod_congr rfl,
      intros,
      split_ifs,
      refl,
      change ((1 : equiv.perm (fin n)) x ≠ x) at h_1,
      have : ((1 : equiv.perm (fin n)) x = x) := by simp,
      exfalso, exact h_1 this
    },
    { have : ∃ i : fin n, σ.to_fun i ≠ i :=
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
      rw ← @finset.prod_sdiff,
      work_on_goal 2 {
        exact singleton i
      },
      tidy,
      suffices : (1 : matrix _ _ R) (σ.to_fun i) i = 0,
      rw this, simp,
      simp [hi] }
  end,
  conv {
    to_lhs, congr, skip, funext,
    rw H,
  },
  transitivity finset.sum (finset.singleton 1 : finset (equiv.perm (fin n))) _,
  { symmetry,
    apply finset.sum_subset,
    { intros i H, simp },
    { intros, simp at a, split_ifs, simp } },
  simp [e],
  rw is_group_hom.one equiv.perm.sign,
  simp,
  apply_instance
end

@[simp] lemma det_mul (M : matrix (fin n) (fin n) R) (N : matrix (fin n) (fin n) R) :
det (M * N) = det M * det N := sorry

instance : is_monoid_hom (det : matrix (fin n) (fin n) R → R) :=
{ map_one := det_one,
  map_mul := det_mul }





-- def cross_out_column
--   (A : matrix (fin (n+1)) (fin (n+1)) R) (m : fin (n+1)) : matrix (fin n) (fin n) R := 
-- λ i j,
-- if j.1 < m.1 then  A i.succ j.raise else 
--   A i.succ j.succ

-- def det_laplace : Π {n: nat}, matrix (fin (n+1)) (fin (n+1)) R → R
-- | 0 := λ A, A 0 0
-- | (n + 1) := λ A, 
--   finset.sum finset.univ (λ k : fin (n+2), (-1 : R)^(k.1) * (A 0 k) *
--  det_laplace (cross_out_column A k))

-- namespace det_laplace

-- lemma det_1_1_zero : det_laplace (0 : matrix (fin 1) (fin 1) R) = 0 := rfl

-- lemma det_1_1_one : det_laplace (1 : matrix (fin 1) (fin 1) R) = 1 := rfl

-- lemma cross_out_column_zero {m : fin (n+1)} : cross_out_column (0 : matrix _ _ R) m = 0 :=
-- by funext; unfold cross_out_column; split_ifs; simp

-- lemma cross_out_column_one_0 : cross_out_column (1 : matrix (fin (n+1)) _ R) 0 = 1 :=
-- begin
--   funext,
--   unfold cross_out_column,
--   split_ifs;
--   simp [one_val];
--   split_ifs;
--   tidy;
--   exfalso;
--   try { exact nat.not_lt_zero _ h, },
--   replace h_1 := fin.veq_of_eq h_1,
--   replace h_2 := fin.vne_of_ne h_2,
--   tidy
-- end

-- lemma cross_out_column_one_ne0 (m : fin (n+1)) (h : m ≠ 0) : det_laplace (cross_out_column (1 : matrix _ _ R) m) = 0 :=
-- begin
--   funext,
--   unfold cross_out_column,
--   split_ifs;
--   simp [one_val];
--   split_ifs;
--   tidy;
--   exfalso;
--   try { exact nat.not_lt_zero _ h, },
--   replace h_1 := fin.veq_of_eq h_1,
--   replace h_2 := fin.vne_of_ne h_2,
--   tidy
-- end

-- @[simp] lemma det_zero : det_laplace (0 : matrix (fin (n+1)) (fin (n+1)) R) = (0 : R) :=
-- begin
--   induction n with n ih,
--   exact det_1_1_zero,
--   unfold det_laplace,
--   conv {
--     to_lhs,
--     congr, skip,
--     funext,
--     rw [cross_out_column_zero, ih] },
--   simp
-- end

-- @[simp] lemma det_one : det_laplace (1 : matrix (fin (n+1)) (fin (n+1)) R) = (1 : R) :=
-- begin
--   induction n with n ih,
--   exact det_1_1_one,
--   unfold det_laplace,
--   have H : ∀ k : fin (n + 2), (-1) ^ k.val * ite (0 = k) (1 : R) 0 * det_laplace (cross_out_column 1 k) = (-1) ^ k.val * ite (0 = k) 1 0,
--   begin
--     intro k, split_ifs,
--     { rw [← h, cross_out_column_one_0, ih], simp },
--     { simp }
--   end,
--   conv {
--     to_lhs,
--     congr, skip,
--     funext,
--     rw [one_val, H k] },
--     transitivity finset.sum (finset.singleton 0 : finset (fin (n+2))) _,
--     { symmetry,
--       apply finset.sum_subset,
--       { intros i H, simp },
--       { intros, simp at a, simp [ne.symm a] } },
--     simp, refl
-- end

-- @[simp] lemma det_mul (M : matrix (fin (n + 1)) _ R) (N : matrix (fin (n + 1)) _ R) :
-- det_laplace (M * N) = det_laplace M * det_laplace N :=
-- begin
--   induction n with n ih,
--   { simp [det_laplace],
--     transitivity finset.sum (finset.singleton 0 : finset (fin (0+1))) _,
--     { symmetry,
--       apply finset.sum_subset,
--       { intros i H, simp },
--       { intros,
--         simp at a,
--         replace a := fin.vne_of_ne a,
--         cases x,
--         tidy } },
--     simp },
--   { simp [det_laplace],

--   }
--   sorry
-- end

-- end det_laplace

end matrix
