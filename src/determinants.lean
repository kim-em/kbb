import tactic.tidy
import group_theory.subgroup
import group_theory.perm
import data.finset
import .monoid_stuff
import .matrices
import .Sym

universes u v

namespace matrix
variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

instance : group (equiv.perm n) := by apply_instance

@[simp] lemma equiv.swap_mul_self (i j : n) : equiv.swap i j * equiv.swap i j = 1 :=
equiv.swap_swap i j

@[simp] lemma equiv.swap_swap_apply (i j k : n) : equiv.swap i j (equiv.swap i j k) = k :=
equiv.swap_core_swap_core k i j

instance : decidable_pred (function.bijective : (n → n) → Prop) :=
λ _, by unfold function.bijective; apply_instance

instance bij_fintype : fintype {f : n → n // function.bijective f} := 
set_fintype _

@[extensionality] theorem equiv.perm.ext (σ τ : equiv.perm n)
  (H : ∀ i, σ i = τ i) : σ = τ :=
equiv.ext _ _ H

instance equiv_perm_fin_finite : fintype (equiv.perm n):=
trunc.rec_on_subsingleton (fintype.equiv_fin n) $ λ φ,
fintype.of_equiv (Sym (fintype.card n)) $
{ to_fun := λ σ, φ.trans (σ.trans φ.symm),
  inv_fun := λ σ, φ.symm.trans (σ.trans φ),
  left_inv := λ σ, by ext i; simp,
  right_inv := λ σ, by ext i; simp }

def e (σ : equiv.perm n) : R := ((σ.sign : ℤ) : R)

@[simp] lemma e_mul (σ τ : equiv.perm n) : (e (σ * τ) : R) = e σ * e τ :=
by unfold e; rw ← int.cast_mul; congr; rw ← units.mul_coe; congr; apply is_group_hom.mul

@[simp] lemma e_swap {i j : n} (H : i ≠ j) : (e (equiv.swap i j) : R) = -1 :=
by unfold e; rw [equiv.perm.sign_swap H]; simp

@[simp] lemma e_one : (e (1 : equiv.perm n) : R) = 1 :=
by unfold e; rw is_group_hom.one (equiv.perm.sign : equiv.perm n → units ℤ); simp

@[simp] lemma e_inv (σ : equiv.perm n): (e σ⁻¹ : R) = e σ :=
by unfold e; rw is_group_hom.inv (equiv.perm.sign : equiv.perm n → units ℤ);
cases int.units_eq_one_or σ.sign with H H; rw H; refl

lemma e_eq_one_or (σ : equiv.perm n) : (e σ : R) = 1 ∨ (e σ : R) = -1 :=
by cases int.units_eq_one_or σ.sign with H H; unfold e; rw H; simp

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

lemma det_mul_aux (M N : matrix n n R) (p : n → n) (H : ¬function.bijective p) :
  finset.sum (finset.univ : finset (equiv.perm n))
    (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
      * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) = 0 :=
have H1 : ¬function.injective p,
  from mt (λ h, and.intro h $ fintype.injective_iff_surjective.1 h) H,
let ⟨i, hi⟩ := not_forall.1 H1 in
let ⟨j, hj⟩ := not_forall.1 hi in
let ⟨H2, H3⟩ := not_imp.1 hj in
calc  finset.sum (finset.univ : finset (equiv.perm n))
        (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x)))
    = finset.sum (finset.univ.filter (λ σ, σ.sign = 1) 
          ∪ finset.univ.filter (λ σ, σ.sign = -1) : finset (equiv.perm n))
        (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) :
  finset.sum_congr (finset.eq_univ_iff_forall.2 $
    by intro σ; simpa using int.units_eq_one_or _).symm (λ _ _, rfl)
... = finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x)))
    + finset.sum (finset.univ.filter (λ σ, σ.sign = -1) : finset (equiv.perm n))
        (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) :
  finset.sum_union (finset.eq_empty_of_forall_not_mem $ λ σ H,
    by simp at H; from absurd (H.1.symm.trans H.2) dec_trivial)
... = finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x)))
    + finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, e (σ * equiv.swap i j) * (finset.prod (finset.univ : finset n) (λ x, M ((σ * equiv.swap i j) x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) :
  begin
    refine congr_arg _ (finset.sum_bij (λ σ _, σ * equiv.swap i j) _ _ _ _).symm,
    { refine λ σ H, finset.mem_filter.2 ⟨finset.mem_univ _, (is_group_hom.mul _ _ _).trans _⟩,
      simp at H, simp [equiv.perm.sign_swap H3, H] },
    { intros, refl },
    { intros _ _ _ _, exact mul_right_cancel },
    refine λ σ H, ⟨σ * equiv.swap i j, finset.mem_filter.2
      ⟨finset.mem_univ _, (is_group_hom.mul equiv.perm.sign _ _).trans _⟩, _⟩,
    { simp at H, rw [H, equiv.perm.sign_swap H3], refl },
    dsimp, rw [mul_assoc, equiv.swap_mul_self, mul_one]
  end
... = finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x)))
    + finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, e (σ * equiv.swap i j) * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) :
  begin
    refine congr_arg _ (finset.sum_congr rfl (λ σ _, congr_arg _ _)),
    suffices : finset.prod (finset.univ : finset n) (λ x, M ((σ * equiv.swap i j) x) (p x))
      = finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x)),
    { rw this },
    refine finset.prod_bij (λ x _, equiv.swap i j x) _ _ _ _,
    { exact λ _ _, finset.mem_univ _ },
    { refine λ _ _, congr_arg _ _,
      rw [equiv.swap_apply_def],
      split_ifs; cc },
    { exact λ _ _ _ _ H, (equiv.swap i j).bijective.1 H },
    refine λ k _, ⟨equiv.swap i j k, finset.mem_univ _, _⟩,
    simp
  end
... = finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x))
        + e (σ * equiv.swap i j) * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) :
  finset.sum_add_distrib.symm
... = finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x)
          * (e σ + e (σ * equiv.swap i j))) :
  finset.sum_congr rfl (λ _ _, (add_mul _ _ _).symm.trans $ mul_comm _ _)
... = finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
          * finset.prod (finset.univ : finset n) (λ x, N (p x) x)
          * 0) :
  finset.sum_congr rfl (λ _ _, congr_arg _ $
    by rw [e_mul, e_swap H3, mul_neg_one, add_neg_self])
... = finset.sum (finset.univ.filter (λ σ, σ.sign = 1) : finset (equiv.perm n))
        (λ σ, (0 : R)) :
  finset.sum_congr rfl (λ _ _, mul_zero _)
... = 0 : finset.sum_const_zero

@[simp] lemma det_mul (M N : matrix n n R) :
det (M * N) = det M * det N :=
calc  det (M * N)
    = finset.sum (finset.univ : finset (equiv.perm n))
        (λ σ, e σ * finset.prod (finset.univ : finset n)
          (λ i, finset.sum (finset.univ : finset n)
            (λ j, M (σ i) j * N j i))) : rfl
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ σ, e σ * finset.sum (finset.pi (finset.univ : finset n) (λ a, (finset.univ : finset n)))
          (λ p, finset.prod (finset.attach finset.univ)
            (λ x, M (σ x.1) (p x.1 x.2) * N (p x.1 x.2) x.1))) :
  finset.sum_congr rfl (λ _ _, congr_arg _ finset.prod_sum)
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ σ, e σ * finset.sum (finset.univ : finset (n → n))
          (λ p, finset.prod (finset.univ : finset n)
            (λ x, M (σ x) (p x) * N (p x) x))) :
  finset.sum_congr rfl (λ _ _, congr_arg _ $
    finset.sum_bij (λ f _ i, f i (finset.mem_univ i))
      (λ _ _, finset.mem_univ _)
      (λ _ _, finset.prod_bij (λ x _, x.1) (λ _ _, finset.mem_univ _)
        (λ _ _, rfl) (λ _ _ _ _, subtype.eq)
        (λ b hb, ⟨⟨b, hb⟩, finset.mem_attach _ _, rfl⟩))
      (λ _ _ _ _ H, funext $ λ i, funext $ λ _, have H1 : _ := congr_fun H i, H1)
      (λ f _, ⟨λ i _, f i, finset.mem_pi.2 $ λ _ _, @finset.mem_univ _ _ _, rfl⟩))
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ σ, e σ * finset.sum (finset.univ : finset (n → n))
          (λ p, finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
            * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) :
  finset.sum_congr rfl (λ _ _, congr_arg _ $ finset.sum_congr rfl $
    λ _ _, finset.prod_mul_distrib)
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ σ, finset.sum (finset.univ : finset (n → n))
          (λ p, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
            * finset.prod (finset.univ : finset n) (λ x, N (p x) x)))) :
  finset.sum_congr rfl (λ σ _, finset.mul_sum)
... = finset.sum (finset.univ : finset (n → n))
        (λ p, finset.sum (finset.univ : finset (equiv.perm n))
          (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
            * finset.prod (finset.univ : finset n) (λ x, N (p x) x)))) :
  finset.sum_comm
... = finset.sum (finset.univ.filter function.bijective : finset (n → n))
        (λ p, finset.sum (finset.univ : finset (equiv.perm n))
          (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
            * finset.prod (finset.univ : finset n) (λ x, N (p x) x)))) :
  (finset.sum_subset (finset.subset_univ _) $ λ p _ H,
    det_mul_aux M N p (mt (λ H, finset.mem_filter.2 ⟨finset.mem_univ _, H⟩) H)).symm
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, finset.sum (finset.univ : finset (equiv.perm n))
          (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (τ x))
            * finset.prod (finset.univ : finset n) (λ x, N (τ x) x)))) :
  begin refine (finset.sum_bij (λ (τ : equiv.perm n) _ k, τ k) _ _ _ _).symm,
    { exact λ τ _, finset.mem_filter.2 ⟨finset.mem_univ _, τ.bijective⟩},
    { exact λ _ _, rfl },
    { exact λ _ _ _ _ H, equiv.perm.ext _ _ (congr_fun H) },
    exact λ b hb, ⟨equiv.of_bijective (finset.mem_filter.1 hb).2, finset.mem_univ _,
      (equiv.of_bijective_to_fun (finset.mem_filter.1 hb).2)⟩
  end
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, finset.sum (finset.univ : finset (equiv.perm n))
          (λ σ, finset.prod (finset.univ : finset n) (λ x, N (τ x) x)
            * (e σ * finset.prod (finset.univ : finset n) (λ x, M (σ x) (τ x))))) :
  finset.sum_congr rfl (λ _ _, finset.sum_congr rfl $ λ _ _, by ac_refl)
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, finset.prod (finset.univ : finset n) (λ x, N (τ x) x) *
          finset.sum (finset.univ : finset (equiv.perm n))
            (λ σ, e σ * finset.prod (finset.univ : finset n) (λ x, M (σ x) (τ x)))) :
  finset.sum_congr rfl (λ _ _, finset.mul_sum.symm)
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, finset.prod (finset.univ : finset n) (λ x, N (τ x) x) *
          finset.sum (finset.univ : finset (equiv.perm n))
            (λ σ, e σ * finset.prod (finset.univ : finset n) (λ x, M ((σ * τ⁻¹) x) x))) :
  finset.sum_congr rfl (λ τ _, congr_arg _ $ finset.sum_congr rfl $ λ σ _, congr_arg _ $
    finset.prod_bij (λ x _, τ x) (λ _ _, finset.mem_univ _)
      (λ _ _, by rw [equiv.perm.mul_apply, equiv.perm.inv_apply_self])
      (λ _ _ _ _ H, τ.bijective.1 H)
      (λ b _, ⟨τ⁻¹ b, finset.mem_univ _, (equiv.perm.apply_inv_self _ _).symm⟩))
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, finset.prod (finset.univ : finset n) (λ x, N (τ x) x) *
          finset.sum (finset.univ : finset (equiv.perm n))
            (λ σ, e (σ * τ) * finset.prod (finset.univ : finset n) (λ x, M (σ x) x))) :
  finset.sum_congr rfl (λ τ _, congr_arg _ $
    finset.sum_bij (λ σ _, σ * τ⁻¹) (λ _ _, finset.mem_univ _)
      (λ σ _, by rw [mul_assoc σ τ⁻¹ τ, inv_mul_self τ, mul_one σ])
      (λ _ _ _ _, mul_right_cancel)
      (λ b _, ⟨b * τ, finset.mem_univ _, by rw [mul_assoc b τ τ⁻¹, mul_inv_self τ, mul_one b]⟩))
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, finset.prod (finset.univ : finset n) (λ x, N (τ x) x) *
          finset.sum (finset.univ : finset (equiv.perm n))
            (λ σ, e τ * (e σ * finset.prod (finset.univ : finset n) (λ x, M (σ x) x)))) :
  finset.sum_congr rfl (λ τ _, congr_arg _ $ finset.sum_congr rfl $ λ σ _,
    by rw [e_mul, mul_comm (e σ) (e τ), mul_assoc])
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, finset.prod (finset.univ : finset n) (λ x, N (τ x) x) *
          (e τ * finset.sum (finset.univ : finset (equiv.perm n))
            (λ σ, e σ * finset.prod (finset.univ : finset n) (λ x, M (σ x) x)))) :
  finset.sum_congr rfl (λ τ _, congr_arg _ finset.mul_sum.symm)
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, e τ * finset.prod (finset.univ : finset n) (λ x, N (τ x) x) *
          finset.sum (finset.univ : finset (equiv.perm n))
            (λ σ, e σ * finset.prod (finset.univ : finset n) (λ x, M (σ x) x))) :
  finset.sum_congr rfl (λ _ _, by rw [mul_left_comm, ← mul_assoc])
... = finset.sum (finset.univ : finset (equiv.perm n))
        (λ τ, e τ * finset.prod (finset.univ : finset n) (λ x, N (τ x) x))
    * finset.sum (finset.univ : finset (equiv.perm n))
        (λ σ, e σ * finset.prod (finset.univ : finset n) (λ x, M (σ x) x)) :
  finset.sum_mul.symm
... = det N * det M : rfl
... = det M * det N : mul_comm _ _

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

end matrix