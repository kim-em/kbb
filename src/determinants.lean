import tactic.tidy
import group_theory.subgroup
import group_theory.perm
import data.finset
import .monoid_stuff
import .matrices
import .Sym

universes u v

lemma finset.prod_mul_right {α} [group α] [fintype α]
  {β} [comm_monoid β] {f : α → β} {s : finset α} (x : α) :
  s.prod f =
  (s.map ⟨λ z, z * x⁻¹, λ _ _, mul_right_cancel⟩).prod (λ z, f (z * x)) :=
finset.prod_bij (λ z _, z * x⁻¹) (λ _ _, by simpa) (λ _ _, by simp)
  (λ _ _ _ _, mul_right_cancel) (λ b H,
    ⟨b * x, by revert H; simp [eq_comm] {contextual:=tt}, by simp⟩)

lemma finset.prod_mul_left {α} [group α] [fintype α]
  {β} [comm_monoid β] {f : α → β} (x : α) :
  (finset.univ : finset α).prod (λ z, f (x * z))
  = (finset.univ : finset α).prod f :=
finset.prod_bij (λ z _, x * z) (λ _ _, finset.mem_univ _) (λ _ _, rfl)
  (λ _ _ _ _, mul_left_cancel) (λ b _, ⟨x⁻¹ * b, finset.mem_univ _, by simp⟩)

lemma finset.sum_mul_right {α} [group α] [fintype α]
  {β} [add_comm_monoid β] {f : α → β} {s : finset α} (x : α) :
  s.sum f =
  (s.map ⟨λ z, z * x⁻¹, λ _ _, mul_right_cancel⟩).sum (λ z, f (z * x)) :=
finset.sum_bij (λ z _, z * x⁻¹) (λ _ _, by simpa) (λ _ _, by simp)
  (λ _ _ _ _, mul_right_cancel) (λ b H,
    ⟨b * x, by revert H; simp [eq_comm] {contextual:=tt}, by simp⟩)

lemma finset.sum_mul_left {α} [group α] [fintype α]
  {β} [add_comm_monoid β] {f : α → β} (x : α) :
  (finset.univ : finset α).sum (λ z, f (x * z))
  = (finset.univ : finset α).sum f :=
finset.sum_bij (λ z _, x * z) (λ _ _, finset.mem_univ _) (λ _ _, rfl)
  (λ _ _ _ _, mul_left_cancel) (λ b _, ⟨x⁻¹ * b, finset.mem_univ _, by simp⟩)

lemma finset.prod_perm {α} [fintype α] [decidable_eq α]
  {β} [comm_monoid β] {f : α → β} (σ : equiv.perm α) :
  (finset.univ : finset α).prod f
  = finset.univ.prod (λ z, f (σ z)) :=
eq.symm $ finset.prod_bij (λ z _, σ z) (λ _ _, finset.mem_univ _) (λ _ _, rfl)
  (λ _ _ _ _ H, σ.bijective.1 H) (λ b _, ⟨σ⁻¹ b, finset.mem_univ _, by simp⟩)

lemma finset.sum_perm {α} [fintype α] [decidable_eq α]
  {β} [add_comm_monoid β] {f : α → β} (σ : equiv.perm α) :
  (finset.univ : finset α).sum f
  = finset.univ.sum (λ z, f (σ z)) :=
eq.symm $ finset.sum_bij (λ z _, σ z) (λ _ _, finset.mem_univ _) (λ _ _, rfl)
  (λ _ _ _ _ H, σ.bijective.1 H) (λ b _, ⟨σ⁻¹ b, finset.mem_univ _, by simp⟩)

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

@[simp] lemma equiv.perm.sign_mul (σ τ : equiv.perm n) :
  (σ * τ).sign = σ.sign * τ.sign :=
is_group_hom.mul _ _ _

@[simp] lemma equiv.perm.sign_one :
  equiv.perm.sign (1 : equiv.perm n) = 1 :=
is_group_hom.one _

@[simp] lemma equiv.perm.sign_refl :
  equiv.perm.sign (equiv.refl n) = 1 :=
is_group_hom.one equiv.perm.sign

@[simp] lemma equiv.perm.sign_swap' {i j : n} :
  (equiv.swap i j).sign = if i = j then 1 else -1 :=
if H : i = j then by simp [H, equiv.swap_self] else
by simp [equiv.perm.sign_swap H, H]

def e (σ : equiv.perm n) : R := ((σ.sign : ℤ) : R)

@[simp] lemma e_mul (σ τ : equiv.perm n) : (e (σ * τ) : R) = e σ * e τ :=
by unfold e; rw ← int.cast_mul; congr; rw ← units.mul_coe; congr; apply is_group_hom.mul

@[simp] lemma e_swap {i j : n} : (e (equiv.swap i j) : R) = if i = j then 1 else -1 :=
by by_cases H : i = j; simp [e, H]

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
  refine (finset.sum_eq_single 1 _ _).trans _,
  { intros σ h1 h2,
    cases not_forall.1 (mt (equiv.ext _ _) h2) with x h3,
    convert mul_zero _,
    apply finset.prod_eq_zero,
    { change x ∈ _, simp },
    exact if_neg h3 },
  simp,
  simp
end

@[simp] lemma det_scalar {r : R} : det (scalar r : matrix n n R) = r^(fintype.card n) :=
by simp [scalar, fintype.card]

-- Useful lemma by Chris
lemma zero_pow : ∀ {n : ℕ}, 0 < n → (0 : R) ^ n = 0
| (n+1) H := zero_mul _

@[simp] lemma det_zero (h : nonempty n) : det (0 : matrix n n R) = (0 : R) :=
by rw ← scalar_zero; simp [-scalar_zero, zero_pow, fintype.card_pos_iff.mpr h]

@[simp] lemma det_one : det (1 : matrix n n R) = (1 : R) :=
by rw ← scalar_one; simp [-scalar_one]

lemma det_mul_aux (M N : matrix n n R) (p : n → n) (H : ¬function.bijective p) :
  finset.sum (finset.univ : finset (equiv.perm n))
    (λ σ, e σ * (finset.prod (finset.univ : finset n) (λ x, M (σ x) (p x))
      * finset.prod (finset.univ : finset n) (λ x, N (p x) x))) = 0 :=
begin
  have H1 : ¬function.injective p,
    from mt (λ h, and.intro h $ fintype.injective_iff_surjective.1 h) H,
  unfold function.injective at H1, simp [not_forall] at H1,
  rcases H1 with ⟨i, j, H2, H3⟩,
  have H4 : (finset.univ : finset (equiv.perm n)) = finset.univ.filter (λ σ, σ.sign = 1) ∪ finset.univ.filter (λ σ, σ.sign = -1),
  { ext k; simpa using int.units_eq_one_or _ },
  have H5 : (finset.univ : finset (equiv.perm n)).filter (λ σ, σ.sign = 1) ∩ finset.univ.filter (λ σ, σ.sign = -1) = ∅,
  { ext k, simp {contextual:=tt}, intro _, from dec_trivial },
  have H6 : finset.map ⟨λ z, z * equiv.swap i j, λ _ _, mul_right_cancel⟩
    (finset.univ.filter (λ σ, σ.sign = -1))
    = finset.univ.filter (λ σ, σ.sign = 1),
  { ext k, split,
    { exact λ H, by revert H; simp [eq_comm, H3] {contextual:=tt} },
    { exact λ H, finset.mem_map.2 ⟨k * equiv.swap i j,
        by revert H; simp [H3, mul_assoc] {contextual:=tt}⟩ } },
  have H7 : ∀ k, p (equiv.swap i j k) = p k,
  { intro k, rw [equiv.swap_apply_def], split_ifs; cc },
  rw [H4, finset.sum_union H5],
  refine eq.trans (congr_arg _ (finset.sum_mul_right $ equiv.swap i j)) _,
  conv { to_lhs, congr, skip, for (finset.prod _ _) [1] { rw finset.prod_perm (equiv.swap i j)}},
  simp [H3, H6, H7]
end

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