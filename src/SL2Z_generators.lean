import .modular_group
import .action

theorem int.mul_eq_one {m n : ℤ} :
  m * n = 1 ↔ m = 1 ∧ n = 1 ∨ m = -1 ∧ n = -1 :=
⟨λ H, or.cases_on (int.units_eq_one_or ⟨m, n, H, by rwa [mul_comm] at H⟩)
  (λ H1, have H2 : m = 1, from units.ext_iff.1 H1,
    or.inl ⟨H2, by rwa [H2, one_mul] at H⟩)
  (λ H1, have H2 : m = -1, from units.ext_iff.1 H1,
    or.inr ⟨H2, by rwa [H2, neg_one_mul, neg_eq_iff_neg_eq, eq_comm] at H⟩),
by simp [or_imp_distrib] {contextual := tt}⟩

namespace SL2Z_M

def S : SL2Z := ⟨0, -1, 1, 0, rfl⟩
def T : SL2Z := ⟨1, 1, 0, 1, rfl⟩

@[simp, SL2Z] lemma S_a : S.a = 0 := rfl
@[simp, SL2Z] lemma S_b : S.b = -1 := rfl
@[simp, SL2Z] lemma S_c : S.c = 1 := rfl
@[simp, SL2Z] lemma S_d : S.d = 0 := rfl
@[simp, SL2Z] lemma T_a : T.a = 1 := rfl
@[simp, SL2Z] lemma T_b : T.b = 1 := rfl
@[simp, SL2Z] lemma T_c : T.c = 0 := rfl
@[simp, SL2Z] lemma T_d : T.d = 1 := rfl

variable {m : ℤ}

local notation `Mat` := integral_matrices_with_determinant

@[simp, SL2Z] lemma S_mul_a (A : Mat m) : (SL2Z_M m S A).a = -A.c := by simp [SL2Z_M]
@[simp, SL2Z] lemma S_mul_b (A : Mat m) : (SL2Z_M m S A).b = -A.d := by simp [SL2Z_M]
@[simp, SL2Z] lemma S_mul_c (A : Mat m) : (SL2Z_M m S A).c = A.a := by simp [SL2Z_M]
@[simp, SL2Z] lemma S_mul_d (A : Mat m) : (SL2Z_M m S A).d = A.b := by simp [SL2Z_M]
@[simp, SL2Z] lemma T_mul_a (A : Mat m) : (SL2Z_M m T A).a = A.a + A.c := by simp [SL2Z_M]
@[simp, SL2Z] lemma T_mul_b (A : Mat m) : (SL2Z_M m T A).b = A.b + A.d := by simp [SL2Z_M]
@[simp, SL2Z] lemma T_mul_c (A : Mat m) : (SL2Z_M m T A).c = A.c := by simp [SL2Z_M]
@[simp, SL2Z] lemma T_mul_d (A : Mat m) : (SL2Z_M m T A).d = A.d := by simp [SL2Z_M]

lemma T_pow_aux (n : ℤ) : (T^n).a = 1 ∧ (T^n).b = n ∧ (T^n).c = 0 ∧ (T^n).d = 1 :=
int.induction_on n dec_trivial
  (λ i, by simp [gpow_add] {contextual:=tt})
  (λ i, by simp [gpow_add] {contextual:=tt})
@[simp, SL2Z] lemma T_pow_a (n : ℤ) : (T^n).a = 1 := (T_pow_aux n).1
@[simp, SL2Z] lemma T_pow_b (n : ℤ) : (T^n).b = n := (T_pow_aux n).2.1
@[simp, SL2Z] lemma T_pow_c (n : ℤ) : (T^n).c = 0 := (T_pow_aux n).2.2.1
@[simp, SL2Z] lemma T_pow_d (n : ℤ) : (T^n).d = 1 := (T_pow_aux n).2.2.2

@[simp, SL2Z] lemma S_mul_S : S * S = -1 := rfl

attribute [elab_as_eliminator] nat.strong_induction_on

def reps (m : ℤ) : set (Mat m) :=
{A : Mat m | A.c = 0 ∧ 0 < A.a ∧ 0 ≤ A.b ∧ int.nat_abs A.b < int.nat_abs A.d }

theorem reduce_aux (m : ℤ) (A : Mat m) (H : int.nat_abs (A.c) ≠ 0) :
  int.nat_abs (SL2Z_M m S (SL2Z_M m (T^(-(A.a/A.c))) A)).c < int.nat_abs A.c :=
begin
  have H2 : A.c ≠ 0, from mt (λ H2, show int.nat_abs (A.c) = 0, by rw H2; refl) H,
  simp only [one_mul, zero_mul, add_zero] with SL2Z,
  rw [neg_mul_eq_neg_mul_symm, mul_comm, ← sub_eq_add_neg, ← int.mod_def],
  rw [← int.coe_nat_lt, int.nat_abs_of_nonneg (int.mod_nonneg _ H2)],
  rw [← int.abs_eq_nat_abs],
  exact int.mod_lt _ H2
end

def reduce_step (A : Mat m) : Mat m := SL2Z_M m S (SL2Z_M m (T^(-(A.a/A.c))) A)

/-- correct if m ≠ 0 -/
def reduce (m : ℤ) : Mat m → Mat m | A :=
if H1 : int.nat_abs A.c = 0
then if H2 : A.a > 0
  then SL2Z_M m (T^(-(A.b/A.d))) A
  else SL2Z_M m (T^(-(-A.b/ -A.d))) (SL2Z_M m S (SL2Z_M m S A))
else
  have int.nat_abs (reduce_step A).c < int.nat_abs A.c, from reduce_aux m A H1,
  reduce (reduce_step A)
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ integral_matrices_with_determinant.c)⟩]}

theorem reduce_def (m : ℤ) (A : Mat m) : reduce m A =
  if int.nat_abs A.c = 0
  then if H2 : A.a > 0
    then SL2Z_M m (T^(-(A.b/A.d))) A
    else SL2Z_M m (T^(-(-A.b/ -A.d))) (SL2Z_M m S (SL2Z_M m S A))
  else reduce m (SL2Z_M m S (SL2Z_M m (T^(-(A.a/A.c))) A)) :=
SL2Z_M.reduce.equations._eqn_1 _ _

theorem reduce_eq_of_zero (m : ℤ) {A : Mat m} (h : int.nat_abs A.c = 0) :
  reduce m A = (if H2 : A.a > 0
    then SL2Z_M m (T^(-(A.b/A.d))) A
    else SL2Z_M m (T^(-(-A.b/ -A.d))) (SL2Z_M m S (SL2Z_M m S A))) :=
by rw [reduce_def, if_pos h]

theorem reduce_eq (m : ℤ) {A : Mat m} (h : int.nat_abs A.c ≠ 0) :
  reduce m A = reduce m (reduce_step A) :=
by rw [reduce_def, reduce_step, if_neg h]

theorem reduce_mem_reps (m : ℤ) (Hm : m ≠ 0) (A : Mat m) : reduce m A ∈ reps m :=
begin
  suffices : ∀ n (A : Mat m), n = int.nat_abs A.c →
    (reduce m A).c = 0 ∧
    0 < (reduce m A).a ∧
    0 ≤ (reduce m A).b ∧
    int.nat_abs (reduce m A).b < int.nat_abs (reduce m A).d,
    from this _ A rfl,
  intro n, clear A,
  apply nat.strong_induction_on n,
  intros n ih A H, subst H,
  by_cases h1 : int.nat_abs (A.c) = 0,
  { rw [reduce_def, if_pos h1],
    by_cases h2 : A.a > 0,
    { rw [dif_pos h2],
      have h3 : A.c = 0 := int.eq_zero_of_nat_abs_eq_zero h1,
      simp only [h3, zero_mul, one_mul, mul_zero, add_zero, zero_add] with SL2Z,
      rw [← neg_mul_eq_neg_mul, ← sub_eq_add_neg, mul_comm, ← int.mod_def],
      have h4 : A.d ≠ 0,
      { intro h4, apply Hm, rw [← A.det, h3, h4, mul_zero, mul_zero, sub_zero] },
      refine ⟨rfl, h2, int.mod_nonneg _ h4, _⟩,
      rw [← int.coe_nat_lt, int.nat_abs_of_nonneg (int.mod_nonneg _ h4)],
      rw [← int.abs_eq_nat_abs],
      exact int.mod_lt _ h4 },
    { rw [dif_neg h2],
      have h3 : A.c = 0 := int.eq_zero_of_nat_abs_eq_zero h1,
      have h4 : -A.d ≠ 0,
      { intro h4, rw [neg_eq_zero] at h4, apply Hm,
        rw [← A.det, h3, h4, mul_zero, mul_zero, sub_zero] },
      have h5 : A.a ≠ 0,
      { intro h5, apply Hm, rw [← A.det, h3, h5, zero_mul, mul_zero, sub_zero] },
      have h6 : -A.a > 0,
      { exact neg_pos_of_neg ((lt_or_eq_of_le (le_of_not_lt h2)).resolve_right h5) },
      simp only [zero_mul, neg_zero, one_mul, mul_zero, h3, add_zero, zero_add, neg_one_mul, mul_neg_one] with SL2Z,
      rw [← neg_mul_eq_neg_mul, ← sub_eq_add_neg, mul_comm, ← int.mod_def],
      refine ⟨rfl, h6, int.mod_nonneg _ h4, _⟩,
      rw [← int.coe_nat_lt, int.nat_abs_of_nonneg (int.mod_nonneg _ h4)],
      rw [← int.abs_eq_nat_abs],
      exact int.mod_lt _ h4 } },
  { rw [reduce_def, if_neg h1],
    exact ih _ (reduce_aux _ _ h1) _ rfl }
end

@[elab_as_eliminator]
protected theorem induction_on {C : (Mat m) → Prop} (A : Mat m) (mne0 : m ≠ 0)
  (H0 : ∀ {A : Mat m} (h0 : A.c = 0) (h1 : A.a * A.d = m) (h2 : 0 < A.a) (h3 : 0 ≤ A.b) (h4 : int.nat_abs A.b < int.nat_abs A.d), C A)
  (HS : ∀ B, C B → C (SL2Z_M m S B)) (HT : ∀ B, C B → C (SL2Z_M m T B)) : C A :=
have hSid : ∀ B, (SL2Z_M m S (SL2Z_M m S (SL2Z_M m S (SL2Z_M m S B)))) = B, from λ B, by ext; simp,
have HS' : ∀ B, C (SL2Z_M m S B) → C B,
  from λ B ih, have H : _ := (HS _ $ HS _ $ HS _ ih), by rwa hSid B at H,
have hTinv : ∀ B, SL2Z_M m S (SL2Z_M m S (SL2Z_M m S (SL2Z_M m T (SL2Z_M m S (SL2Z_M m T (SL2Z_M m S B)))))) = SL2Z_M m T⁻¹ B,
  from λ B, by repeat {rw [←is_monoid_action.mul (SL2Z_M m)]}; congr,
have HT' : ∀ B, C B → C (SL2Z_M m T⁻¹ B),
  from λ B ih, by {have H := (HS _ $ HS _ $ HS _ $ HT _ $ HS _ $ HT _ $ HS _ ih), by rwa [hTinv] at H},
have HT3 : ∀ B, C (SL2Z_M m T B) → C B, from λ B ih,
  begin
    have H := HT' (SL2Z_M m T B) ih,
    rw [←is_monoid_action.mul (SL2Z_M m)] at H,
    rw mul_left_inv at H,
    rw [is_monoid_action.one (SL2Z_M m)] at H,
    exact H
  end,
have HT4 : ∀ B, C (SL2Z_M m T⁻¹ B) → C B, from λ B ih,
  begin
    have H := HT (SL2Z_M m T⁻¹ B) ih,
    rw [←is_monoid_action.mul (SL2Z_M m)] at H,
    simp at H,
    rw [is_monoid_action.one (SL2Z_M m)] at H,
    exact H
  end,
have HT5 : ∀ B (n:ℤ), C (SL2Z_M m (T^n) B) → C B, from λ B n,
  int.induction_on n (by rw [gpow_zero, is_monoid_action.one (SL2Z_M m)]; from id)
    (λ i ih1 ih2, ih1 $ HT3 _ $ begin
      conv { congr, rw ←is_monoid_action.mul (SL2Z_M m) },
      conv at ih2 { congr, rw [add_comm, gpow_add, gpow_one] },
      assumption end)
    (λ i ih1 ih2, ih1 $ HT4 _ $ begin
      conv { congr, rw ←is_monoid_action.mul (SL2Z_M m) },
      conv at ih2 { congr, rw [sub_eq_neg_add, gpow_add, gpow_neg_one] },
      assumption end),
have Hred : C (reduce m A),
{ rcases reduce_mem_reps m mne0 A with ⟨H1, H2, H3, H4⟩,
  refine H0 H1 _ H2 H3 H4,
  simpa only [H1, mul_zero, sub_zero] using (reduce m A).det },
suffices ∀ n (A : Mat m), int.nat_abs A.c = n → C (reduce m A) → C A,
  from this _ _ rfl Hred,
λ n_stupid, nat.strong_induction_on n_stupid $ λ n ih A H1 H2,
begin
  subst H1,
  rw reduce_def at H2, split_ifs at H2 with H3 H4,
  { exact HT5 _ _ H2 },
  { exact HS' _ (HS' _ (HT5 _ _ H2)) },
  have H4 := ih _ (reduce_aux _ _ H3) _ rfl H2,
  exact HT5 _ _ (HS' _ H4)
end

-- theorem closure : group.closure ({S, T} : set SL2Z) = set.univ :=
-- set.eq_univ_of_forall $ λ A, SL2Z_M.induction_on A
--   (group.in_closure.one _)
--   (λ B ih, group.in_closure.mul (group.in_closure.basic $ or.inr $ or.inl rfl) ih)
--   (λ B ih, group.in_closure.mul (group.in_closure.basic $ or.inl rfl) ih)

-- (h0 : A.c = 0) (h1 : A.a * A.d = m) (h2 : 0 ≤ A.a) (h3 : 0 ≤ A.b)
-- (h4 : int.nat_abs A.b ≤ int.nat_abs A.d)

theorem reduce_spec (m : ℤ) : ∀A:Mat m, ∃ S, SL2Z_M m S A = reduce m A | A :=
if h : int.nat_abs A.c = 0 then
begin
  rw [reduce_eq_of_zero m h],
  split_ifs,
  { exact ⟨_, rfl⟩ },
  { rw [← is_monoid_action.mul (SL2Z_M m), ← is_monoid_action.mul (SL2Z_M m)],
    exact ⟨_, rfl⟩ }
end
else
  have int.nat_abs (reduce_step A).c < int.nat_abs A.c, from reduce_aux m A h,
  let ⟨S, eq⟩ := reduce_spec (reduce_step A) in
  begin
    rw [reduce_eq m h, ← eq, reduce_step, ← is_monoid_action.mul (SL2Z_M m), ← is_monoid_action.mul (SL2Z_M m)],
    exact ⟨_, rfl⟩
  end
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ integral_matrices_with_determinant.c)⟩]}

theorem reps_unique (m : ℤ) (hm : m ≠ 0) :
  ∀(M : SL2Z) (A B : Mat m), A ∈ reps m → B ∈ reps m → SL2Z_M m M A = B → A = B :=
begin
  rintros ⟨a, b, c, d, H9⟩ ⟨e, f, g, h, H10⟩ ⟨i, j, k, l, H11⟩ ⟨H1, H2, H3, H4⟩ ⟨H5, H6, H7, H8⟩ H,
  rcases integral_matrices_with_determinant.mk.inj H with ⟨H12, H13, H14, H15⟩, clear H,
  -- TODO: cleanup this proof before it goes to mathlib
  ext;
    dsimp only at *; subst H1; subst H5;
    simp only [mul_zero, add_zero, sub_zero] at H10 H11 H12 H14;
    have H16 := (mul_eq_zero.1 H14).resolve_right (ne_of_gt H2); subst H16; clear H14;
    simp only [mul_zero, zero_mul, sub_zero, zero_add] at H9 H15;
    have H16 : a ≠ -1 := (by
    { intro H16, subst H16, rw neg_one_mul at H12, subst H12,
      rw neg_pos at H6, exact lt_asymm H2 H6 });
    cases (int.mul_eq_one.1 H9).resolve_right (mt and.left H16) with H17 H18;
    substs H17 H18; clear H9 H16;
    simp only [one_mul] at H12 H13 H15,
  { assumption },
  { substs H12 H13 H15,
    rw [← int.coe_nat_lt, int.nat_abs_of_nonneg H3] at H4,
    rw [← int.coe_nat_lt, int.nat_abs_of_nonneg H7] at H8,
    rw [← int.abs_eq_nat_abs] at H4 H8,
    conv {to_lhs, rw ← int.mod_eq_of_lt H3 H4},
    conv {to_rhs, rw ← int.mod_eq_of_lt H7 H8},
    rw [int.mod_abs, int.mod_abs, int.add_mul_mod_self] },
  { assumption }
end

variable (m)

instance reps.fintype_pos (m:ℕ+) : fintype (reps m) :=
fintype.of_equiv {v : fin (m+1) × fin (m+1) × fin (m+1) // v.1.1 * v.2.2.1 = m ∧ v.2.1.1 < v.2.2.1}
{ to_fun := λ A, ⟨⟨A.1.1.1, A.1.2.1.1, 0, A.1.2.2.1, by rw [mul_zero, sub_zero, ← int.coe_nat_mul, A.2.1, coe_coe]⟩,
    rfl, int.coe_nat_pos.2 $ nat.pos_of_ne_zero $ λ H, ne_of_gt m.2 $ A.2.1.symm.trans $ by rw [H, zero_mul],
    trivial, by simp only [int.nat_abs_of_nat, A.2.2]⟩,
  inv_fun := λ A, ⟨(⟨int.nat_abs A.1.a, nat.lt_succ_of_le $ nat.le_of_dvd m.2 ⟨int.nat_abs A.1.d,
      by have := A.1.det; simp only [A.2.1, mul_zero, sub_zero] at this;
      rw [← int.nat_abs_mul, this, coe_coe, int.nat_abs_of_nat]⟩⟩,
    ⟨int.nat_abs A.1.b, nat.lt_succ_of_le $ le_trans (le_of_lt A.2.2.2.2) $ nat.le_of_dvd m.2 ⟨int.nat_abs A.1.a,
      by have := A.1.det; simp only [A.2.1, mul_zero, sub_zero] at this;
      rw [mul_comm, ← int.nat_abs_mul, this, coe_coe, int.nat_abs_of_nat]⟩⟩,
    ⟨int.nat_abs A.1.d, nat.lt_succ_of_le $ nat.le_of_dvd m.2 ⟨int.nat_abs A.1.a,
      by have := A.1.det; simp only [A.2.1, mul_zero, sub_zero] at this;
      rw [mul_comm, ← int.nat_abs_mul, this, coe_coe, int.nat_abs_of_nat]⟩⟩),
    by have := A.1.det; simp only [A.2.1, mul_zero, sub_zero] at this;
      rw [← int.nat_abs_mul, this, coe_coe, int.nat_abs_of_nat],
    A.2.2.2.2⟩,
  left_inv := λ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨d, hd⟩⟩, H1, H2⟩, subtype.eq $ prod.ext
    (fin.eq_of_veq $ int.nat_abs_of_nat _) $ prod.ext
    (fin.eq_of_veq $ int.nat_abs_of_nat _)
    (fin.eq_of_veq $ int.nat_abs_of_nat _),
  right_inv := λ ⟨⟨a, b, c, d, H1⟩, H2, H3, H4, H5⟩, subtype.eq $
    integral_matrices_with_determinant.ext _ _ _
      (int.nat_abs_of_nonneg $ le_of_lt H3) (int.nat_abs_of_nonneg H4) (eq.symm H2) $
      int.nat_abs_of_nonneg $ le_of_not_lt $ λ H6, not_le_of_lt m.2 $
      int.coe_nat_le.1 $ show (m:ℤ) ≤ 0,
      by dsimp only at H2 H3 H4 H5; rw [H2, mul_zero, sub_zero] at H1;
      rw ← H1; from mul_nonpos_of_nonneg_of_nonpos (le_of_lt H3) (le_of_lt H6), }

def reps.fintype : Π m : ℤ, m ≠ 0 → fintype (reps m)
| (int.of_nat $ n+1) H := reps.fintype_pos ⟨n+1, nat.zero_lt_succ n⟩
| 0 H := (H rfl).elim
| -[1+ n] H := fintype.of_equiv (reps (⟨n+1, nat.zero_lt_succ _⟩:pnat))
{ to_fun := λ A, ⟨⟨A.1.a, A.1.b, A.1.c, -A.1.d,
      by have := A.1.det; rw [A.2.1, mul_zero, sub_zero] at this ⊢;
      rw [mul_neg_eq_neg_mul_symm, this]; refl⟩,
    A.2.1, A.2.2.1, A.2.2.2.1, trans_rel_left _ A.2.2.2.2 $ eq.symm $ int.nat_abs_neg _⟩,
  inv_fun := λ A, ⟨⟨A.1.a, A.1.b, A.1.c, -A.1.d,
      by have := A.1.det; rw [A.2.1, mul_zero, sub_zero] at this ⊢;
      rw [mul_neg_eq_neg_mul_symm, this]; refl⟩,
    A.2.1, A.2.2.1, A.2.2.2.1, trans_rel_left _ A.2.2.2.2 $ eq.symm $ int.nat_abs_neg _⟩,
  left_inv := λ ⟨⟨a, b, c, d, H1⟩, H2⟩, subtype.eq $
    integral_matrices_with_determinant.ext _ _ _ rfl rfl rfl (neg_neg _),
  right_inv := λ ⟨⟨a, b, c, d, H1⟩, H2⟩, subtype.eq $
    integral_matrices_with_determinant.ext _ _ _ rfl rfl rfl (neg_neg _) }

def π : reps m → quotient (action_rel $ SL2Z_M m) :=
  λ A, (@quotient.mk _ (action_rel $ SL2Z_M m)) A

section
set_option eqn_compiler.zeta true
def reps_equiv (hm : m ≠ 0) : quotient (action_rel (SL2Z_M m)) ≃ reps m :=
by letI := action_rel (SL2Z_M m); from
{ to_fun := λ x, quotient.lift_on x (λ A, (⟨reduce m A, reduce_mem_reps m hm A⟩ : reps m)) $ λ A B ⟨M, H⟩,
    let ⟨MA, HA⟩ := reduce_spec m A in
    let ⟨MB, HB⟩ := reduce_spec m B in
    subtype.eq $ reps_unique m hm (MB * M * MA⁻¹) _ _ (reduce_mem_reps m hm A) (reduce_mem_reps m hm B) $
    by simp only [is_monoid_action.mul (SL2Z_M m)];
    rw [← HA, ← is_monoid_action.mul (SL2Z_M m) MA⁻¹, inv_mul_self];
    rw [is_monoid_action.one (SL2Z_M m), H, HB],
  inv_fun := λ A, ⟦A.1⟧,
  left_inv := λ x, quotient.induction_on x $ λ A, quotient.sound $
    let ⟨MA, HA⟩ := reduce_spec m A in
    ⟨MA⁻¹, show SL2Z_M m MA⁻¹ (reduce m A) = A,
    by rw [← HA, ← is_monoid_action.mul (SL2Z_M m) MA⁻¹, inv_mul_self];
    rw [is_monoid_action.one (SL2Z_M m)]⟩,
  right_inv := λ A, subtype.eq $
    let ⟨MA, HA⟩ := reduce_spec m A in
    reps_unique m hm MA⁻¹ _ _ (reduce_mem_reps m hm A) A.2 $
    show SL2Z_M m MA⁻¹ (reduce m A) = A,
    by rw [← HA, ← is_monoid_action.mul (SL2Z_M m) MA⁻¹, inv_mul_self];
    rw [is_monoid_action.one (SL2Z_M m)] }
end

protected def decidable_eq (hm : m ≠ 0) : decidable_eq (quotient (action_rel (SL2Z_M m))) :=
equiv.decidable_eq (reps_equiv m hm)

def finiteness (hm : m ≠ 0) : fintype (quotient $ action_rel $ SL2Z_M m) :=
@fintype.of_equiv _ _ (reps.fintype m hm) (reps_equiv m hm).symm

end SL2Z_M
