import .modular_group
import .action

lemma mul_pos_iff {α : Type*} [linear_ordered_ring α] (a b : α) :
  0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) :=
iff.intro  pos_and_pos_or_neg_and_neg_of_mul_pos $ assume h,
match h with
| or.inl ⟨ha, hb⟩ := mul_pos ha hb
| or.inr ⟨ha, hb⟩ := mul_pos_of_neg_of_neg ha hb
end

@[simp] lemma not_one_lt_zero {α : Type*} [linear_ordered_semiring α] : ¬ (1:α) < 0 :=
not_lt_of_gt zero_lt_one

namespace int

theorem mul_eq_one {m n : ℤ} :
  m * n = 1 ↔ m = 1 ∧ n = 1 ∨ m = -1 ∧ n = -1 :=
⟨λ H, or.cases_on (int.units_eq_one_or ⟨m, n, H, by rwa [mul_comm] at H⟩)
  (λ H1, have H2 : m = 1, from units.ext_iff.1 H1,
    or.inl ⟨H2, by rwa [H2, one_mul] at H⟩)
  (λ H1, have H2 : m = -1, from units.ext_iff.1 H1,
    or.inr ⟨H2, by rwa [H2, neg_one_mul, neg_eq_iff_neg_eq, eq_comm] at H⟩),
by simp [or_imp_distrib] {contextual := tt}⟩

lemma nat_abs_lt_nat_abs (i k : ℤ) (hi : 0 ≤ i) (h : i < abs k) : nat_abs i < nat_abs k :=
coe_nat_lt.1 $ by rwa [nat_abs_of_nonneg hi, ← int.abs_eq_nat_abs]

end int

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

@[elab_as_eliminator]
def reduce_rec (m : ℤ) {C : Mat m → Sort*}
  (h₀ : ∀A:Mat m, A.c = 0 → C A)
  (h₁ : ∀A:Mat m, int.nat_abs A.c ≠ 0 → C (reduce_step A) → C A) :
  ∀A, C A | A :=
if hc : int.nat_abs A.c = 0 then h₀ A (int.eq_zero_of_nat_abs_eq_zero hc)
else
  have int.nat_abs (reduce_step A).c < int.nat_abs A.c, from reduce_aux m A hc,
  h₁ A hc (reduce_rec (reduce_step A))
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ integral_matrices_with_determinant.c)⟩]}

/-- correct if m ≠ 0 -/
def reduce (m : ℤ) : Mat m → Mat m | A :=
if hc : int.nat_abs A.c = 0
then if ha : 0 < A.a
  then SL2Z_M m (T^(-(A.b/A.d))) A
  else SL2Z_M m (T^(-(-A.b/ -A.d))) (SL2Z_M m S (SL2Z_M m S A))
else
  have int.nat_abs (reduce_step A).c < int.nat_abs A.c, from reduce_aux m A hc,
  reduce (reduce_step A)
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ integral_matrices_with_determinant.c)⟩]}

@[simp] theorem reduce_eq1 (m : ℤ) {A : Mat m} (hc : int.nat_abs A.c = 0) (ha : 0 < A.a) :
  reduce m A = SL2Z_M m (T^(-(A.b/A.d))) A :=
by rw [reduce.equations._eqn_1 _ _, if_pos hc, if_pos ha]; refl

@[simp] theorem reduce_eq2 (m : ℤ) {A : Mat m} (hc : int.nat_abs A.c = 0) (ha : ¬ 0 < A.a) :
  reduce m A = SL2Z_M m (T^(-(-A.b/ -A.d))) (SL2Z_M m S (SL2Z_M m S A)) :=
by rw [reduce.equations._eqn_1 _ _, if_pos hc, if_neg ha]; refl

@[simp] theorem reduce_eq3 (m : ℤ) {A : Mat m} (h : int.nat_abs A.c ≠ 0) :
  reduce m A = reduce m (reduce_step A) :=
by rw [reduce.equations._eqn_1 _ _, if_neg h]

theorem reduce_spec (m : ℤ) : ∀A : Mat m, ∃ S, SL2Z_M m S A = reduce m A :=
begin
  refine reduce_rec m _ _,
  { intros A hc,
    by_cases ha : 0 < A.a,
    { simp [*], exact ⟨_, rfl⟩ },
    { simp [*, (is_monoid_action.mul (SL2Z_M m) _ _ _).symm], exact ⟨_, rfl⟩ } },
  { rintros A hc ⟨S, eq⟩,
    rw [reduce_eq3 m hc, ← eq, reduce_step, ← is_monoid_action.mul (SL2Z_M m), ← is_monoid_action.mul (SL2Z_M m)],
    exact ⟨_, rfl⟩ }
end

theorem reduce_mem_reps (m : ℤ) (hm : m ≠ 0) : ∀(A : Mat m), reduce m A ∈ reps m :=
begin
  refine reduce_rec m (assume A (c_eq : A.c = 0), _) (assume A hc ih, _),
  { have hd : A.d ≠ 0, { intro d_eq, apply hm, rw [← A.det, d_eq, c_eq, mul_zero, mul_zero, sub_zero] },
    have eq : ∀b d, b + -(b / d * d) = b % d, { intros, rw [← sub_eq_add_neg, mul_comm, ← int.mod_def] },
    have h : ∀(a b : ℤ), 0 < a → 0 < a ∧ 0 ≤ b % A.d ∧ int.nat_abs (b % A.d) < int.nat_abs A.d :=
      assume a b ha, ⟨ha, int.mod_nonneg _ hd, int.nat_abs_lt_nat_abs _ _ (int.mod_nonneg _ hd) (int.mod_lt _ hd)⟩,
    by_cases ha : 0 < A.a,
    { simpa [reduce_eq1, reps, c_eq, ha, eq] using h _ _ ha },
    { have a_ne : A.a ≠ 0,
      { intro a_eq, apply hm, rw [← A.det, a_eq, c_eq, zero_mul, mul_zero, sub_zero] },
      have a_pos : -A.a > 0 := neg_pos_of_neg (lt_of_le_of_ne (le_of_not_gt ha) a_ne),
      simpa [reduce_eq2, reps, c_eq, ha, eq] using h _ _ a_pos } },
  { rwa [reduce_eq3 m hc] }
end

@[elab_as_eliminator]
protected theorem induction_on {C : Mat m → Prop} (A : Mat m) (mne0 : m ≠ 0)
  (h0 : ∀{A:Mat m}, A.c = 0 → A.a * A.d = m → 0 < A.a → 0 ≤ A.b → int.nat_abs A.b < int.nat_abs A.d → C A)
  (hS : ∀ B, C B → C (SL2Z_M m S B)) (hT : ∀ B, C B → C (SL2Z_M m T B)) :
  C A :=
have S_eq : ∀ B, (SL2Z_M m S (SL2Z_M m S (SL2Z_M m S (SL2Z_M m S B)))) = B,
  by intro b; ext; simp,
have hS' : ∀{B}, C (SL2Z_M m S B) → C B, from
  λ B ih, have h : _ := (hS _ $ hS _ $ hS _ ih), by rwa S_eq B at h,
have eq : ∀ B,
  (SL2Z_M m S $ SL2Z_M m S $ SL2Z_M m S $ SL2Z_M m T $ SL2Z_M m S $ SL2Z_M m T $ SL2Z_M m S B) =
    SL2Z_M m T⁻¹ B,
  by intro b; repeat {rw [←is_monoid_action.mul (SL2Z_M m)]}; congr,
have hT_inv : ∀ B, C B → C (SL2Z_M m T⁻¹ B), from
  λ B ih, have h : _ := (hS _ $ hS _ $ hS _ $ hT _ $ hS _ $ hT _ $ hS _ ih), by rwa eq at h,
have hT' : ∀B, C (SL2Z_M m T B) → C B,
{ assume B ih,
  have h := hT_inv (SL2Z_M m T B) ih,
  rwa [←is_monoid_action.mul (SL2Z_M m), mul_left_inv, is_monoid_action.one (SL2Z_M m)] at h },
have hT_inv' : ∀ B, C (SL2Z_M m T⁻¹ B) → C B,
{ assume B ih,
  have H := hT (SL2Z_M m T⁻¹ B) ih,
  rwa [←is_monoid_action.mul (SL2Z_M m), mul_right_inv, is_monoid_action.one (SL2Z_M m)] at H },
have hTpow' : ∀{B} {n:ℤ}, C (SL2Z_M m (T^n) B) → C B,
{ refine assume B n, int.induction_on n (λh, _) (λi ih1 ih2, ih1 $ hT' _ _) (λi ih1 ih2, ih1 $ hT_inv' _ _),
  { rwa [gpow_zero, is_monoid_action.one (SL2Z_M m)] at h },
  { rwa [add_comm, gpow_add, gpow_one, is_monoid_action.mul (SL2Z_M m)] at ih2 },
  { rwa [sub_eq_neg_add, gpow_add, gpow_neg_one, is_monoid_action.mul (SL2Z_M m)] at ih2 } },
have h_reduce : C (reduce m A),
{ rcases reduce_mem_reps m mne0 A with ⟨H1, H2, H3, H4⟩,
  refine h0 H1 _ H2 H3 H4,
  simpa only [H1, mul_zero, sub_zero] using (reduce m A).det },
suffices ∀A : Mat m, C (reduce m A) → C A, from this _ h_reduce,
begin
  refine reduce_rec m _ _,
  { assume A c_eq ih,
    by_cases ha : 0 < A.a,
    { simp [reduce_eq1, c_eq, ha, -gpow_neg] at ih, exact hTpow' ih },
    { simp [reduce_eq2, c_eq, ha] at ih, exact (hS' $ hS' $ hTpow' ih) } },
  { assume A hc ih hA,
    rw [reduce_eq3 m hc] at hA,
    exact (hTpow' $ hS' $ ih hA) }
end

theorem reps_unique (m : ℤ) (hm : m ≠ 0) :
  ∀(M : SL2Z) (A B : Mat m), A ∈ reps m → B ∈ reps m → SL2Z_M m M A = B → A = B :=
begin
  rintros ⟨a, b, c, d, _⟩ ⟨e, f, g, h, _⟩ ⟨i, j, k, l, _⟩
    ⟨g_eq, e_pos, f_nonneg, f_bound⟩ ⟨k_eq, H6, f'_nonneg, f'_bound⟩ B_eq,
  rcases integral_matrices_with_determinant.mk.inj B_eq with ⟨i_eq, j_eq, ce_0, _⟩, clear B_eq,
  dsimp only at *,
  subst g_eq, subst k_eq, subst j_eq, subst i_eq,
  have : c = 0, { simp at ce_0, rcases ce_0 with rfl | rfl, { refl }, exact (irrefl _ e_pos).elim },
  subst this,
  have : a = 1, { by_contradiction, simp [*, int.mul_eq_one, mul_pos_iff, neg_pos, not_lt_of_gt e_pos] at * },
  subst this,
  by_cases hb : b ≠ 0; by_cases hh : h ≠ 0; cases_matching* [_ ∧ _, _ ∨ _]; subst_vars;
    simp [*, neg_pos, int.coe_nat_lt.symm, (int.abs_eq_nat_abs _).symm] at *,
  { rw [abs_of_nonneg f_nonneg] at f_bound,
    rw [abs_of_nonneg f'_nonneg] at f'_bound,
    rw [← int.mod_eq_of_lt f'_nonneg f'_bound, ← int.mod_eq_of_lt f_nonneg f_bound],
    simp }
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
      by dsimp only at H2 H3 H4 H5;
        rw [H2, mul_zero, sub_zero] at H1;
        rw ← H1;
      from mul_nonpos_of_nonneg_of_nonpos (le_of_lt H3) (le_of_lt H6), }

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
