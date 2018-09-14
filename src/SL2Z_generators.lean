import .modular_group
import .action

theorem int.mul_eq_one {m n : ℤ} :
  m * n = 1 ↔ m = 1 ∧ n = 1 ∨ m = -1 ∧ n = -1 :=
⟨λ H, or.cases_on (int.units_eq_one_or ⟨m, n, H, by rwa [mul_comm] at H⟩)
  (λ H1, have H2 : m = 1, from units.ext_iff.1 H1, or.inl ⟨H2,
    by rwa [H2, one_mul] at H⟩)
  (λ H1, have H2 : m = -1, from units.ext_iff.1 H1, or.inr ⟨H2,
    by rwa [H2, neg_one_mul, neg_eq_iff_neg_eq, eq_comm] at H⟩),
λ H, or.cases_on H
  (λ ⟨H1, H2⟩, by rw [H1, H2]; refl)
  (λ ⟨H1, H2⟩, by rw [H1, H2]; refl)⟩

namespace SL2Z_M_

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

@[simp, SL2Z] lemma S_mul_a (A : Mat m) : (SL2Z_M_ m S A).a = -A.c := by simp [SL2Z_M_]
@[simp, SL2Z] lemma S_mul_b (A : Mat m) : (SL2Z_M_ m S A).b = -A.d := by simp [SL2Z_M_]
@[simp, SL2Z] lemma S_mul_c (A : Mat m) : (SL2Z_M_ m S A).c = A.a := by simp [SL2Z_M_]
@[simp, SL2Z] lemma S_mul_d (A : Mat m) : (SL2Z_M_ m S A).d = A.b := by simp [SL2Z_M_]
@[simp, SL2Z] lemma T_mul_a (A : Mat m) : (SL2Z_M_ m T A).a = A.a + A.c := by simp [SL2Z_M_]
@[simp, SL2Z] lemma T_mul_b (A : Mat m) : (SL2Z_M_ m T A).b = A.b + A.d := by simp [SL2Z_M_]
@[simp, SL2Z] lemma T_mul_c (A : Mat m) : (SL2Z_M_ m T A).c = A.c := by simp [SL2Z_M_]
@[simp, SL2Z] lemma T_mul_d (A : Mat m) : (SL2Z_M_ m T A).d = A.d := by simp [SL2Z_M_]

lemma T_pow_aux (n : ℤ) : (T^n).a = 1 ∧ (T^n).b = n ∧ (T^n).c = 0 ∧ (T^n).d = 1 :=
int.induction_on n dec_trivial
  (λ i, by simp [gpow_add] {contextual:=tt})
  (λ i, by simp [gpow_add] {contextual:=tt})
@[simp, SL2Z] lemma T_pow_a (n : ℤ) : (T^n).a = 1 := (T_pow_aux n).1
@[simp, SL2Z] lemma T_pow_b (n : ℤ) : (T^n).b = n := (T_pow_aux n).2.1
@[simp, SL2Z] lemma T_pow_c (n : ℤ) : (T^n).c = 0 := (T_pow_aux n).2.2.1
@[simp, SL2Z] lemma T_pow_d (n : ℤ) : (T^n).d = 1 := (T_pow_aux n).2.2.2

@[simp, SL2Z] lemma S_mul_S : S * S = -1 := rfl

@[elab_as_eliminator]
protected theorem induction_on {C : (Mat m) → Prop} (A : Mat m) (mne0 : m ≠ 0)
  (H0 : ∀ {A : Mat m} (h0 : A.c = 0) (h1 : A.a * A.d = m) (h2 : 0 ≤ A.a) (h3 : 0 ≤ A.b) (h4 : int.nat_abs A.b ≤ int.nat_abs A.d), C A)
  (HS : ∀ B, C B → C (SL2Z_M_ m S B)) (HT : ∀ B, C B → C (SL2Z_M_ m T B)) : C A :=
have hSid : ∀ B, (SL2Z_M_ m S (SL2Z_M_ m S (SL2Z_M_ m S (SL2Z_M_ m S B)))) = B, from λ B, by ext; simp [SL2Z_M_],
have hneg : ∀ B, (SL2Z_M_ m S (SL2Z_M_ m S B)) = -B, from λ B, by ext; simp [SL2Z_M_],
have HS' : ∀ B, C (SL2Z_M_ m S B) → C B,
  from λ B ih, have H : _ := (HS _ $ HS _ $ HS _ ih), by rwa hSid B at H,
have Hneg : ∀ B, C (-B) → C B, from λ B ih, by rw ←hneg B at ih; apply (HS' _ $ HS' _ ih),
have hTinv : ∀ B, SL2Z_M_ m S (SL2Z_M_ m S (SL2Z_M_ m S (SL2Z_M_ m T (SL2Z_M_ m S (SL2Z_M_ m T (SL2Z_M_ m S B)))))) = SL2Z_M_ m T⁻¹ B,
  from λ B, by repeat {rw [←is_monoid_action.mul (SL2Z_M_ m)]}; congr,
have HT' : ∀ B, C B → C (SL2Z_M_ m T⁻¹ B),
  from λ B ih, by {have H := (HS _ $ HS _ $ HS _ $ HT _ $ HS _ $ HT _ $ HS _ ih), by rwa [hTinv] at H},
have HT3 : ∀ B, C (SL2Z_M_ m T B) → C B, from λ B ih,
  begin
    have H := HT' (SL2Z_M_ m T B) ih,
    rw [←is_monoid_action.mul (SL2Z_M_ m)] at H,
    rw mul_left_inv at H,
    rw [is_monoid_action.one (SL2Z_M_ m)] at H,
    exact H
  end,
have HT4 : ∀ B, C (SL2Z_M_ m T⁻¹ B) → C B, from λ B ih,
  begin
    have H := HT (SL2Z_M_ m T⁻¹ B) ih,
    rw [←is_monoid_action.mul (SL2Z_M_ m)] at H,
    simp at H,
    rw [is_monoid_action.one (SL2Z_M_ m)] at H,
    exact H
  end,
have HT5 : ∀ B (n:ℤ), C (SL2Z_M_ m (T^n) B) → C B, from λ B n,
  int.induction_on n (by rw [gpow_zero, is_monoid_action.one (SL2Z_M_ m)]; from id)
    (λ i ih1 ih2, ih1 $ HT3 _ $ begin
      conv { congr, rw ←is_monoid_action.mul (SL2Z_M_ m) },
      conv at ih2 { congr, rw [add_comm, gpow_add, gpow_one] },
      assumption end)
    (λ i ih1 ih2, ih1 $ HT4 _ $ begin
      conv { congr, rw ←is_monoid_action.mul (SL2Z_M_ m) },
      conv at ih2 { congr, rw [sub_eq_neg_add, gpow_add, gpow_neg_one] },
      assumption end),
suffices ∀ n (A : Mat m), int.nat_abs A.c = n → C A,
  from this _ _ rfl,
λ n_stupid, nat.strong_induction_on n_stupid $ λ n,
assume ih : ∀ k, k < n → ∀ (A : Mat m), int.nat_abs (A.c) = k → C A,
show ∀ (A : Mat m), int.nat_abs (A.c) = n → C A,
from λ A H1, or.cases_on (nat.eq_zero_or_eq_succ_pred n)
(assume H2 : n = 0, have H3 : A.c = 0, from int.eq_zero_of_nat_abs_eq_zero (H1.trans H2),
  have H4 : A.a * A.d = m, by simpa only [H3, mul_zero, sub_zero] using A.det,
    show C A,
begin
  clear H1,
  revert A,
  suffices : ∀ (A : Mat m), A.c = 0 → A.a * A.d = m → 0 ≤ A.a → C A,
  intros A h0 h1,
  cases (lt_or_le A.a 0) with h2 h2,
  { exact (Hneg _ $ this (-A) (by simp [h0]) (by simp [h1]) (by simp [le_of_lt,h2])) },
  { exact this A h0 h1 h2 },
  suffices : ∀ (A : Mat m), A.c = 0 → A.a * A.d = m → 0 ≤ A.a → 0 ≤ A.b → C A,
  intros A h0 h1 h2,
  cases (lt_or_le A.b 0) with h3 h3,
  { refine (HT5 _ (-A.b * A.d) $ this ((SL2Z_M_ m (T ^ (-A.b * A.d)) A))
      (by simp [SL2Z_M_,h0]) (by simp [SL2Z_M_,h0,h1]) (by simp [SL2Z_M_,h0,h2]) _),
    { suffices : 0 ≤ A.b +-(A.b * A.d * A.d), by simp [SL2Z_M_, h0, this],
      rw show A.b +-(A.b * A.d * A.d) = (-A.b)*(A.d * A.d - 1), by ring,
      apply mul_nonneg (le_of_lt (neg_pos.2 h3)),
      have d_ne : A.d ≠ 0,
      { rw ←h1 at mne0,
        exact ne_zero_of_mul_ne_zero_left mne0 },
      apply sub_nonneg_of_le,
      simpa using int.add_one_le_of_lt (mul_self_pos d_ne) } },
  { exact this A h0 h1 h2 h3 },
  {intros A h0 h1 h2 h3,
    by_cases h4 : (int.nat_abs A.b ≤ int.nat_abs A.d),
    { exact H0 h0 h1 h2 h3 h4 },
    { apply HT5 _ (-(A.b/A.d)),
      apply H0; simp [SL2Z_M_,h0,h1,h2,h3],
      { apply le_add_of_neg_add_le,
        rw [add_zero, neg_le_neg_iff],
        apply int.div_mul_le,
        intro nope, rw [nope, mul_zero] at h1,
        exact mne0 h1.symm },
      have d_ne : A.d ≠ 0,
          { rw ←h1 at mne0,
            exact ne_zero_of_mul_ne_zero_left mne0 },
      conv {to_lhs, congr,congr, rw ←int.mod_add_div A.b A.d},
      have triv : A.d * (A.b / A.d) + -(A.b / A.d * A.d) = 0,
        by { rw mul_comm, ring, rw sub_eq_zero },
      suffices : int.nat_abs (A.b % A.d) ≤ int.nat_abs (A.d), by simp [this, triv],
      rw [←int.coe_nat_le, int.nat_abs_of_nonneg (int.mod_nonneg A.b d_ne),
          ←int.abs_eq_nat_abs],
      exact le_of_lt (int.mod_lt A.b d_ne) } }
end)
(assume H2 : n = n.pred.succ, or.cases_on (lt_or_le (int.nat_abs A.a) n)
  (assume H3 : int.nat_abs (A.a) < n, HS' _ $ ih _
    (by simpa only [one_mul, zero_mul, add_zero] with SL2Z) _ rfl)
  (assume H3 : n ≤ int.nat_abs (A.a), HT5 _ (-(A.a/A.c)) $ HS' _ $
    have H4 : A.c ≠ 0, from λ H, by rw H at H1; rw ←H1 at H2; from absurd H2 dec_trivial,
    ih _ (by simp only [one_mul, zero_mul, add_zero, SL2Z_M_] with SL2Z;
      rw [mul_comm, mul_neg_eq_neg_mul_symm, ← sub_eq_add_neg, ← int.mod_def];
      rw [← int.coe_nat_lt, int.nat_abs_of_nonneg (int.mod_nonneg _ H4)];
      rw [← H1, ← int.abs_eq_nat_abs]; from int.mod_lt _ H4) _ rfl))

-- theorem closure : group.closure ({S, T} : set SL2Z) = set.univ :=
-- set.eq_univ_of_forall $ λ A, SL2Z_M_.induction_on A
--   (group.in_closure.one _)
--   (λ B ih, group.in_closure.mul (group.in_closure.basic $ or.inr $ or.inl rfl) ih)
--   (λ B ih, group.in_closure.mul (group.in_closure.basic $ or.inl rfl) ih)

-- (h0 : A.c = 0) (h1 : A.a * A.d = m) (h2 : 0 ≤ A.a) (h3 : 0 ≤ A.b)
-- (h4 : int.nat_abs A.b ≤ int.nat_abs A.d)

variable (m)

def reps : Type :=
{A : Mat m // A.c = 0 ∧ 0 ≤ A.a ∧ 0 ≤ A.b ∧ int.nat_abs A.b ≤ int.nat_abs A.d }

instance reps.fintype_pos (m:ℕ+) : fintype (reps m) :=
fintype.of_equiv {v : fin (m+1) × fin (m+1) × fin (m+1) // v.1.1 * v.2.2.1 = m ∧ v.2.1.1 ≤ v.2.2.1}
{ to_fun := λ A, ⟨⟨A.1.1.1, A.1.2.1.1, 0, A.1.2.2.1, by rw [mul_zero, sub_zero, ← int.coe_nat_mul, A.2.1, coe_coe]⟩,
    rfl, trivial, trivial, by simp only [int.nat_abs_of_nat, A.2.2]⟩,
  inv_fun := λ A, ⟨(⟨int.nat_abs A.1.a, nat.lt_succ_of_le $ nat.le_of_dvd m.2 ⟨int.nat_abs A.1.d,
      by have := A.1.det; simp only [A.2.1, mul_zero, sub_zero] at this;
      rw [← int.nat_abs_mul, this, coe_coe, int.nat_abs_of_nat]⟩⟩,
    ⟨int.nat_abs A.1.b, nat.lt_succ_of_le $ le_trans A.2.2.2.2 $ nat.le_of_dvd m.2 ⟨int.nat_abs A.1.a,
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
      (int.nat_abs_of_nonneg H3) (int.nat_abs_of_nonneg H4) (eq.symm H2) $
      int.nat_abs_of_nonneg $ le_of_not_lt $ λ H6, not_le_of_lt m.2 $
      int.coe_nat_le.1 $ show (m:ℤ) ≤ 0,
      by dsimp only at H2 H3 H4 H5; rw [H2, mul_zero, sub_zero] at H1;
      rw ← H1; from mul_nonpos_of_nonneg_of_nonpos H3 (le_of_lt H6), }

instance reps.fintype : Π m : ℤ, m ≠ 0 → fintype (reps m)
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

def π : reps m → quotient (action_rel $ SL2Z_M_ m) :=
  λ A, (@quotient.mk _ (action_rel $ SL2Z_M_ m)) A.1

lemma reps_reps : m ≠ 0 → function.surjective (π m) :=
begin
  letI := action_rel (SL2Z_M_ m),
  rintros m_ne ⟨A⟩,
  apply SL2Z_M_.induction_on A m_ne,
  { intros M h0 h1 h2 h3 h4,
    existsi (⟨M, ⟨h0, h2, h3, h4⟩⟩ : reps m),
    refl },
  all_goals
  { rintros M ⟨M', H⟩,
    existsi M',
    rw H,
    apply quot.sound },
  { existsi S, refl },
  { existsi T, refl }
end

instance finitely_many_orbits {m : ℤ} [m ≠ 0] :
fintype (quotient (action_rel (SL2Z_M_ m))) :=
@fintype.of_surjective _ _ (reps.fintype m ‹m ≠ 0›) sorry (π m) (reps_reps m ‹m ≠ 0›)

instance SL2Z_M_.decidable : Π A B, decidable (∃ S : SL2Z, SL2Z_M_ m S A = B) :=
sorry

instance : decidable_eq (quotient (action_rel (SL2Z_M_ m))) :=
@quotient.decidable_eq _ _ $ by intros X Y; from SL2Z_M_.decidable m X Y
#check equiv.decidable_eq_of_equiv
def finiteness : m ≠ 0 → fintype (quotient $ action_rel $ SL2Z_M_ m) :=
λ h, @fintype.of_surjective _ _ (reps.fintype _ h) _ (π m) (@reps_reps m h)
end SL2Z_M_
