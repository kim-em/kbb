import .modular_group

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

namespace SL2Z

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

@[simp, SL2Z] lemma S_mul_a (A : SL2Z) : (S * A).a = -A.c := by simp
@[simp, SL2Z] lemma S_mul_b (A : SL2Z) : (S * A).b = -A.d := by simp
@[simp, SL2Z] lemma S_mul_c (A : SL2Z) : (S * A).c = A.a := by simp
@[simp, SL2Z] lemma S_mul_d (A : SL2Z) : (S * A).d = A.b := by simp
@[simp, SL2Z] lemma T_mul_a (A : SL2Z) : (T * A).a = A.a + A.c := by simp
@[simp, SL2Z] lemma T_mul_b (A : SL2Z) : (T * A).b = A.b + A.d := by simp
@[simp, SL2Z] lemma T_mul_c (A : SL2Z) : (T * A).c = A.c := by simp
@[simp, SL2Z] lemma T_mul_d (A : SL2Z) : (T * A).d = A.d := by simp

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
protected theorem induction_on {C : SL2Z → Prop} (A : SL2Z)
  (H1 : C 1) (HS : ∀ B, C B → C (S * B))
  (HT : ∀ B, C B → C (T * B)) : C A :=
have HS1 : ∀ B, C (S * B) → C B,
  from λ B ih, have H : _ := (HS _ $ HS _ $ HS _ ih),
  by rw [← mul_assoc, ← mul_assoc, ← mul_assoc] at H;
  change C(1*B) at H; rwa [one_mul] at H,
have HT1 : ∀ B, C B → C (T⁻¹ * B),
  from λ B ih,
  by have H := (HS _ $ HS _ $ HS _ $ HT _ $ HS _ $ HT _ $ HS _ ih);
  rwa [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc] at H,
have HT2 : ∀ n : ℤ, C (T^n),
  from λ n, int.induction_on n H1
    (λ i ih, by rw [add_comm, gpow_add]; from HT _ ih)
    (λ i ih, by rw [sub_eq_neg_add, gpow_add]; from HT1 _ ih),
have HT3 : ∀ B, C (T * B) → C B, from λ B ih,
  by simpa only [inv_mul_cancel_left] using HT1 _ ih,
have HT4 : ∀ B, C (T⁻¹ * B) → C B, from λ B ih,
  by simpa only [mul_inv_cancel_left] using HT _ ih,
have HT5 : ∀ B (n:ℤ), C (T^n * B) → C B, from λ B n,
  int.induction_on n (by rw [gpow_zero, one_mul]; from id)
    (λ i ih1 ih2, ih1 $ HT3 _ $ by rwa [add_comm, gpow_add, mul_assoc, gpow_one] at ih2)
    (λ i ih1 ih2, ih1 $ HT4 _ $ by rwa [sub_eq_neg_add, gpow_add, mul_assoc, gpow_neg_one] at ih2),
suffices ∀ n (A : SL2Z), n = int.nat_abs A.c → C A,
  from this _ _ rfl,
λ n, nat.strong_induction_on n $ λ n,
assume ih : ∀ m, m < n → ∀ (A : SL2Z), m = int.nat_abs (A.c) → C A,
show ∀ (A : SL2Z), n = int.nat_abs (A.c) → C A,
from λ A H1, or.cases_on (nat.eq_zero_or_eq_succ_pred n)
(assume H2 : n = 0, have H3 : A.c = 0, from int.eq_zero_of_nat_abs_eq_zero (H1.symm.trans H2),
  have H4 : A.a * A.d = 1, by simpa only [H3, mul_zero, sub_zero] using A.det,
  or.cases_on (int.mul_eq_one.1 H4)
    (λ ⟨H5, H6⟩, have H7 : A = T^A.b,
        by ext; simp only [H3, H5, H6] with SL2Z,
      by rw H7; apply HT2)
    (λ ⟨H5, H6⟩, have H7 : A = S * (S * T^(-A.b)),
        by rw [← mul_assoc, S_mul_S]; ext; simp only [H3, H5, H6, neg_neg, neg_zero] with SL2Z,
      by rw H7; solve_by_elim))
(assume H2 : n = n.pred.succ, or.cases_on (lt_or_le (int.nat_abs A.a) n)
  (assume H3 : int.nat_abs (A.a) < n, HS1 _ $ ih _
    (by simpa only [one_mul, zero_mul, add_zero] with SL2Z) _ rfl)
  (assume H3 : n ≤ int.nat_abs (A.a), HT5 _ (-(A.a/A.c)) $ HS1 _ $
    have H4 : A.c ≠ 0, from λ H, by rw H at H1; rw H1 at H2; from absurd H2 dec_trivial,
    ih _ (by simp only [one_mul, zero_mul, add_zero] with SL2Z;
      rw [mul_comm, mul_neg_eq_neg_mul_symm, ← sub_eq_add_neg, ← int.mod_def];
      rw [← int.coe_nat_lt, int.nat_abs_of_nonneg (int.mod_nonneg _ H4)];
      rw [H1, ← int.abs_eq_nat_abs]; from int.mod_lt _ H4) _ rfl))

theorem closure : group.closure ({S, T} : set SL2Z) = set.univ :=
set.eq_univ_of_forall $ λ A, SL2Z.induction_on A
  (group.in_closure.one _)
  (λ B ih, group.in_closure.mul (group.in_closure.basic $ or.inr $ or.inl rfl) ih)
  (λ B ih, group.in_closure.mul (group.in_closure.basic $ or.inl rfl) ih)

end SL2Z