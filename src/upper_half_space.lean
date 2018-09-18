import data.complex.basic
import .modular_group
import tactic.linarith

open complex

def upper_half_space := {z : ℂ | z.im > 0}
local notation `ℍ` := upper_half_space
local notation `Mat` := integral_matrices_with_determinant

instance upper_half_space.to_complex : has_coe ℍ ℂ := ⟨λ z, z.val⟩

noncomputable def «Möbius_transform» (a b c d : ℝ) (z : ℂ) : ℂ :=
(↑a * z + b) / (c * z + d)

theorem preserve_ℍ.aux {a b c d : ℝ} (det : a * d - b * c > 0) {z : ℂ} (hz : z ∈ ℍ) :
  ↑c * z + ↑d ≠ 0 :=
begin
  intro H,
  have H1 : c = 0 ∨ z.im = 0, by simpa using congr_arg complex.im H,
  cases H1,
  { simp [H1, of_real_zero] at H,
    simp [H, H1] at det,
    linarith },
  change z.im > 0 at hz,
  linarith,
end

lemma preserve_ℍ {a b c d : ℝ} (det : a * d - b * c > 0) (z : ℂ) (h : z.im > 0) :
(«Möbius_transform» a b c d z).im > 0 :=
calc _ = (a * d - b * c) * z.im * (norm_sq (↑c * z + ↑d))⁻¹ :
  by simp [«Möbius_transform», div_eq_mul_inv, -add_comm]; ring
   ... > 0 : mul_pos (mul_pos det h) (inv_pos (norm_sq_pos.2 (preserve_ℍ.aux det h)))

noncomputable def M_trans {m : ℤ} (hm : 0 < m) (A : Mat m) (z : ℍ) : ℍ :=
begin
  refine ⟨«Möbius_transform» A.a A.b A.c A.d z, preserve_ℍ _ _ z.2⟩,
  show 0 < (A.a * A.d - A.b * A.c : ℝ),
  rwa [← int.cast_mul, ← int.cast_mul, ← int.cast_sub, ← int.cast_zero, int.cast_lt, A.det],
end

theorem SL2Z_H.aux {a b c d : ℤ} (h : a * d - b * c = 1) : (a : ℝ) * d - b * c > 0 :=
by convert zero_lt_one; simpa using congr_arg (coe : ℤ → ℝ) h

noncomputable def SL2Z_H : SL2Z → ℍ → ℍ :=
λ M z, ⟨«Möbius_transform» M.a M.b M.c M.d z, preserve_ℍ (SL2Z_H.aux M.det) z z.property⟩

@[simp] lemma SL2Z_H_val (A z) : (SL2Z_H A z).val = ((A.a:ℝ) * z.1 + (A.b:ℝ)) / ((A.c:ℝ) * z.1 + (A.d:ℝ)) := rfl

noncomputable instance : is_group_action SL2Z_H :=
{ mul := λ ⟨a1, b1, c1, d1, H1⟩ ⟨a2, b2, c2, d2, H2⟩ ⟨z, hz⟩,
    begin
      apply subtype.eq,
      simp only [SL2Z_H_val, SL2Z_mul_a, SL2Z_mul_b, SL2Z_mul_c, SL2Z_mul_d,
        of_real_add, of_real_mul, int.cast_add, int.cast_mul],
      have H3 := preserve_ℍ.aux (SL2Z_H.aux H2) hz,
      have H4 := preserve_ℍ.aux (SL2Z_H.aux H1)
        (preserve_ℍ (SL2Z_H.aux H2) z hz),
      simp only [«Möbius_transform»] at H3 H4,
      rw ← mul_div_mul_right _ H4 H3,
      conv { to_rhs,
        rw [add_mul, add_mul, mul_assoc, mul_assoc],
        rw [div_mul_cancel _ H3] },
      congr' 1; simp only [add_mul, mul_add, mul_assoc, add_left_comm, add_assoc]
    end,
  one := λ ⟨z, hz⟩, subtype.eq $ by simp [of_real_zero] }