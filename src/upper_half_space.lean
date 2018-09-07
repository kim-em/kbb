import data.complex.basic
import .modular_group

open complex

def upper_half_space := {z : ℂ | z.im > 0}
local notation `ℍ` := upper_half_space

instance upper_half_space.to_complex : has_coe ℍ ℂ := ⟨λ z, z.val⟩

noncomputable def «Möbius_transform» (a b c d : ℝ) (z : ℂ) : ℂ :=
(↑a * z + b) / (c * z + d)

lemma preserve_ℍ {a b c d : ℝ} (det : a * d - b * c > 0) (z : ℂ) (h : z.im > 0) :
(«Möbius_transform» a b c d z).im > 0 :=
begin
  change ((↑a * z + ↑b) * (↑c * z + ↑d)⁻¹).im > 0,
  simp,
  let N := norm_sq (↑d + ↑c * z),
  change a * z.im * ((d + c * z.re) * N⁻¹) + (b + a * z.re) * (-(c * z.im) * N⁻¹) > 0,
  rw show a * z.im * ((d + c * z.re) * N⁻¹) + (b + a * z.re) * (-(c * z.im) * N⁻¹) = (a * d - b * c) * z.im * N⁻¹,
    by ring,
  rw mul_assoc,
  apply mul_pos det,
  apply mul_pos h,
  apply inv_pos,
  rw norm_sq_pos, clear N,
  intro h',
  have H : (↑d + ↑c * z).im = 0 := by rw [h']; simp,
  simp at H,
  cases H,
  { rw H at h',
    change ↑d + 0 * z = 0 at h',
    simp at h',
    rw [h', H] at det,
    simp at det,
    exact ne_of_gt det rfl },
  { rw H at h,
    exact ne_of_gt h rfl }
end

def aux {a b c d : ℤ} (h : a * d - b * c = 1) : (a : ℝ) * d - b * c > 0 :=
begin
  rw show (a : ℝ) * d - b * c = 1, by simpa using congr_arg (coe : ℤ → ℝ) h,
  exact zero_lt_one
end

noncomputable def SL2Z_H : SL2Z → ℍ → ℍ :=
λ M z, ⟨«Möbius_transform» M.a M.b M.c M.d z, preserve_ℍ (aux M.det) z z.property⟩

instance : is_group_action SL2Z_H := sorry