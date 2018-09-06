import tactic.ring
import data.complex.basic
import group_theory.group_action
import algebra.module
import algebra.pi_instances
import linear_algebra.subtype_module
import .modular_group
import .holomorphic_functions

universes u v

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

structure is_modular_form (k : ℕ) (f : ℍ → ℂ) : Prop :=
(hol      : is_holomorphic f)
(transf   : ∀ M : SL2Z, ∀ z : ℍ, f (SL2Z_H M z) = (M.c*z + M.d)^k * f z)
(infinity : ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M)

def modular_forms (k : ℕ) := {f : ℍ → ℂ | is_modular_form k f}

-- I would like to remove the following line... but I can't
instance foobar (X : Type u) (R : Type v) [ring R] : module R (X → R) := pi.module

instance (k : ℕ) : is_submodule (modular_forms k) :=
{ zero_ := begin
    fsplit,
    { sorry },
    { intros M z,
      simp },
    { existsi (0 : ℝ),
      existsi (0 : ℝ),
      intros,
      simp }
  end,
  add_  := begin
    intros f g hf hg,
    fsplit,
    { sorry },
    { intros M z,
      suffices : f (SL2Z_H M z) + g (SL2Z_H M z) = (↑(M.c) * ↑z + ↑(M.d)) ^ k * (f z + g z),
        by simp at *; assumption,
      rw [hf.transf, hg.transf],
      ring },
    { cases hf.infinity with Mf hMf,
      cases hg.infinity with Mg hMg,
      cases hMf with Af hAMf,
      cases hMg with Ag hAMg,
      existsi (Mf + Mg),
      existsi (max Af Ag),
      intros z hz,
      simp,
      apply le_trans (complex.abs_add _ _),
      apply add_le_add,
      { refine hAMf z _,
        exact le_trans (le_max_left _ _) hz },
      { refine hAMg z _,
        exact le_trans (le_max_right _ _) hz } }
  end,
  smul  := begin
    intros c f hyp,
    fsplit,
    { sorry },
    { intros M z,
      suffices : c * f (SL2Z_H M z) = (↑(M.c) * ↑z + ↑(M.d)) ^ k * (c * f z),
        by simp at *; assumption,
      rw hyp.transf M z,
      ring },
    { cases hyp.infinity with M hM,
      cases hM with A hAM,
      existsi (abs c * M),
      existsi A,
      intros z hz,
      simp,
      apply mul_le_mul_of_nonneg_left (hAM z hz) (complex.abs_nonneg c) }
  end }

-- I would like to remove this line. But I can't...
noncomputable instance {k : ℕ} : module ℂ (modular_forms k) := subtype.module

structure is_cusp_form (k : ℕ) (f : ℍ → ℂ) : Prop :=
(hol      : is_holomorphic f)
(transf   : ∀ M : SL2Z, ∀ z : ℍ, f (SL2Z_H M z) = (M.c*z + M.d)^k * f z)
(infinity : ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε)

lemma is_modular_form_of_is_cusp_form {k : ℕ} (f : ℍ → ℂ) (h : is_cusp_form k f) : is_modular_form k f :=
⟨h.1, h.2, ⟨(1 : ℝ), h.3 1 (zero_lt_one) ⟩ ⟩

/- def Hecke_operator {k : ℕ} (m : ℤ) : modular_forms k → modular_forms k :=
λ f,
(m^k.pred : ℂ) • (sorry : modular_forms k) -- why is this • failing?
 -/