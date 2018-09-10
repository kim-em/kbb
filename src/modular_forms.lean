import tactic.ring
import tactic.monotonicity.interactive
import group_theory.group_action
import algebra.module
import algebra.pi_instances
import linear_algebra.subtype_module
import .holomorphic_functions
import .upper_half_space

universes u v

open complex

local attribute [monotonic] complex.abs_add

local notation `ℍ` := upper_half_space

def is_Petersson_weight_ (k : ℕ) := { f : ℍ → ℂ | ∀ M : SL2Z, ∀ z : ℍ, f (SL2Z_H M z) = (M.c*z + M.d)^k * f z }

def is_bound_at_infinity := { f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M }

def is_zero_at_infinity := { f : ℍ → ℂ | ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε }

instance (k : ℕ) : is_submodule (is_Petersson_weight_ k) :=
{ zero_ := λ M z, by simp,
  add_  := λ f g hf hg M z, begin
    suffices : f (SL2Z_H M z) + g (SL2Z_H M z) = (↑(M.c) * ↑z + ↑(M.d)) ^ k * (f z + g z),
      by simp at * ; assumption,
    rw [hf, hg],
    ring
  end,
  smul  := λ c f hyp M z, begin
    suffices : c * f (SL2Z_H M z) = (↑(M.c) * ↑z + ↑(M.d)) ^ k * (c * f z),
      by simp at *; assumption,
    rw hyp M z,
    ring
  end }

instance : is_submodule is_bound_at_infinity :=
{ zero_ := ⟨0, ⟨0, λ z h, by simp⟩⟩,
  add_  := λ f g hf hg, begin
    rcases hf with ⟨Mf, ⟨Af, hAMf⟩⟩,
    rcases hg with ⟨Mg, ⟨Ag, hAMg⟩⟩,
    existsi [Mf + Mg, max Af Ag],
    intros z hz,
    specialize hAMf z (le_trans (le_max_left Af Ag) hz),
    specialize hAMg z (le_trans (le_max_right Af Ag) hz),

    exact calc abs ((f + g) z) ≤ abs (f z) + abs (g z) : by mono
    ... ≤ Mf + Mg : by mono
  end,
  smul  := λ c f hyp, begin
    cases hyp with M hM,
    cases hM with A hAM,
    existsi [abs c * M, A],
    intros z hz,
    simpa using mul_le_mul_of_nonneg_left (hAM z hz) (complex.abs_nonneg c)
  end }

instance : is_submodule is_zero_at_infinity :=
{ zero_ := λ ε hε, ⟨1, λ z hz, by simp [le_of_lt hε]⟩,
  add_  := λ f g hf hg ε hε, begin
    cases hf (ε/2) (half_pos hε) with Af hAf,
    cases hg (ε/2) (half_pos hε) with Ag hAg,
    existsi (max Af Ag),
    intros z hz,
    specialize hAf z (le_trans (le_max_left _ _) hz),
    specialize hAg z (le_trans (le_max_right _ _) hz),
    rw show ε = ε / 2 + ε / 2, by simp,
    exact le_trans (complex.abs_add _ _) (add_le_add hAf hAg)
  end,
  smul  := λ c f hyp ε hε, begin
    by_cases hc : (c = 0),
    { existsi (0 : ℝ ), intros, simp [hc], exact le_of_lt hε },
    { cases hyp (ε / abs c) (lt_div_of_mul_lt (by simp [hc]) (by simp; exact hε)) with A hA,
      existsi A,
      intros z hz,
      rw show abs ((c • f) z) = (abs c)* abs (f z), by simp,
      rw show ε = abs c * (ε / abs c), by rw [mul_comm] ; simp [hc, div_mul_cancel],
      exact mul_le_mul_of_nonneg_left (hA z hz) (complex.abs_nonneg c) }
  end }

lemma is_bound_at_infinity_of_is_zero_at_infinity {f : ℍ → ℂ} (h : is_zero_at_infinity f) :
is_bound_at_infinity f := ⟨1, h 1 zero_lt_one⟩

-- structure is_modular_form (k : ℕ) (f : ℍ → ℂ) : Prop :=
-- (hol      : is_holomorphic f)
-- (transf   : ∀ M : SL2Z, ∀ z : ℍ, f (SL2Z_H M z) = (M.c*z + M.d)^k * f z)
-- (infinity : ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M)

def is_modular_form (k : ℕ) := {f : ℍ → ℂ | is_holomorphic f} ∩ (is_Petersson_weight_ k) ∩ is_bound_at_infinity

def is_cusp_form (k : ℕ) := {f : ℍ → ℂ | is_holomorphic f} ∩ (is_Petersson_weight_ k) ∩ is_zero_at_infinity

lemma is_modular_form_of_is_cusp_form {k : ℕ} (f : ℍ → ℂ) (h : is_cusp_form k f) : is_modular_form k f :=
⟨h.1, is_bound_at_infinity_of_is_zero_at_infinity h.2⟩

instance (k : ℕ) : is_submodule (is_modular_form k) := is_submodule.inter_submodule

instance (k : ℕ) : is_submodule (is_cusp_form k) := is_submodule.inter_submodule

/- def Hecke_operator {k : ℕ} (m : ℤ) : modular_forms k → modular_forms k :=
λ f,
(m^k.pred : ℂ) • (sorry : modular_forms k) -- why is this • failing?
 -/
