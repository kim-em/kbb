import data.complex.basic
import group_theory.group_action

open complex

def upper_half_space := {z : ℂ // z.im > 0}
local notation `ℍ` := upper_half_space

instance upper_half_space.to_complex : has_coe ℍ ℂ := ⟨λ z, z.val⟩

def is_holomorphic (f : ℍ → ℂ) : Prop := sorry

def SL2Z : Type := sorry

def SL2Z.mk : ℤ → ℤ → ℤ → ℤ → SL2Z := sorry

instance : group SL2Z := sorry

def SL2Z_H : SL2Z → ℍ → ℍ := sorry

instance : is_group_action SL2Z_H := sorry

structure is_modular_form (k : ℕ) (f : ℍ → ℂ) : Prop :=
(hol      : is_holomorphic f)
(transf   : ∀ a b c d : ℤ, a*d - b*c = 1 → ∀ z : ℍ, f (SL2Z_H (SL2Z.mk a b c d) z) = (c*z + d)^k * f z)
(infinity : ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M)