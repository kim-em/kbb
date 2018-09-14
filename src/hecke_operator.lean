import .SL2Z_generators
import .modular_forms

local notation `ℍ` := upper_half_space
local notation `Mat` := integral_matrices_with_determinant

def Hecke_operator {k : ℕ} (m : ℤ) (h : m > 0) (f : is_Petersson_weight_ (k+1)) :
is_Petersson_weight_ (k+1) :=
let orbits := quotient (action_rel (SL2Z_M_ m)) in
⟨ λ z : ℍ, (m^k : ℂ) * finset.univ.sum
begin
  haveI := SL2Z_M_.finitely_many_orbits m (ne_of_gt h),
  apply quotient.lift,
  swap,
  show (Mat m → ℂ),
  intro A,
  exact 1/(A.c * z + A.d)^(k+1) *
   (f.1 (⟨«Möbius_transform» A.a A.b A.c A.d z.1,
    preserve_ℍ (sorry) z.1 z.2⟩ : ℍ)),
  intros A B H,
  dsimp,
  repeat {sorry},
end⟩
