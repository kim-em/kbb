import .SL2Z_generators
import .modular_forms

local notation `ℍ` := upper_half_space
local notation `Mat` := integral_matrices_with_determinant

lemma pos_det' {m : ℤ}  (h : m > 0) {A : Mat m} : ↑(A.a) * ↑(A.d) - ↑(A.b) * ↑(A.c) > (0 : ℝ) :=
begin
  cases A with a b c d det,
  rw ←det at h,
  rw [←int.cast_mul, ←int.cast_mul, ←int.cast_sub],
  suffices : (0 : ℝ) < ↑(a * d - b * c), exact this,
  rwa int.cast_pos
end

def Hecke_operator {k : ℕ} (m : ℤ) (h : m > 0) (f : is_Petersson_weight_ (k+1)) :
  is_Petersson_weight_ (k+1) :=
let orbits := quotient (action_rel (SL2Z_M m)) in
⟨ λ z : ℍ, (m^k : ℂ) * finset.univ.sum
begin
  haveI := SL2Z_M.finiteness m (ne_of_gt h),
  apply quotient.lift,
  swap,
  show (Mat m → ℂ),
  intro A,
  cases f with f weight_f,
  refine 1/(A.c * z + A.d)^(k+1) *
   (f (⟨«Möbius_transform» A.a A.b A.c A.d z.1,
    preserve_ℍ (pos_det' h) z.1 z.2⟩ : ℍ)),
  intros A B H,
  cases f with f weight_f,
  dsimp,
  dsimp [is_Petersson_weight_, SL2Z_H] at weight_f,

  --dsimp [(≈)] at H,

  sorry,
end⟩