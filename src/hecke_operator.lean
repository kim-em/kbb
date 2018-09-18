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

noncomputable def Hecke_operator {k : ℕ} (m : ℤ) (h : m > 0) (f : is_Petersson_weight_ (k+1)) :
  is_Petersson_weight_ (k+1) :=
begin
  let orbits := quotient (action_rel (SL2Z_M m)),
  letI h_orbits : fintype orbits := SL2Z_M.finiteness m (ne_of_gt h),
  refine ⟨λz:ℍ,
    (m^k : ℂ) * (finset.univ : finset orbits).sum (λo, quotient.lift_on' o _ _), _⟩,
  refine λA,
    1 / (A.c * z + A.d)^(k+1) *
    f.1 (⟨«Möbius_transform» A.a A.b A.c A.d z, preserve_ℍ (pos_det' h) z z.2⟩ : ℍ),
  { rcases f with ⟨f, weight_f⟩,
    rintros A B ⟨M, eq⟩,
    dsimp,
    dsimp [is_Petersson_weight_, SL2Z_H] at weight_f,
    sorry },
  { sorry }
end

