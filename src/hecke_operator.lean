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

theorem M_trans_SL2Z_H {m : ℤ} {h : m > 0} {M : SL2Z} {A : Mat m} :
M_trans h (SL2Z_M m M A) = SL2Z_H M ∘ (M_trans h A) :=
begin
  funext z,
  simp [M_trans, SL2Z_M, SL2Z_H, «Möbius_transform»],

-- m : ℤ,
-- h : m > 0,
-- M : SL2Z,
-- A : Mat m,
-- z : ↥ℍ
-- ⊢ (↑(M.a) * ↑(A.b) + (↑(M.b) * ↑(A.d) + (↑(M.a) * ↑(A.a) + ↑(M.b) * ↑(A.c)) * ↑z)) /
--       (↑(M.c) * ↑(A.b) + (↑(M.d) * ↑(A.d) + (↑(M.c) * ↑(A.a) + ↑(M.d) * ↑(A.c)) * ↑z)) =
--     (↑(M.b) + ↑(M.a) * ((↑(A.b) + ↑(A.a) * ↑z) / (↑(A.d) + ↑(A.c) * ↑z))) /
--       (↑(M.d) + ↑(M.c) * ((↑(A.b) + ↑(A.a) * ↑z) / (↑(A.d) + ↑(A.c) * ↑z)))

  -- ring, -- fails
  sorry
end

noncomputable def Hecke_operator {k : ℕ} (m : ℤ) (h : m > 0) (f : is_Petersson_weight_ (k+1)) :
  is_Petersson_weight_ (k+1) :=
begin
  let orbits := quotient (action_rel (SL2Z_M m)),
  letI h_orbits : fintype orbits := SL2Z_M.finiteness m (ne_of_gt h),
  refine ⟨λz:ℍ,
    (m^k : ℂ) * (finset.univ : finset orbits).sum (λo, quotient.lift_on' o _ _), _⟩,
  refine λA, 1 / (A.c * z + A.d)^(k+1) * f.1 (M_trans h A z),
  { rcases f with ⟨f, weight_f⟩,
    rintros A B ⟨M, H⟩,
    -- dsimp [is_Petersson_weight_, SL2Z_H] at weight_f,
    rw [← H, M_trans_SL2Z_H],
    simp,
    rw (weight_f M _),
    rw ← mul_assoc,
    congr' 1,
    
    sorry },
  { sorry }
end

