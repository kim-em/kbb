import tactic.ring
import tactic.tidy
import group_theory.group_action
import .matrix_groups

run_cmd mk_simp_attr `SL2Z

@[tidy] meta def tidy_ring := `[ring]

@[derive decidable_eq]
structure integral_matrices_with_determinant (m : ℤ) :=
(a b c d : ℤ)
(det : a * d - b * c = m)

@[extensionality]
theorem integral_matrices_with_determinant.ext (m : ℤ) :
  ∀ (A B : integral_matrices_with_determinant m)
  (H1 : A.a = B.a) (H2 : A.b = B.b) (H3 : A.c = B.c) (H4 : A.d = B.d),
  A = B
| ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ rfl rfl rfl rfl := rfl

@[reducible]
def SL2Z := integral_matrices_with_determinant 1

instance : group SL2Z :=
{ mul := λ A B, ⟨A.a * B.a + A.b * B.c,
                A.a * B.b + A.b * B.d,
                A.c * B.a + A.d * B.c,
                A.c * B.b + A.d * B.d,
    calc  (A.a * B.a + A.b * B.c) * (A.c * B.b + A.d * B.d) - (A.a * B.b + A.b * B.d) * (A.c * B.a + A.d * B.c)
        = (A.a * A.d - A.b * A.c) * (B.a * B.d - B.b * B.c) : by ring
    ... = 1 : by rw [A.det, B.det, mul_one]⟩,
  mul_assoc := λ A B C, by cases A; cases B; cases C; ext; dsimp; ring,
  one := ⟨1, 0, 0, 1, rfl⟩,
  one_mul := λ A, by cases A; ext; change _ + _ = _; simp,
  mul_one := λ A, by cases A; ext; change _ + _ = _; simp,
  inv := λ A, ⟨A.d, -A.b, -A.c, A.a, by simpa [mul_comm] using A.det⟩,
  mul_left_inv := λ A, by cases A; ext; change _ + _ = _; simp at A_det; simp [mul_comm, A_det]; refl }

@[simp, SL2Z] lemma SL2Z_mul_a (A B : SL2Z) : (A * B).a = A.a * B.a + A.b * B.c := rfl
@[simp, SL2Z] lemma SL2Z_mul_b (A B : SL2Z) : (A * B).b = A.a * B.b + A.b * B.d := rfl
@[simp, SL2Z] lemma SL2Z_mul_c (A B : SL2Z) : (A * B).c = A.c * B.a + A.d * B.c := rfl
@[simp, SL2Z] lemma SL2Z_mul_d (A B : SL2Z) : (A * B).d = A.c * B.b + A.d * B.d := rfl
@[simp, SL2Z] lemma SL2Z_one_a : (1 : SL2Z).a = 1 := rfl
@[simp, SL2Z] lemma SL2Z_one_b : (1 : SL2Z).b = 0 := rfl
@[simp, SL2Z] lemma SL2Z_one_c : (1 : SL2Z).c = 0 := rfl
@[simp, SL2Z] lemma SL2Z_one_d : (1 : SL2Z).d = 1 := rfl
@[simp, SL2Z] lemma SL2Z_inv_a (A : SL2Z) : (A⁻¹).a = A.d := rfl
@[simp, SL2Z] lemma SL2Z_inv_b (A : SL2Z) : (A⁻¹).b = -A.b := rfl
@[simp, SL2Z] lemma SL2Z_inv_c (A : SL2Z) : (A⁻¹).c = -A.c := rfl
@[simp, SL2Z] lemma SL2Z_inv_d (A : SL2Z) : (A⁻¹).d = A.a := rfl

def SL2Z_M_ (m : ℤ) : SL2Z → integral_matrices_with_determinant m → integral_matrices_with_determinant m :=
λ X Y, {  a := X.a * Y.a + X.b * Y.c,
          b := X.a * Y.b + X.b * Y.d,
          c := X.c * Y.a + X.d * Y.c,
          d := X.c * Y.b + X.d * Y.d,
          det := begin
            conv { to_rhs, rw ← one_mul m, congr, rw ← X.det, skip, rw ← Y.det }, 
            ring
          end }

instance (m : ℤ) : is_group_action (SL2Z_M_ m) :=
{ mul := λ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩,
    by ext; simp [SL2Z_M_, add_mul, mul_add, mul_assoc],
  one := λ ⟨_, _, _, _, _⟩, by ext; simp [SL2Z_M_], }

@[elab_as_eliminator]
def fin2.rec_on {C : fin 2 → Sort*} : ∀ (n : fin 2), C 0 → C 1 → C n
| ⟨0, _⟩ C0 _ := C0
| ⟨1, _⟩ _ C1 := C1
| ⟨n+2, H⟩ _ _ := false.elim $ by cases H with H H; cases H with H H; cases H

@[elab_as_eliminator]
theorem fin2.induction_on {C : fin 2 → Prop} (n : fin 2) (H0 : C 0) (H1 : C 1) : C n :=
fin2.rec_on n H0 H1

def SL2Z_SL_2_Z : SL2Z ≃ SL 2 ℤ :=
{ to_fun := λ A, ⟨units.mk
    (λ i j, fin2.rec_on i (fin2.rec_on j A.a A.b) (fin2.rec_on j A.c A.d))
    (λ i j, fin2.rec_on i (fin2.rec_on j A.d (-A.b)) (fin2.rec_on j (-A.c) A.a))
    (matrix.ext' $ λ i j, fin2.induction_on i
      (fin2.induction_on j
        (show A.a * A.d + (A.b * (-A.c) + 0) = 1, by rw [add_zero, mul_neg_eq_neg_mul_symm, ← sub_eq_add_neg, A.det])
        (show A.a * (-A.b) + (A.b * A.a + 0) = 0, by rw [add_zero, mul_comm, ← add_mul, neg_add_self, zero_mul]))
      (fin2.induction_on j
        (show A.c * A.d + (A.d * (-A.c) + 0) = 0, by rw [add_zero, mul_comm, ← mul_add, add_neg_self, mul_zero])
        (show A.c * (-A.b) + (A.d * A.a + 0) = 1, by rw [add_zero, mul_comm, add_comm, mul_comm, ← neg_mul_eq_neg_mul, ← sub_eq_add_neg, A.det])))
    (matrix.ext' $ λ i j, fin2.induction_on i
      (fin2.induction_on j
        (show A.d * A.a + (-A.b * A.c + 0) = 1, by rw [add_zero, ← neg_mul_eq_neg_mul, mul_comm, ← sub_eq_add_neg, A.det])
        (show A.d * A.b + (-A.b * A.d + 0) = 0, by rw [add_zero, mul_comm, ← add_mul, add_neg_self, zero_mul]))
      (fin2.induction_on j
        (show -A.c * A.a + (A.a * A.c + 0) = 0, by rw [add_zero, mul_comm, ← mul_add, neg_add_self, mul_zero])
        (show -A.c * A.b + (A.a * A.d + 0) = 1, by rw [add_zero, ← neg_mul_eq_neg_mul, mul_comm, add_comm, ← sub_eq_add_neg, A.det]))),
    is_subgroup.mem_trivial.2 $ units.ext $
    show ((1:ℤ) * (A.a * (A.d * 1))) + (((-1:ℤ) * (A.c * (A.b * 1))) + (0:ℤ)) = 1,
    by rw [one_mul, mul_one, mul_one, add_zero, neg_one_mul, mul_comm A.c]; from A.det⟩,
  inv_fun := λ M, ⟨M.1.1 0 0, M.1.1 0 1, M.1.1 1 0, M.1.1 1 1,
    have H : ((1:ℤ) * (M.1.1 0 0 * (M.1.1 1 1 * 1))) + (((-1:ℤ) * (M.1.1 1 0 * (M.1.1 0 1 * 1))) + (0:ℤ)) = 1,
      from units.ext_iff.1 (is_subgroup.mem_trivial.1 M.2),
    by rwa [one_mul, mul_one, mul_one, add_zero, neg_one_mul, mul_comm (M.1.1 1 0)] at H⟩,
  left_inv := λ A, integral_matrices_with_determinant.ext 1 _ _
    rfl rfl rfl rfl,
  right_inv := λ M, subtype.eq $ units.ext $ matrix.ext' $ λ i j,
    fin2.induction_on i
      (fin2.induction_on j rfl rfl)
      (fin2.induction_on j rfl rfl) }

namespace integral_matrices_with_determinant

variables (m : ℤ) (A B : integral_matrices_with_determinant m)

instance : has_neg (integral_matrices_with_determinant m) :=
⟨λ A, ⟨-A.a, -A.b, -A.c, -A.d, by rw [neg_mul_neg, neg_mul_neg, A.det]⟩⟩

@[simp, SL2Z] lemma neg_a : (-A).a = -A.a := rfl
@[simp, SL2Z] lemma neg_b : (-A).b = -A.b := rfl
@[simp, SL2Z] lemma neg_c : (-A).c = -A.c := rfl
@[simp, SL2Z] lemma neg_d : (-A).d = -A.d := rfl
@[simp, SL2Z] protected lemma neg_neg : -(-A) = A := by ext; simp

end integral_matrices_with_determinant

namespace SL2Z

variables (A B : SL2Z)

@[simp, SL2Z] protected lemma neg_one_mul : -1 * A = -A := by ext; simp
@[simp, SL2Z] protected lemma neg_mul_neg : -A * -B = A * B := by ext; simp
@[simp, SL2Z] protected lemma neg_mul : -(A * B) = -A * B := by ext; simp
@[simp, SL2Z] protected lemma neg_neg : -(-A) = A := by ext; simp

end SL2Z