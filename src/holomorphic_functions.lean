import analysis.complex
import algebra.pi_instances
import ring_theory.subring
import analysis.normed_space

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u v

open filter complex

def has_complex_derivative_at
(f : ℂ → ℂ)
(f'z : ℂ) 
(z : ℂ) : Prop :=
let error_term (h : ℂ) : ℝ := 
    abs((f (z + h) - (f z + f'z * h))/h) in
(tendsto error_term (nhds 0) (nhds 0))

section
variables  {α : Type*} {β : Type*} {s : set α}

def extend_by_zero [has_zero β] (f : s → β) : α → β :=
λ z, if h : z ∈ s then f ⟨z, h⟩ else 0

lemma extend_by_zero_add [add_group β] (f g : s → β) :
extend_by_zero (f + g) = extend_by_zero f + extend_by_zero g :=
by ext z ; by_cases h : z ∈ s ; simp [extend_by_zero, h]

lemma extend_by_zero_mul [semiring β] (f g : s → β) :
extend_by_zero (f * g) = extend_by_zero f * extend_by_zero g :=
by ext z ; by_cases h : z ∈ s ; simp [extend_by_zero, h]

lemma extend_by_zero_neg [add_group β] (f : s → β) :
extend_by_zero (-f) = -extend_by_zero f :=
by ext z ; by_cases h : z ∈ s ; simp [extend_by_zero, h]

end

/-- holomorphic function from a subset of ℂ. Correct definition if domain is open. -/
def is_holomorphic {domain : set ℂ} (f : domain → ℂ) :=
(∀ z : domain, ∃ f'z, has_complex_derivative_at (extend_by_zero f) f'z z)

variable {domain : set ℂ}
/-
instance : is_subring {f : domain → ℂ | is_holomorphic f} :=
{ zero_mem := sorry,
  add_mem  := sorry,
  neg_mem  := sorry,
  mul_mem  := sorry,
  one_mem  := sorry,
}-/

lemma const_hol (domain_open : is_open domain) (c : ℂ) : is_holomorphic (λ z : domain, (c : ℂ)) :=
begin
  intro z₀,
  existsi (0 : ℂ),
  dsimp [has_complex_derivative_at],
  simp,
  sorry
end

lemma zero_hol : is_holomorphic (λ z : domain, (0 : ℂ)) :=
begin
  intro z₀,
  existsi (0 : ℂ),
  dsimp [has_complex_derivative_at],
  have : extend_by_zero (λ (z : {x // x ∈ domain}), (0:ℂ)) = (λ (z : ℂ), 0),
  { ext z,
    dsimp only [extend_by_zero],
    by_cases h : z ∈ domain ; simp [h] ; refl },
  simp [this, tendsto_const_nhds]
end

lemma one_hol (domain_open : is_open domain) : is_holomorphic (λ z : domain, (1 : ℂ)) := const_hol domain_open 1

lemma add_hol (f g : domain → ℂ) (f_hol : is_holomorphic f) (g_hol : is_holomorphic g) : is_holomorphic (f + g) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  cases g_hol z₀ with g'z₀ Hg,
  existsi (f'z₀ + g'z₀),
  rw extend_by_zero_add,
  have Hfg : tendsto (λ (h : ℂ), abs ((extend_by_zero f (↑z₀ + h) - (extend_by_zero f ↑z₀ + f'z₀ * h)) / h) +
         abs ((extend_by_zero g (↑z₀ + h) - (extend_by_zero g ↑z₀ + g'z₀ * h)) / h)) (nhds 0) (nhds 0) :=
  by simpa using tendsto_add Hf Hg,
  refine squeeze_zero _ _ Hfg,
  { intro h, apply complex.abs_nonneg },
  { intro h,
    refine le_trans (le_of_eq _) (complex.abs_add _ _),
    congr,
    dsimp,
    ring }
end

lemma neg_hol (f : domain → ℂ) (f_hol : is_holomorphic f) : is_holomorphic (-f) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ H,
  existsi -f'z₀,
  rw extend_by_zero_neg,
  suffices : tendsto (λ (h : ℂ), abs ((-(extend_by_zero f (↑z₀ + h) + -(extend_by_zero f ↑z₀ + f'z₀ * h))) / h))
    (nhds 0) (nhds 0),
  { simpa [has_complex_derivative_at] },
  conv { congr, funext, rw [neg_div, complex.abs_neg], },
  exact H
end

-- instance complex_fun_module : module ℂ (domain → ℂ) := sorry

-- I would like to remove the following line... but I can't
instance foobar (X : Type u) (R : Type v) [ring R] : module R (X → R) := pi.module

instance hol_submodule : is_submodule {f : domain → ℂ | is_holomorphic f} := sorry

/-
{ zero_ := zero_hol,
  add_  := begin
    intros f g f_hol g_hol,
    intro z₀,
    cases f_hol z₀ with f' limf,
    cases g_hol z₀ with g' limg,
    existsi f' + g',
    dsimp only [has_complex_derivative_at],
    rw extend_by_zero_add,
    apply squeeze_zero,
    { intro h,
      exact abs_nonneg _ },
    { intro h,
      
      sorry },
    { 
      sorry },
    { 
      sorry },
  end,
  smul := 
  begin
    
    sorry
  end,
  
} -/