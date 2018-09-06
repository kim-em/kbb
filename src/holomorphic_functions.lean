import analysis.complex
import algebra.pi_instances
import ring_theory.subring
import analysis.normed_space

local attribute [instance] classical.prop_decidable
noncomputable theory

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

/- instance complex_fun_module : module ℂ (domain → ℂ) := sorry

instance hol_submodule : @is_submodule ℂ _ _ _ {f : domain → ℂ | is_holomorphic f} :=
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