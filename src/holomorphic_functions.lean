import analysis.complex

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

def extend_by_default {α : Type*} {β : Type*} [inhabited β] {s : set α} (f : s → β) : α → β :=
λ z, if h : z ∈ s then f ⟨z, h⟩ else default β

/-- holomorphic function from a subset of ℂ. Correct definition if domain is open. -/
def is_holomorphic {domain : set ℂ} (f : domain → ℂ) :=
(∀ z : domain, ∃ f'z, has_complex_derivative_at (extend_by_default f) f'z z)