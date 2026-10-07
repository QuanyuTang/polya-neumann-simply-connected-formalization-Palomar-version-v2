module

public import RequestProject.SobolevMultiplier

/-! Sobolev regularity of a fixed point from two specified gains. -/

@[expose] public section

set_option autoImplicit false

namespace PolyaNeumann

theorem sobolev_bootstrap_two_steps {s₀ s₁ s₂ : ℝ}
    (Φ : (ℤ → ℂ) → (ℤ → ℂ))
    (h₀₁ : ∀ f, IsSobolevSeq s₀ f → IsSobolevSeq s₁ (Φ f))
    (h₁₂ : ∀ f, IsSobolevSeq s₁ f → IsSobolevSeq s₂ (Φ f))
    (z : ℤ → ℂ) (hz : IsSobolevSeq s₀ z) (hfix : Φ z = z) :
    IsSobolevSeq s₂ z := by
  have h₁ := h₀₁ z hz
  rw [hfix] at h₁
  have h₂ := h₁₂ z h₁
  rwa [hfix] at h₂

theorem sobolev_bootstrap_to_half
    (Φ : (ℤ → ℂ) → (ℤ → ℂ))
    (h₀₁ : ∀ f, IsSobolevSeq 0 f → IsSobolevSeq (1 / 4 : ℝ) (Φ f))
    (h₁₂ : ∀ f, IsSobolevSeq (1 / 4 : ℝ) f → IsSobolevSeq (1 / 2 : ℝ) (Φ f))
    (z : ℤ → ℂ) (hz : IsSobolevSeq 0 z) (hfix : Φ z = z) :
    IsSobolevSeq (1 / 2 : ℝ) z :=
  sobolev_bootstrap_two_steps Φ h₀₁ h₁₂ z hz hfix

end PolyaNeumann

end
