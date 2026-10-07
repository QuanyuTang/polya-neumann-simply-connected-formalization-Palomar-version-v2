module

public import RequestProject.LocalConformalWeakModes

/-! The nonzero Fourier principal term in the actual Neumann weak equation. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate

private theorem normalize_weak_mode {s t k E a I b : ℂ} (hs : s ≠ 0) (hk : k ≠ 0)
    (h : s ^ 2 * k * a - E * I = t * s * b) :
    t * s * a - (t ^ 2 / k) * b = E * (t / (s * k)) * I := by
  have he : E * I = s ^ 2 * k * a - t * s * b := by linear_combination -h
  calc
    _ = (t / (s * k)) * (s ^ 2 * k * a - t * s * b) := by
      field_simp [hs, hk]
    _ = (t / (s * k)) * (E * I) := by rw [← he]
    _ = _ := by ring

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

include hb hhol hinj hC e he hsource hes in
theorem localConformal_principal_mode_pos
    (E : ℝ) (b : L2Z) (u : NeumannH1 (F '' ball (0 : ℂ) 1))
    (hu : IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E b u)
    (m : ℕ) :
    localConformalDiskHalfTrace hR F hFs hL u ((m + 1 : ℕ) : ℤ) -
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b ((m + 1 : ℕ) : ℤ) =
        (E : ℂ) * diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK u)
          ((m + 1 : ℕ) : ℤ) := by
  have hw := localConformal_weak_holomorphic_mode hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b u hu (m + 1)
  have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_natCast, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  have hs : (Real.sqrt (2 * π) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'
  have hk : (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity :
    ((m + 1 : ℕ) : ℝ) ≠ 0)
  have hs2 : (Real.sqrt (2 * π) : ℂ) ^ 2 = (2 * π : ℂ) := by
    exact_mod_cast Real.sq_sqrt two_pi_pos.le
  have ht2 : (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = (((m + 2 : ℕ) : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ))
  rw [hweight] at hw
  have hn := normalize_weak_mode hs hk (by simpa only [hs2, Complex.ofReal_natCast] using hw)
  rw [ht2] at hn
  rw [localConformalDiskHalfTrace_apply]
  change 1 + |(((m + 1 : ℕ) : ℤ) : ℝ)| = _ at hweight
  rw [hweight, boundaryFourier_apply]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, diskMassForcingCoeff,
    diskMassForcingScale, mul_assoc] using hn

include hb hhol hinj hC e he hsource hes in
theorem localConformal_principal_mode_neg
    (E : ℝ) (b : L2Z) (u : NeumannH1 (F '' ball (0 : ℂ) 1))
    (hu : IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E b u)
    (m : ℕ) :
    localConformalDiskHalfTrace hR F hFs hL u (-((m + 1 : ℕ) : ℤ)) -
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b (-((m + 1 : ℕ) : ℤ)) =
        (E : ℂ) * diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK u)
          (-((m + 1 : ℕ) : ℤ)) := by
  have hw := localConformal_weak_antiholomorphic_mode hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b u hu (m + 1)
  have hweight : sobWeight (-((m + 1 : ℕ) : ℤ)) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  have hs : (Real.sqrt (2 * π) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'
  have hk : (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity :
    ((m + 1 : ℕ) : ℝ) ≠ 0)
  have hs2 : (Real.sqrt (2 * π) : ℂ) ^ 2 = (2 * π : ℂ) := by
    exact_mod_cast Real.sq_sqrt two_pi_pos.le
  have ht2 : (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = (((m + 2 : ℕ) : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ))
  rw [hweight] at hw
  have hn := normalize_weak_mode hs hk (by simpa only [hs2, Complex.ofReal_natCast] using hw)
  rw [ht2] at hn
  have hi : -((m + 1 : ℕ) : ℤ) = Int.negSucc m := by omega
  rw [localConformalDiskHalfTrace_apply]
  unfold sobWeight at hweight
  rw [hweight, boundaryFourier_apply, hi]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, diskMassForcingCoeff,
    diskMassForcingScale, hi, mul_assoc] using hn

end

end PolyaNeumann

end
