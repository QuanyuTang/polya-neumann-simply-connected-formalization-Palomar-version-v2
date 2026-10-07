module

public import RequestProject.LocalConformalVekuaTrace

/-!
# Ordinary averaged normalization of the genuine Vekua trace

Scalar multiplication commutes with every actual interval primitive.
The pointwise boundary series therefore has exactly the same form in
averaged Fourier coordinates, with the genuine sqrt(2π) normalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric

theorem volterraPrimitiveIterate_const_mul (a h : ℝ → ℂ) (c : ℂ) (j : ℕ) :
    volterraPrimitiveIterate a (fun θ => c * h θ) j =
      fun θ => c * volterraPrimitiveIterate a h j θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext θ
    change (∫ s in (0 : ℝ)..θ,
      a s * volterraPrimitiveIterate a (fun t => c * h t) j s) =
      c * (∫ s in (0 : ℝ)..θ, a s * volterraPrimitiveIterate a h j s)
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [ih]
    ring

theorem hardyFourierTrace_const_mul (c : ℂ) (h : ℤ → ℂ) (θ : ℝ) :
    hardyFourierTrace (fun n => c * h n) θ = c * hardyFourierTrace h θ := by
  unfold hardyFourierTrace
  simp only [mul_assoc]
  exact tsum_mul_left

theorem hardyFourierTrace_normalizedHardyAverage (b : L2Z) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage b) θ =
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) θ :=
  hardyFourierTrace_const_mul _ _ _

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

/-- The genuine ordinary coordinate trace is the convergent Volterra
series of its original averaged input. -/
theorem localConformalVekuaBoundary_average_volterra_hasSum_of_H1
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (θ : ℝ) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j *
      (F (circleMap 0 1 θ) - F 1) ^ j *
      volterraPrimitiveIterate (fun s => star (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage b)) j θ)
      (hardyFourierTrace (normalizedHardyAverage
        (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E b)) θ) := by
  let c : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)⁻¹
  have hfun : hardyFourierTrace (normalizedHardyAverage b) =
      fun t => c * hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) t := by
    funext t
    exact hardyFourierTrace_normalizedHardyAverage b t
  have hs := (localConformalVekuaBoundary_volterra_hasSum_of_H1 hR F hFs hb hL hhol
    hinj hC hK e he hsource hes E b hbn hb1 θ).mul_left c
  simp only [starRingEnd_apply] at hs
  convert hs using 1
  · funext j
    rw [hfun, volterraPrimitiveIterate_const_mul]
    ring
  · exact hardyFourierTrace_normalizedHardyAverage _ θ

end PhysicalCoordinates

end PolyaNeumann

end
