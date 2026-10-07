module

public import RequestProject.PhysicalDrivenKernelRealization
public import RequestProject.PhysicalDrivenRowsReconstruction
public import RequestProject.LocalConformalVekuaConormalBridge

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate InnerProductSpace

theorem physicalDrivenPrimitive_trace_eq {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (normalizedHardyAverage b)) (k : ℕ) (s : ℝ) :
    hardyFourierTrace (normalizedHardyAverage
      (((localConformalHardyPrimitive hR F hFs) ^ k) b)) s =
      volterraPrimitiveIterate (fun t => conj (deriv (physicalCircleTrace F) t))
        (hardyFourierTrace (normalizedHardyAverage b)) k s := by
  exact localConformalHardyPrimitive_pow_volterra_of_H1 hR F hFs hhol b hbn hb1 k s

theorem physicalDrivenPrimitive_deriv {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j : ℕ) (θ : ℝ) :
    HasDerivAt (hardyFourierTrace (normalizedHardyAverage
      (((localConformalHardyPrimitive hR F hFs) ^ (j + 1)) b)))
      ((conj (deriv (physicalCircleTrace F) θ)) *
        hardyFourierTrace (normalizedHardyAverage
          (((localConformalHardyPrimitive hR F hFs) ^ j) b)) θ) θ := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hnorm : IsSobolevSeq 1 (normalizedHardyAverage b) := by
    exact isSobolevSeq_smul (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ hb1
  have hbn' : IsNonpositiveFourierSupport (normalizedHardyAverage b) := by
    intro n hn
    simp [normalizedHardyAverage, fromL2, hbn n hn]
  have hA : IsWL1 1 (fourierCoeff (localConformalPrimitiveCircle F)) := by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  have hAn : IsStrictNegativeFourierSupport
      (fourierCoeff (localConformalPrimitiveCircle F)) := by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol
  have hder := hasDerivAt_hardyFourierTrace_antiPrimIter_succ
    (localConformalPrimitiveCircle F) hA hnorm hAn hbn' j θ
  rw [localConformalPrimitiveCircle_coeff hR F hFs] at hder
  rw [← normalizedHardyAverage_localConformalHardyPrimitive_pow hR F hFs (j + 1) b,
    ← normalizedHardyAverage_localConformalHardyPrimitive_pow hR F hFs j b,
    localConformalPrimitiveCircle_apply hR F hFs] at hder
  exact hder

end PolyaNeumann

end
