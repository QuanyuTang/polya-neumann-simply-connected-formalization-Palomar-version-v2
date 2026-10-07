module

public import RequestProject.PhysicalDrivenKernelConormal
public import RequestProject.NeumannNormalizedBoundary

/-!
# Actual Neumann realization of the observation kernel

The driven construction supplies its actual Hardy input, physical H¹
vector, coordinate trace, and coordinate conormal. The genuine weak
conormal formula identifies this vector with the original Neumann
Poisson solution away from the original spectrum. In particular the
actual Poisson trace equals the actual Volterra trace in the observation
kernel. The conformal coordinates and their arclength change of variable
are explicit supplied data; their existence is still a separate theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Metric
open scoped InnerProductSpace

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
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0)

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (by simp))
local notation "bF" => physicalDrivenKernelInput hΓLip hΓF hW g hg hO
local notation "uF" => physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
  e he hsource hes hΓLip hW g hg hO
local notation "loadF" => sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
  (boundaryFourier (physicalDrivenKernelCoordinateLoad g hg))

include hγ hτ hcoord hE in
/-- The actual reconstructed vector has the true original Neumann weak
equation for the actual coordinate forcing, without a nonresonance
assumption. -/
theorem physicalDrivenKernelH1_isNormalizedNeumannSolution :
    IsNormalizedNeumannSolution QF E loadF uF := by
  intro w
  have hbn := physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC
    e he hsource hΓLip hE hW g hg hO
  have hw := localConformalVekuaH1_normalizedConormal_weak_form hR F hFs hb hL
    hhol hinj hC hK e he hsource hes hγ hτ hcoord (E : ℂ) bF hbn w
  rw [physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad hR F hFs hb hL
    hhol hinj hC hK e he hsource hes hΓLip hE hW g hg hO] at hw
  exact hw

include hγ hτ hcoord hE in
/-- Uniqueness in the actual physical H¹ form identifies the driven
vector with the original normalized Neumann Poisson solution. -/
theorem physicalDrivenKernelH1_eq_normalizedNeumannPoisson
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) :
    uF = normalizedNeumannPoisson QF E loadF := by
  have hu := (isNormalizedNeumannSolution_iff QF E loadF uF).mp
    (physicalDrivenKernelH1_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj
      hC hK e he hsource hes hγ hτ hcoord hΓLip hE hW g hg hO)
  have hp := (isNormalizedNeumannSolution_iff QF E loadF _).mp
    (normalizedNeumannPoisson_isSolution QF
      (h1HelmholtzForm_isUnit hb hL hE.le hnr) loadF)
  exact h1HelmholtzForm_injective hb hL hE.le hnr (hu.trans hp.symm)

include hγ hτ hcoord hE in
/-- The true Poisson trace has the actual Volterra formula on the
observation kernel, with the original complex sign and normalization. -/
theorem normalizedNeumannPoisson_observationKernel_trace_eq_volterra_ae
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) :
    (TF (normalizedNeumannPoisson QF E loadF) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        (fun θ => -Complex.I * volterraOp W g θ) := by
  rw [← physicalDrivenKernelH1_eq_normalizedNeumannPoisson hR F hFs hb hL hhol hinj
    hC hK e he hsource hes hγ hτ hcoord hΓLip hE hW g hg hO hnr]
  exact physicalDrivenKernelH1_coordinate_trace_eq_volterra_ae hR F hFs hb hL
    hhol hinj hC hK e he hsource hes hΓLip hE hW g hg hO

include hγ hτ hcoord hE in
/-- Equality for the actual normalized Neumann boundary operator, whose
definition uses the original physical form resolvent. -/
theorem normalizedNeumannBoundary_observationKernel_eq
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) :
    normalizedNeumannBoundary QF E loadF = QF uF := by
  change QF (normalizedNeumannPoisson QF E loadF) = QF uF
  rw [physicalDrivenKernelH1_eq_normalizedNeumannPoisson hR F hFs hb hL hhol hinj
    hC hK e he hsource hes hγ hτ hcoord hΓLip hE hW g hg hO hnr]

end PhysicalCoordinates

end PolyaNeumann

end
