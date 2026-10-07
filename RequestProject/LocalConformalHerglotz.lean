module

public import RequestProject.LocalConformalBoundaryLoad
public import RequestProject.NeumannHerglotzBoundary

/-!
# Actual Herglotz waves in conformal weak coordinates

The physical conormal load is the genuine ordinary-coordinate boundary L²
trace, transformed with its proved Jacobian factor. The normalized variational
solution is identified with the actual interior Herglotz wave by its Green
identity and uniqueness at a nonresonant physical Neumann energy.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hhol hinj hC hcoord

/-- The actual physical Herglotz Green equation in normalized weak coordinates. -/
theorem localConformalHerglotz_isNormalizedNeumannSolution
    {E : ℝ} (hE : 0 ≤ E) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))
      (herglotzWaveH1 hb ha (Real.sqrt E)) :=
  isBoundaryNeumannSolution_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord _ _ (herglotzWaveH1_sqrt_isBoundaryNeumannSolution hb hL hγ ha hE)

/-- Nonresonance of the actual physical spectrum identifies the normalized
Poisson solution with the actual Herglotz wave in the physical H¹ space. -/
theorem localConformal_normalizedNeumannPoisson_herglotz
    {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue (F '' ball (0 : ℂ) 1) j ≠ ENNReal.ofReal E)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    normalizedNeumannPoisson (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
        herglotzWaveH1 hb ha (Real.sqrt E) := by
  let Q := localConformalDiskHalfTrace hR F hFs hL
  let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))
  have hunit := h1HelmholtzForm_isUnit hb hL hE hnr
  have hp := normalizedNeumannPoisson_isSolution Q hunit b
  have hw := localConformalHerglotz_isNormalizedNeumannSolution
    hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE ha
  exact (existsUnique_normalizedNeumannSolution Q hunit b).unique hp hw

/-- The actual normalized boundary operator takes the transformed physical
conormal load to the actual conformal half trace of the Herglotz wave. -/
theorem localConformal_normalizedNeumannBoundary_herglotz
    {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue (F '' ball (0 : ℂ) 1) j ≠ ENNReal.ofReal E)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    normalizedNeumannBoundary (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      localConformalDiskHalfTrace hR F hFs hL (herglotzWaveH1 hb ha (Real.sqrt E)) := by
  change localConformalDiskHalfTrace hR F hFs hL
    (normalizedNeumannPoisson (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))) = _
  rw [localConformal_normalizedNeumannPoisson_herglotz
    hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE hnr ha]

end PolyaNeumann

end
