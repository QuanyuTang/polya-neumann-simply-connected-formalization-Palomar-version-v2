module

public import RequestProject.LocalConformalVekuaTransport
public import RequestProject.LocalConformalHardySubspace

/-!
# A fixed complement for the actual physical conormal chart

The genuine Vekua transport proves injectivity at a reference energy
with a genuine nonzero boundary cut. The closed full nonpositive Fourier
space and the proved identity-plus-compact conormal factorization then
supply a fixed finite-rank complement and a continuous chart inverse.
No injectivity assumption for the conormal operator is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Filter Metric
open scoped Topology

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

local notation "H₀" => nonpositiveFourierSubspace
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

include hb hL hhol hinj hC hK e he hsource hes in
theorem exists_localConformal_fixed_complement_of_cutC_ne_zero
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E₀ W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ T : H₀ᗮ →L[ℂ] L2Z,
      FiniteDimensional ℂ
        (LinearMap.range ((T - Submodule.subtypeL H₀ᗮ : H₀ᗮ →L[ℂ] L2Z) :
          H₀ᗮ →ₗ[ℂ] L2Z)) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L
          (H₀).orthogonalProjection + T ∘L H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E : ℝ => Ring.inverse ((NF (E : ℂ)).comp (H₀).subtypeL ∘L
          (H₀).orthogonalProjection + T ∘L H₀ᗮ.orthogonalProjection)) U := by
  apply normalizedConormal_fixed_complement H₀ hβF haF hgF
  intro b d hbd
  apply Subtype.ext
  have hi := localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E₀ hE₀ hW hcut
  exact hi b.property d.property hbd

end PhysicalCoordinates

end PolyaNeumann

end
