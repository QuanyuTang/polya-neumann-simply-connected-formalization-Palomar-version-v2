module

public import RequestProject.LocalConformalFixedComplement
public import RequestProject.PositiveFourierBasis

/-!
# A genuine finite Fourier complement for the physical conormal chart

The finite-rank completion is chosen in the actual standard Fourier bases.
Both vectors of every rank-one correction have finite Fourier support.
This is the extra property needed for preservation of Sobolev regularity;
finite rank alone would not imply that property.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Filter
open scoped Topology InnerProductSpace

local notation "H₀" => nonpositiveFourierSubspace

theorem normalizedConormal_fixed_fourier_complement
    {b a g : ℤ → ℂ} (hb : IsWL1 (1 / 2) b) (ha : IsWL1 (1 / 2) a)
    (hg : IsWL1 (1 / 2) g) {E₀ : ℝ}
    (hinj : Function.Injective ((normalizedConormal hb ha hg E₀).comp (H₀).subtypeL)) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      (∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite) ∧
      (∀ r, (Function.support (v r : ℤ → ℂ)).Finite) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit ((normalizedConormal hb ha hg (E : ℂ)).comp (H₀).subtypeL ∘L
          (H₀).orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E : ℝ => Ring.inverse
          ((normalizedConormal hb ha hg (E : ℂ)).comp (H₀).subtypeL ∘L
            (H₀).orthogonalProjection +
            (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
              H₀ᗮ.orthogonalProjection)) U := by
  have hJ : Continuous fun E : ℝ =>
      (normalizedConormal hb ha hg (E : ℂ)).comp (H₀).subtypeL :=
    ((continuous_normalizedConormal hb ha hg).comp Complex.continuous_ofReal).clm_comp
      continuous_const
  have heq : (normalizedConormal hb ha hg E₀).comp (H₀).subtypeL ∘L
      (H₀).orthogonalProjection + Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection -
        (1 : L2Z →L[ℂ] L2Z) =
      (normalizedConormal hb ha hg E₀ - (1 : L2Z →L[ℂ] L2Z)) ∘L
        ((H₀).subtypeL ∘L (H₀).orthogonalProjection) := by
    ext1 x
    have hx := (H₀).starProjection_add_starProjection_orthogonal x
    rw [Submodule.starProjection_apply, Submodule.starProjection_apply] at hx
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, Submodule.subtypeL_apply]
    rw [← sub_eq_zero]
    have horth : (H₀ᗮ.orthogonalProjection x : L2Z) =
        x - ((H₀).orthogonalProjection x : L2Z) := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact hx
    rw [horth]
    abel
  have hcpt : IsCompactOperator ((normalizedConormal hb ha hg E₀).comp (H₀).subtypeL ∘L
      (H₀).orthogonalProjection + Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection -
        (1 : L2Z →L[ℂ] L2Z)) := by
    rw [heq]
    exact (isCompactOperator_normalizedConormal_sub_one hb ha hg E₀).comp_clm _
  obtain ⟨d, u, v, hu, hv, U, hU, hunit, hcont⟩ :=
    exists_fixed_complement_basis H₀ hJ hcpt hinj stdBasisZ positiveFourierHilbertBasis
  exact ⟨d, u, v,
    (fun r => finite_support_of_mem_span_positiveFourierHilbertBasis (hu r)),
    (fun r => finite_support_of_mem_span_stdBasisZ (hv r)), U, hU, hunit, hcont⟩

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' Metric.ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' Metric.ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1))
    (hinj : InjOn F (Metric.ball (0 : ℂ) 1))
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

include hb hL hhol hinj hC hK e he hsource hes in
theorem exists_localConformal_fixed_fourier_complement_of_cutC_ne_zero
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E₀ W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      (∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite) ∧
      (∀ r, (Function.support (v r : ℤ → ℂ)).Finite) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L
          (H₀).orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E : ℝ => Ring.inverse ((NF (E : ℂ)).comp (H₀).subtypeL ∘L
          (H₀).orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) U := by
  apply normalizedConormal_fixed_fourier_complement hβF haF hgF
  intro b d hbd
  apply Subtype.ext
  exact (localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E₀ hE₀ hW hcut)
    b.property d.property hbd

end PhysicalCoordinates

end PolyaNeumann

end
