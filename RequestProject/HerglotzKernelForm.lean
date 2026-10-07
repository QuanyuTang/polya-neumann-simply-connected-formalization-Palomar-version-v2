module

public import RequestProject.KernelFourierAction
public import RequestProject.HerglotzReduction

/-!
# The corrected kernel form on actual Herglotz conormal traces

The normalized conormal vector is `2π Λ⁻¹ᐟ² ĝ`. This file identifies its
pairing with the compact weighted kernel matrix with the actual boundary
double integral, including the factor `(2π)⁻¹`. The clamped extension is
only used to construct the circle `L²` input and leaves the physical
boundary integral unchanged.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace

local instance factTwoPiPosHKF : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

lemma exists_bound_clampedHerglotzConormal {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (k : ℝ) (a : dirDensities) :
    ∃ B : ℝ, ∀ θ, ‖clampedHerglotzConormal k γ a.1 θ‖ ≤ B := by
  obtain ⟨_, B, hB⟩ := herglotzConormal_bounded a.2.intervalIntegrable k hK
  exact ⟨B, fun θ => hB (clampTwoPi θ)⟩

/-- The actual normalized conormal vector is the half-order smoothing of
the Fourier coordinates of its circle `L²` trace, scaled by `2π`. -/
theorem normalizedHerglotzConormal_eq_smoothing_fourier
    {Ω : Set ℂ} (hS : IsSmoothDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {K : NNReal} (hK : LipschitzWith K γ)
    (k : ℝ) (a : dirDensities) {B : ℝ}
    (hB : ∀ θ, ‖clampedHerglotzConormal k γ a.1 θ‖ ≤ B) :
    normalizedHerglotzConormal hS hγ k a =
      (2 * π : ℂ) • sobolevSmoothing (1 / 2) (by norm_num)
        ((fourierBasis (T := 2 * π)).repr
          ((memLp_liftIco_two_pi
            (continuous_clampedHerglotzConormal hS hγ a.2 k).measurable hB).toLp _)) := by
  rw [normalizedHerglotzConormal_eq_sobVec hS hγ hK k a]
  congr 1
  apply lp.ext
  funext n
  simp only [sobVec_apply, sobolevSmoothing, diagOp_apply]
  congr 1
  rw [fourierBasis_repr, fourierCoeff_congr_ae (MemLp.coeFn_toLp
    (memLp_liftIco_two_pi
      (continuous_clampedHerglotzConormal hS hγ a.2 k).measurable hB)),
    fourierCoeff_liftIco_two_pi]
  exact (fourierCoeffOn_congr_Icc
    (fun θ hθ => clampedHerglotzConormal_eq hθ) n).symm

/-- The normalized compact-kernel quadratic form is exactly the physical
kernel contribution on the Herglotz conormal density. -/
theorem normalizedHerglotzConormal_correctedRemainder_pairing
    {Ω : Set ℂ} (hS : IsSmoothDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {K : NNReal} (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) (k : ℝ) (a : dirDensities) :
    (1 / (2 * π) : ℂ) *
      ⟪normalizedHerglotzConormal hS hγ k a,
        hsMatrixOp (correctedRemainderMatrix W 0 0)
          (summable_correctedRemainderMatrix_smoothDomain hS hγ hW hc
            (by norm_num) (by norm_num) (by norm_num) (by norm_num))
          (normalizedHerglotzConormal hS hγ k a)⟫_ℂ =
      l2Inner (herglotzConormal k a.1 γ)
        (fun θ => ∫ s in (0 : ℝ)..(2 * π),
          correctedKernel W θ s * herglotzConormal k a.1 γ s) := by
  obtain ⟨B, hB⟩ := exists_bound_clampedHerglotzConormal hK k a
  have hg := (continuous_clampedHerglotzConormal hS hγ a.2 k).measurable
  rw [normalizedHerglotzConormal_eq_smoothing_fourier hS hγ hK k a hB,
    map_smul, inner_smul_left, inner_smul_right]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal]
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast two_pi_pos.ne'
  calc
    _ = (2 * π : ℂ) *
        ⟪sobolevSmoothing (1 / 2) (by norm_num)
            ((fourierBasis (T := 2 * π)).repr
              ((memLp_liftIco_two_pi hg hB).toLp _)),
          hsMatrixOp (correctedRemainderMatrix W 0 0)
            (summable_correctedRemainderMatrix_smoothDomain hS hγ hW hc
              (by norm_num) (by norm_num) (by norm_num) (by norm_num))
            (sobolevSmoothing (1 / 2) (by norm_num)
              ((fourierBasis (T := 2 * π)).repr
                ((memLp_liftIco_two_pi hg hB).toLp _)))⟫_ℂ := by
          field_simp [hpi] <;> ring
    _ = l2Inner (clampedHerglotzConormal k γ a.1)
        (fun θ => ∫ s in (0 : ℝ)..(2 * π),
          correctedKernel W θ s * clampedHerglotzConormal k γ a.1 s) :=
      correctedRemainderOp_physical_pairing hS hγ hK hW hc hg hg hB hB
    _ = _ := by
      unfold l2Inner
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le two_pi_pos.le] at hθ
      rw [clampedHerglotzConormal_eq hθ]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le two_pi_pos.le] at hs
      rw [clampedHerglotzConormal_eq hs]

end PolyaNeumann
