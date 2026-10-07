module

public import RequestProject.LocalConformalRegularPrincipal
public import RequestProject.CorrectedKernelSobolevGain

/-!
# The Fourier operator assembled from the genuine regular Neumann map

The definition uses the actual regular weak resolvent and the actual
corrected-kernel matrix. Its compact principal remainder is proved here.
Identification with the physical periodic boundary expression is a
separate mathematical statement, not an assumption of this file.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric

private theorem normalizedAbs_symbol_sub_one {n : ℤ} (hn : n ≠ 0) :
    normalizedInverseAbsSymbol n - 1 =
      ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) * normalizedInverseAbsSymbol n := by
  have hw : sobWeight n ≠ 0 := (sobWeight_pos n).ne'
  have habs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr hn)
  have hr : sobWeight n / |(n : ℝ)| - 1 =
      sobWeight n ^ (-(1 : ℝ)) * (sobWeight n / |(n : ℝ)|) := by
    rw [Real.rpow_neg (sobWeight_pos n).le, Real.rpow_one]
    field_simp [hw, habs]
    simp only [sobWeight]
    ring
  simp only [normalizedInverseAbsSymbol, if_neg hn]
  exact_mod_cast hr

theorem normalizedInverseAbsOperator_sub_one_factorization :
    normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z) =
      (sobolevSmoothing 1 zero_le_one).comp normalizedInverseAbsOperator -
        zeroModeProjection := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, lp.coeFn_sub, Pi.sub_apply,
    normalizedInverseAbsOperator_apply, sobolevSmoothing, diagOp_apply,
    zeroModeProjection_apply]
  by_cases hn : n = 0
  · subst n
    simp [normalizedInverseAbsSymbol]
  · simp only [if_neg hn, zero_mul, sub_zero]
    calc
      _ = (normalizedInverseAbsSymbol n - 1) * b n := by ring
      _ = _ := by rw [normalizedAbs_symbol_sub_one hn]; ring

theorem isCompactOperator_normalizedInverseAbsOperator_sub_one :
    IsCompactOperator (normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z)) := by
  rw [normalizedInverseAbsOperator_sub_one_factorization]
  exact ((isCompactOperator_sobolevSmoothing zero_lt_one).comp_clm
    normalizedInverseAbsOperator).sub isCompactOperator_zeroModeProjection

def normalizedPeriodicRegularOperator {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
    principalNormalized + hsMatrixOp (correctedRemainderMatrix W 0 0) hbase

theorem normalizedPeriodicRegularOperator_sub_four_posProj_compact
    {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (hN : IsCompactOperator (normalizedNeumannRegular Q E₀ E - (1 : L2Z →L[ℂ] L2Z))) :
    IsCompactOperator (normalizedPeriodicRegularOperator Q E₀ E W hbase -
      (4 : ℂ) • posProj) := by
  have hdiff : IsCompactOperator (normalizedNeumannRegular Q E₀ E -
      normalizedInverseAbsOperator) := by
    have heq : normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator =
        (normalizedNeumannRegular Q E₀ E - 1) - (normalizedInverseAbsOperator - 1) := by abel
    rw [heq]
    exact hN.sub isCompactOperator_normalizedInverseAbsOperator_sub_one
  have heq : normalizedPeriodicRegularOperator Q E₀ E W hbase - (4 : ℂ) • posProj =
      (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
        (principalNormalized - (4 : ℂ) • posProj) +
          hsMatrixOp (correctedRemainderMatrix W 0 0) hbase := by
    unfold normalizedPeriodicRegularOperator
    abel
  rw [heq]
  exact ((hdiff.smul (2 : ℂ)).add principal_normalized_sub_four_posProj_compact).add
    (isCompactOperator_hsMatrixOp _ hbase)

section PhysicalCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

include hb hhol hinj hC e he hsource hes in
theorem localConformal_normalizedPeriodicRegular_sub_four_posProj_compact
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E))
    (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    IsCompactOperator (normalizedPeriodicRegularOperator
      (localConformalDiskHalfTrace hR F hFs hL) E₀ E W hbase - (4 : ℂ) • posProj) := by
  exact normalizedPeriodicRegularOperator_sub_four_posProj_compact
    (localConformalDiskHalfTrace hR F hFs hL) E₀ E W hbase
    (isCompactOperator_localConformal_normalizedNeumannRegular_sub_one
      hR F hFs hb hL hhol hinj hC e he hsource hes hE₀ hunit)

end PhysicalCoordinates

end PolyaNeumann

end
