module

public import RequestProject.NormalizedPeriodicRegular
public import RequestProject.FourierFiniteRankRegularity

/-!
# Sobolev gains of the actual regular periodic remainder

The genuine weak regular Neumann factorization gives an order-one
remainder on every normalized input. Together with the actual corrected
matrix, this yields the two Sobolev gains needed for the reduced kernel.
No regularity conclusion is inferred from compactness alone.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped InnerProductSpace

theorem isSobolevSeq_sobolevSmoothing (s : ℝ) (hs : 0 ≤ s) (b : L2Z) :
    IsSobolevSeq s (sobolevSmoothing s hs b : ℤ → ℂ) :=
  isSobolevSeq_fromL2 s b

theorem isSobolevSeq_zeroModeProjection (s : ℝ) (b : L2Z) :
    IsSobolevSeq s (zeroModeProjection b : ℤ → ℂ) := by
  apply isSobolevSeq_of_finite_fourier_support
  refine (finite_singleton (0 : ℤ)).subset ?_
  intro n hn
  by_contra hn0
  have hn0' : n ≠ 0 := by simpa only [mem_singleton_iff] using hn0
  exact hn (by simp [zeroModeProjection_apply, hn0'])

theorem normalizedInverseAbsOperator_sub_one_sobolev (b : L2Z) :
    IsSobolevSeq 1
      ((normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z)) b : ℤ → ℂ) := by
  rw [normalizedInverseAbsOperator_sub_one_factorization]
  change _ ∈ fourierSobolevSubmodule 1
  exact (fourierSobolevSubmodule 1).sub_mem
    (isSobolevSeq_sobolevSmoothing 1 zero_le_one (normalizedInverseAbsOperator b))
    (isSobolevSeq_zeroModeProjection 1 b)

theorem principalNormalized_eq_four_inverseAbs_posProj :
    principalNormalized =
      (4 : ℂ) • normalizedInverseAbsOperator.comp posProj := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    lp.coeFn_smul, Pi.smul_apply, principalNormalized, posProj, diagOp_apply,
    normalizedInverseAbsOperator_apply, smul_eq_mul]
  by_cases hn : 0 < n
  · have hn0 : n ≠ 0 := hn.ne'
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    simp only [if_pos hn, one_mul, principalSymbol_pos hn,
      normalizedInverseAbsSymbol, if_neg hn0, sobWeight, abs_of_pos hnr]
    push_cast
    field_simp [hnc]
    ring
  · rcases lt_or_eq_of_le (le_of_not_gt hn) with hneg | hzero
    · simp [if_neg hn, principalSymbol_neg hneg]
    · subst n
      simp [principalSymbol, normalizedInverseAbsSymbol]

theorem principalNormalized_sub_four_posProj_sobolev (b : L2Z) :
    IsSobolevSeq 1 ((principalNormalized - (4 : ℂ) • posProj) b : ℤ → ℂ) := by
  have heq : principalNormalized - (4 : ℂ) • posProj =
      (4 : ℂ) • (normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z)).comp posProj := by
    rw [principalNormalized_eq_four_inverseAbs_posProj,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp, smul_sub]
  rw [heq]
  change _ ∈ fourierSobolevSubmodule 1
  exact (fourierSobolevSubmodule 1).smul_mem (4 : ℂ)
    (normalizedInverseAbsOperator_sub_one_sobolev (posProj b))

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

local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

include hb hhol hinj hC hK e he hsource hes in
theorem localConformal_normalizedNeumannRegular_sub_one_sobolev
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E)) (b : L2Z) :
    IsSobolevSeq 1
      ((normalizedNeumannRegular QF E₀ E - (1 : L2Z →L[ℂ] L2Z)) b : ℤ → ℂ) := by
  rw [localConformal_regular_principal_factorization hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE₀ hunit]
  change _ ∈ fourierSobolevSubmodule 1
  exact (fourierSobolevSubmodule 1).add_mem
    (isSobolevSeq_sobolevSmoothing 1 zero_le_one
      (localConformalRegularPrincipalFactor hR F hFs hL hK E₀ E b))
    (isSobolevSeq_zeroModeProjection 1
      ((normalizedNeumannRegular QF E₀ E - 1) b))

include hb hhol hinj hC hK e he hsource hes in
theorem localConformal_normalizedNeumannRegular_sub_inverseAbs_sobolev
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E)) (b : L2Z) :
    IsSobolevSeq 1
      ((normalizedNeumannRegular QF E₀ E - normalizedInverseAbsOperator) b : ℤ → ℂ) := by
  have heq : normalizedNeumannRegular QF E₀ E - normalizedInverseAbsOperator =
      (normalizedNeumannRegular QF E₀ E - 1) -
        (normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z)) := by abel
  rw [heq]
  change _ ∈ fourierSobolevSubmodule 1
  exact (fourierSobolevSubmodule 1).sub_mem
    (localConformal_normalizedNeumannRegular_sub_one_sobolev hR F hFs hb hL hhol hinj
      hC hK e he hsource hes hE₀ hunit b)
    (normalizedInverseAbsOperator_sub_one_sobolev b)

include hb hhol hinj hC hK e he hsource hes in
theorem localConformal_periodicRegular_remainder_sobolev_gain
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E))
    {L L' : NNReal} {γ : ℝ → ℂ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ)
    (hγ' : ∀ x ∈ Icc 0 (2 * Real.pi), ∀ y ∈ Icc 0 (2 * Real.pi),
      ‖deriv γ x - deriv γ y‖ ≤ L' * |x - y|)
    (hW : IsTransport γ E W) (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    {s δ : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) (hst : s + δ ≤ 1)
    (b : L2Z) (hbs : IsSobolevSeq s (b : ℤ → ℂ)) :
    IsSobolevSeq (s + δ)
      ((normalizedPeriodicRegularOperator QF E₀ E W hbase - (4 : ℂ) • posProj) b : ℤ → ℂ) := by
  have hN := (sobNormSq_mono hst
    (localConformal_normalizedNeumannRegular_sub_inverseAbs_sobolev hR F hFs hb hL hhol
      hinj hC hK e he hsource hes hE₀ hunit b)).1
  have hP := (sobNormSq_mono hst (principalNormalized_sub_four_posProj_sobolev b)).1
  have hC' := correctedRemainderOp_sobolev_gain hγLip hγ' hW hcut hδ hδ' hs hs' hbase b hbs
  have heq : normalizedPeriodicRegularOperator QF E₀ E W hbase - (4 : ℂ) • posProj =
      (2 : ℂ) • (normalizedNeumannRegular QF E₀ E - normalizedInverseAbsOperator) +
        (principalNormalized - (4 : ℂ) • posProj) +
          hsMatrixOp (correctedRemainderMatrix W 0 0) hbase := by
    unfold normalizedPeriodicRegularOperator
    abel
  rw [heq]
  change _ ∈ fourierSobolevSubmodule (s + δ)
  exact (fourierSobolevSubmodule (s + δ)).add_mem
    ((fourierSobolevSubmodule (s + δ)).add_mem
      ((fourierSobolevSubmodule (s + δ)).smul_mem (2 : ℂ) hN) hP) hC'

end PhysicalCoordinates

end PolyaNeumann

end
