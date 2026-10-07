module

public import RequestProject.LocalConformalForcedModes
public import RequestProject.LocalConformalPrincipalFactorization
public import RequestProject.NeumannProjectedWeak

/-!
# The actual regular Neumann principal part in supplied conformal coordinates

The projected weak equation has physical mass forcing
`E • u_reg - (E₀ + 1) • w`, where `w` is the actual resonant projection
of the load. Its harmonic tests give a factorization of the actual regular
normalized NtD remainder through one Fourier derivative. The zero mode is
retained by the genuine rank-one projection. The same zero-load tests give
the one-derivative factor of the actual Neumann residue.

Existence of the supplied smooth conformal coordinates is a separate
obligation; none of these statements adds coordinates to the final theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real InnerProductSpace ComplexConjugate

private theorem regular_sobolevSmoothing_one_apply (b : L2Z) (n : ℤ) :
    sobolevSmoothing 1 (by norm_num) b n = (sobWeight n : ℂ)⁻¹ * b n := by
  simp only [sobolevSmoothing, diagOp_apply, Real.rpow_neg_one, Complex.ofReal_inv]

private theorem forced_remainder_scalar {s k : ℝ}
    (hk : k ≠ 0) (hs : s ≠ 0) (hsk : s = k + 1)
    {t b d : ℂ} (h : t - ((s / k : ℝ) : ℂ) * b = d) :
    t - b = (s : ℂ)⁻¹ *
      (((s / k : ℝ) : ℂ) * b + (s : ℂ) * d) := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hskc : (s : ℂ) = (k : ℂ) + 1 := by exact_mod_cast hsk
  have hsc' : (k : ℂ) + 1 ≠ 0 := by rwa [hskc] at hsc
  calc
    t - b = ((s / k : ℝ) : ℂ) * b - b + d := by linear_combination h
    _ = _ := by
      simp only [Complex.ofReal_div, hskc]
      field_simp [hkc, hsc']
      ring

private theorem forced_remainder_mode (n : ℤ) (hn : n ≠ 0)
    {t b d : ℂ} (h : t - normalizedInverseAbsSymbol n * b = d) :
    t - b = (sobWeight n : ℂ)⁻¹ *
      (normalizedInverseAbsSymbol n * b + (sobWeight n : ℂ) * d) := by
  have hk : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hn)
  have hs : sobWeight n ≠ 0 := (sobWeight_pos n).ne'
  have hsk : sobWeight n = |(n : ℝ)| + 1 := by unfold sobWeight; ring
  simp only [normalizedInverseAbsSymbol, if_neg hn] at h ⊢
  exact forced_remainder_scalar hk hs hsk h

private theorem forced_principal_factorization_of_modes
    (T M : L2Z →L[ℂ] L2Z) (d : L2Z → ℤ → ℂ)
    (hM : ∀ b n, M b n = (sobWeight n : ℂ) * d b n)
    (hz : ∀ b, d b 0 = 0)
    (hm : ∀ b n, n ≠ 0 → T b n - normalizedInverseAbsSymbol n * b n = d b n) :
    T - 1 = (sobolevSmoothing 1 (by norm_num)).comp
      (normalizedInverseAbsOperator + M) + zeroModeProjection.comp (T - 1) := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    regular_sobolevSmoothing_one_apply, normalizedInverseAbsOperator_apply,
    zeroModeProjection_apply, lp.coeFn_sub, lp.coeFn_add,
    Pi.sub_apply, Pi.add_apply, hM]
  by_cases hn : n = 0
  · subst n
    simp [normalizedInverseAbsSymbol, hz]
  · rw [if_neg hn, zero_mul, add_zero]
    exact forced_remainder_mode n hn (hm b n hn)

private theorem zero_load_factorization_of_modes
    (T M : L2Z →L[ℂ] L2Z) (d : L2Z → ℤ → ℂ)
    (hM : ∀ b n, M b n = (sobWeight n : ℂ) * d b n)
    (hz : ∀ b, d b 0 = 0)
    (hm : ∀ b n, n ≠ 0 → T b n = d b n) :
    T = (sobolevSmoothing 1 (by norm_num)).comp M + zeroModeProjection.comp T := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    regular_sobolevSmoothing_one_apply, zeroModeProjection_apply,
    lp.coeFn_add, Pi.add_apply, hM]
  by_cases hn : n = 0
  · subst n
    simp [hz]
  · rw [if_neg hn, zero_mul, add_zero, hm b n hn]
    have hw : (sobWeight n : ℂ) ≠ 0 := by exact_mod_cast (sobWeight_pos n).ne'
    rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]

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

/-- The actual mass input of the projected regular weak equation. -/
def localConformalRegularMassInput (E₀ E : ℝ) :
    L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  (((E : ℂ) • h1RegularResolvent (F '' ball (0 : ℂ) 1) E₀ E) -
    ((E₀ + 1 : ℝ) : ℂ) • (h1ResonantSpace (F '' ball (0 : ℂ) 1) E₀).starProjection).comp
      (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL))

/-- The actual regular interior solution satisfies the general forced
weak equation with the genuine projected mass input above. -/
theorem localConformalRegular_isForcedSolution {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E)) (b : L2Z) :
    IsNormalizedNeumannForcedSolution (localConformalDiskHalfTrace hR F hFs hL) b
      (h1RegularResolvent (F '' ball (0 : ℂ) 1) E₀ E
        (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL) b))
      (localConformalRegularMassInput hR F hFs hL E₀ E b) := by
  intro v
  have h := h1RegularResolvent_adjoint_weak_pairing
    (localConformalDiskHalfTrace hR F hFs hL) hE₀ hunit b v
  simp only [localConformalRegularMassInput, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_smul, inner_sub_right, inner_smul_right]
  linear_combination h

/-- Every actual resonant vector is a zero-load forced solution with
physical mass input `E₀ • w`. -/
theorem localConformalResonant_isForcedSolution {E₀ : ℝ}
    {w : NeumannH1 (F '' ball (0 : ℂ) 1)}
    (hw : w ∈ h1ResonantSpace (F '' ball (0 : ℂ) 1) E₀) :
    IsNormalizedNeumannForcedSolution (localConformalDiskHalfTrace hR F hFs hL) 0 w
      ((E₀ : ℂ) • w) := by
  intro v
  simp only [map_smul, inner_smul_right, inner_zero_right]
  rw [h1Resonant_weak_pairing hw v, sub_self]

/-- The bounded factor before the compact one-derivative smoothing in
the actual regular normalized NtD remainder. -/
def localConformalRegularPrincipalFactor (E₀ E : ℝ) : L2Z →L[ℂ] L2Z :=
  normalizedInverseAbsOperator + (localConformalMassFourierH1 hR F hFs hL hK).comp
    (localConformalRegularMassInput hR F hFs hL E₀ E)

include hb hhol hinj hC e he hsource hes in
theorem localConformal_regular_principal_factorization {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E)) :
    normalizedNeumannRegular (localConformalDiskHalfTrace hR F hFs hL) E₀ E - 1 =
      (sobolevSmoothing 1 (by norm_num)).comp
        (localConformalRegularPrincipalFactor hR F hFs hL hK E₀ E) +
      zeroModeProjection.comp
        (normalizedNeumannRegular (localConformalDiskHalfTrace hR F hFs hL) E₀ E - 1) := by
  refine forced_principal_factorization_of_modes
    (normalizedNeumannRegular (localConformalDiskHalfTrace hR F hFs hL) E₀ E)
    ((localConformalMassFourierH1 hR F hFs hL hK).comp
      (localConformalRegularMassInput hR F hFs hL E₀ E))
    (fun b n => diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK
      (localConformalRegularMassInput hR F hFs hL E₀ E b)) n) ?_ ?_ ?_
  · intro b n
    simp only [ContinuousLinearMap.comp_apply, localConformalMassFourierH1_apply]
  · intro b
    simp only [diskMassForcingCoeff]
  · intro b n hn
    have hforced := localConformalRegular_isForcedSolution hR F hFs hL hE₀ hunit b
    have hm := localConformal_forced_principal_mode_ne_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b
      (h1RegularResolvent (F '' ball (0 : ℂ) 1) E₀ E
        (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL) b))
      (localConformalRegularMassInput hR F hFs hL E₀ E b) hforced n hn
    simpa only [normalizedNeumannRegular, ContinuousLinearMap.comp_apply,
      normalizedInverseAbsSymbol, if_neg hn] using hm

include hb hhol hinj hC e he hsource hes in
theorem isCompactOperator_localConformal_normalizedNeumannRegular_sub_one
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E)) :
    IsCompactOperator
      (normalizedNeumannRegular (localConformalDiskHalfTrace hR F hFs hL) E₀ E -
        (1 : L2Z →L[ℂ] L2Z)) := by
  obtain ⟨K, _, hK⟩ := exists_localConformalMassDensity_bound hR F hFs
  rw [localConformal_regular_principal_factorization hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE₀ hunit]
  exact ((isCompactOperator_sobolevSmoothing (by norm_num : (0 : ℝ) < 1)).comp_clm
    (localConformalRegularPrincipalFactor hR F hFs hL hK E₀ E)).add
      (isCompactOperator_zeroModeProjection.comp_clm
        (normalizedNeumannRegular (localConformalDiskHalfTrace hR F hFs hL) E₀ E - 1))

/-- The actual residue's bounded one-derivative factor, obtained from
zero-load harmonic tests rather than an assumed trace formula. -/
def localConformalResiduePrincipalFactor (E₀ : ℝ) : L2Z →L[ℂ] L2Z :=
  ((E₀ + 1 : ℝ) : ℂ) • ((localConformalMassFourierH1 hR F hFs hL hK).comp
    (((E₀ : ℂ) • (h1ResonantSpace (F '' ball (0 : ℂ) 1) E₀).starProjection).comp
      (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL))))

include hb hhol hinj hC e he hsource hes in
theorem localConformal_residue_principal_factorization (E₀ : ℝ) :
    normalizedNeumannResidue (localConformalDiskHalfTrace hR F hFs hL) E₀ =
      (sobolevSmoothing 1 (by norm_num)).comp
        (localConformalResiduePrincipalFactor hR F hFs hL hK E₀) +
      zeroModeProjection.comp
        (normalizedNeumannResidue (localConformalDiskHalfTrace hR F hFs hL) E₀) := by
  refine zero_load_factorization_of_modes
    (normalizedNeumannResidue (localConformalDiskHalfTrace hR F hFs hL) E₀)
    (localConformalResiduePrincipalFactor hR F hFs hL hK E₀)
    (fun b n => ((E₀ + 1 : ℝ) : ℂ) * diskMassForcingCoeff
      (localConformalMassForcing hR F hFs hL hK
        ((E₀ : ℂ) • (h1ResonantSpace (F '' ball (0 : ℂ) 1) E₀).starProjection
          (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL) b))) n)
    ?_ ?_ ?_
  · intro b n
    simp only [localConformalResiduePrincipalFactor, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, localConformalMassFourierH1_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · intro b
    simp only [diskMassForcingCoeff, mul_zero]
  · intro b n hn
    have hw := (h1ResonantSpace (F '' ball (0 : ℂ) 1) E₀).starProjection_apply_mem
      (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL) b)
    have hforced := localConformalResonant_isForcedSolution hR F hFs hL hw
    have hm := localConformal_forced_principal_mode_ne_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes 0
      ((h1ResonantSpace (F '' ball (0 : ℂ) 1) E₀).starProjection
        (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL) b))
      ((E₀ : ℂ) • (h1ResonantSpace (F '' ball (0 : ℂ) 1) E₀).starProjection
        (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL) b))
      hforced n hn
    simp only [lp.coeFn_zero, Pi.zero_apply, mul_zero, sub_zero] at hm
    simpa only [normalizedNeumannResidue, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using
      congrArg (fun z : ℂ => ((E₀ + 1 : ℝ) : ℂ) * z) hm

include hb hhol hinj hC e he hsource hes in
theorem isCompactOperator_localConformal_normalizedNeumannResidue (E₀ : ℝ) :
    IsCompactOperator (normalizedNeumannResidue (localConformalDiskHalfTrace hR F hFs hL) E₀) := by
  obtain ⟨K, _, hK⟩ := exists_localConformalMassDensity_bound hR F hFs
  rw [localConformal_residue_principal_factorization hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E₀]
  exact ((isCompactOperator_sobolevSmoothing (by norm_num : (0 : ℝ) < 1)).comp_clm
    (localConformalResiduePrincipalFactor hR F hFs hL hK E₀)).add
      (isCompactOperator_zeroModeProjection.comp_clm
        (normalizedNeumannResidue (localConformalDiskHalfTrace hR F hFs hL) E₀))

/-- The regular one-derivative factor is continuous wherever the genuine
fixed-complement inverse is continuous. -/
theorem continuousOn_localConformalRegularPrincipalFactor {E₀ : ℝ} {U : Set ℝ}
    (hi : ContinuousOn (fun E =>
      Ring.inverse (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E)) U) :
    ContinuousOn (localConformalRegularPrincipalFactor hR F hFs hL hK E₀) U := by
  have hE : ContinuousOn (fun E : ℝ => (E : ℂ)) U :=
    Complex.continuous_ofReal.continuousOn
  have hreg : ContinuousOn (h1RegularResolvent (F '' ball (0 : ℂ) 1) E₀) U :=
    continuousOn_h1RegularResolvent hi
  have hforce : ContinuousOn (localConformalRegularMassInput hR F hFs hL E₀) U := by
    unfold localConformalRegularMassInput
    exact ((hE.smul hreg).sub continuousOn_const).clm_comp continuousOn_const
  unfold localConformalRegularPrincipalFactor
  exact continuousOn_const.add (continuousOn_const.clm_comp hforce)

end

end PolyaNeumann

end
