module

public import RequestProject.PhysicalDrivenL2Reconstruction
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.LocalConformalVekuaTrace
public import RequestProject.PhysicalVolterraNormalization

/-!
# Genuine H¹ realization of the driven observation kernel

The actual zeroth factorial gauge of an L² driven vector determines
normalized Hardy input, with the ordinary `sqrt(2π)` Fourier scale.
Its regularity is supplied by the proved forced zeroth-row equation,
and its Fourier support by the actual physical moment criterion.
The physical H¹ Vekua series is centered at F(1), including mode zero.

This module is part of the verified dependency chain. Initial
conformal-coordinate existence and identification of the final physical
normal load remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate

local instance drivenRealizationTwoPiPos : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

private theorem driven_realization_circle_coeff
    (H : C(AddCircle (2 * Real.pi), ℂ)) :
    fourierCoeff H = fourierCoeffOn Real.two_pi_pos
      (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) := by
  funext n
  have he : AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) =
      (H : AddCircle (2 * Real.pi) → ℂ) := by
    funext q
    change H ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) :
      AddCircle (2 * Real.pi)) = H q
    have hrep : ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) :
        AddCircle (2 * Real.pi)) = q :=
      (AddCircle.equivIoc (2 * Real.pi) 0).symm_apply_apply q
    rw [hrep]
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) n
  simpa only [he, zero_add] using h

/-- The actual continuous circle representative of the zeroth driven
gauge. Its matching endpoint values come from the true observation kernel. -/
def physicalDrivenKernelCircleGauge
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hO : observationAdj W g = 0) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨AddCircle.liftIco (2 * Real.pi) 0
    (physicalDrivenGauge γ E (physicalDrivenVector W g) 0), by
    obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO 0
    exact AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
      (physicalDrivenGauge_continuousOn γ hγ E _
        (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) 0)⟩

theorem physicalDrivenKernelCircleGauge_apply
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hO : observationAdj W g = 0) (θ : ℝ) :
    physicalDrivenKernelCircleGauge γ hγ E hW g hg hO
      (θ : AddCircle (2 * Real.pi)) = physicalDrivenPeriodicGauge γ E W g 0 θ := rfl

theorem physicalDrivenKernelCircleGauge_fourierCoeff
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hO : observationAdj W g = 0) :
    fourierCoeff (physicalDrivenKernelCircleGauge γ hγ E hW g hg hO) =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) :=
  driven_realization_circle_coeff _

/-- The genuine normalized Hardy input of the driven kernel. The
ordinary averaged coefficient is multiplied by sqrt(2π) sqrt(λ_n). -/
def physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) : L2Z :=
  (Real.sqrt (2 * Real.pi) : ℂ) • sobVec (1 / 2 : ℝ)
    (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0))
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_half hγLip hγ hW g hg hO)

theorem physicalDrivenKernelInput_apply
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) (n : ℤ) :
    physicalDrivenKernelInput hγLip hγ hW g hg hO n =
      (Real.sqrt (2 * Real.pi) : ℂ) * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) n := by
  simp only [physicalDrivenKernelInput, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    sobVec_apply, mul_assoc]

theorem fromL2_physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) :
    fromL2 (1 / 2 : ℝ) (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      (Real.sqrt (2 * Real.pi) : ℂ) •
        fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) := by
  rw [physicalDrivenKernelInput, fromL2_smul, fromL2_sobVec]

/-- The normalized input has the actual extra half order supplied by
the forced zeroth-row equation, without a regularity premise on g's kernel. -/
theorem fromL2_physicalDrivenKernelInput_isSobolevSeq_one
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ)
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) := by
  rw [fromL2_physicalDrivenKernelInput]
  exact isSobolevSeq_smul _
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)

theorem normalizedHardyAverage_physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) :
    normalizedHardyAverage (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
      fromL2 (1 / 2 : ℝ) (physicalDrivenKernelInput hγLip hγ hW g hg hO) = _
  rw [fromL2_physicalDrivenKernelInput, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The initial Hardy value reconstructed from the derived coefficients
is the actual continuous driven zeroth gauge at every parameter. -/
theorem hardyFourierTrace_physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) θ =
      physicalDrivenPeriodicGauge γ E W g 0 θ := by
  let H := physicalDrivenKernelCircleGauge γ hγ.continuous E hW.1 g
    (intervalIntegrable_boundary_of_memLp g hg) hO
  have hcoef : fourierCoeff H =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) :=
    physicalDrivenKernelCircleGauge_fourierCoeff _ _ _ _ _ _ _
  have hsum : Summable (fun n => ‖fourierCoeff H n‖) := by
    rw [hcoef]
    have hreg : IsSobolevSeq (0 + 1 : ℝ)
        (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0)) := by
      simpa only [zero_add] using
        (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)
    exact (sq_tsum_norm_le (s := 0) (by norm_num)
      hreg).1
  rw [normalizedHardyAverage_physicalDrivenKernelInput, ← hcoef]
  exact hardyFourierTrace_fourierCoeff H hsum θ

private theorem driven_realization_volterra_congrOn
    {a h k : ℝ → ℂ} {T : ℝ} (he : EqOn h k (Icc 0 T)) :
    ∀ j θ, θ ∈ Icc 0 T →
      volterraPrimitiveIterate a h j θ = volterraPrimitiveIterate a k j θ := by
  intro j
  induction j with
  | zero => exact he
  | succ j ih =>
      intro θ hθ
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hθ.1] at hs
      dsimp only
      rw [ih s ⟨hs.1, hs.2.trans hθ.2⟩]

theorem driven_realization_continuousOn_memLp
    {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 (2 * Real.pi))) :
    MemLp f 2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound
    ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ =>
    hC θ (Ioc_subset_Icc_self hθ)

/-- A genuine boundary L² function with order-one coefficients equals
their continuous Fourier reconstruction a.e. This uses the actual
unitary boundary Fourier transform, without presuming a representative. -/
theorem boundaryL2_ae_hardyFourierTrace_of_H1
    (v : BoundaryL2)
    (hv : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ))) :
    (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      hardyFourierTrace (fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ)) := by
  let c := fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ)
  have hc : Summable (fun n => ‖c n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hv)).1
  let H := hardyCircleReconstruction c
  let f : ℝ → ℂ := fun θ => H (θ : AddCircle (2 * Real.pi))
  have hfc : Continuous f := H.continuous.comp (AddCircle.continuous_mk' _)
  have hfm := driven_realization_continuousOn_memLp hfc.continuousOn
  let w : BoundaryL2 := hfm.toLp f
  have haw : (w : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f := hfm.coeFn_toLp
  have hcoef : fourierCoeffOn Real.two_pi_pos (w : ℝ → ℂ) = c := by
    rw [fourierCoeffOn_congr_ae Real.two_pi_pos haw]
    change fourierCoeffOn Real.two_pi_pos
      (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) = c
    rw [← driven_realization_circle_coeff, hardyCircleReconstruction_fourierCoeff hc]
  have hF : boundaryFourier v = boundaryFourier w := by
    apply lp.ext
    funext n
    rw [boundaryFourier_apply, boundaryFourier_apply, hcoef]
  have he : v = w := boundaryFourier.injective hF
  have hav : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f := by
    rw [he]
    exact haw
  filter_upwards [hav] with θ hθ
  exact hθ.trans (hardyCircleReconstruction_coe hc θ)

/-- The actual boundary L² vector of the driven zeroth row. Continuity
and L² membership are derived from the integrable driven construction. -/
def physicalDrivenRowZeroL2
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) : BoundaryL2 :=
  (driven_realization_continuousOn_memLp
    (physicalDrivenRow_continuousOn _
      (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) 0)).toLp
    (physicalDrivenRow (physicalDrivenVector W g) 0)

theorem physicalDrivenRowZeroL2_ae
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    (physicalDrivenRowZeroL2 hW g hg : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        physicalDrivenRow (physicalDrivenVector W g) 0 :=
  MemLp.coeFn_toLp _

/-- Variation of constants gives the true `-i T g` zeroth trace for
integrable forcing, using only the actual Bochner integral construction. -/
theorem physicalDrivenRow_zero_eq_volterraOp_of_intervalIntegrable
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenRow (physicalDrivenVector W g) 0 θ = -Complex.I * volterraOp W g θ := by
  have hi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 θ := by
    apply (physicalDrivenIntegrand_intervalIntegrable hW g hg).mono_set'
    rw [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le]
    exact Ioc_subset_Ioc_right hθ.2
  let A : Ell2 →L[ℂ] ℂ := (innerSL ℂ (basisVec 0)).comp (W θ)
  have hA := A.intervalIntegral_comp_comm hi
  have hinner : inner ℂ (basisVec 0)
      (W θ (∫ s in (0 : ℝ)..θ, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))) =
      volterraOp W g θ := by
    simp only [A, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      map_smul, smul_eq_mul] at hA
    rw [← hA]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [volterraKernel]
    ring
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  change (Real.sqrt 2 : ℂ) * (physicalDrivenVector W g θ : ℕ → ℂ) 0 = _
  rw [← inner_basisVec]
  simp only [physicalDrivenVector, inner_smul_right, hinner]
  field_simp [hs0]

theorem normalizedHardyAverage_localConformalDiskHalfTrace
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    normalizedHardyAverage (localConformalDiskHalfTrace hR F hFs hL u) =
      fourierCoeffOn Real.two_pi_pos (localConformalDiskH1Trace hR F hFs hL u) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  funext n
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
    fromL2 (1 / 2 : ℝ) (localConformalDiskHalfTrace hR F hFs hL u) n = _
  rw [fromL2_half_localConformalDiskHalfTrace, boundaryFourier_apply,
    ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

private theorem driven_realization_closed_deriv_ne_zero
    {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2) :
    ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0 := by
  have hc : ContinuousOn (fun z => C * ‖fderiv ℝ F z 1‖ ^ 2)
      (closedBall (0 : ℂ) 1) :=
    (continuousOn_const.mul
      ((((hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
        continuousOn_const).norm).pow 2)).mono (closedBall_subset_ball hR)
  have hle : ∀ z ∈ ball (0 : ℂ) 1, (1 : ℝ) ≤ C * ‖fderiv ℝ F z 1‖ ^ 2 := by
    intro z hz
    have hfd : fderiv ℝ F z 1 = deriv F z := by
      rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
      change fderiv ℂ F z 1 = _
      rw [fderiv_eq_deriv_mul, mul_one]
    rw [hfd]
    exact hC z hz
  intro z hz hzero
  have hbound : (1 : ℝ) ≤ C * ‖fderiv ℝ F z 1‖ ^ 2 := by
    apply le_on_closure hle continuousOn_const
    · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hc
    · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa only [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      using hbound
  norm_num at hbad

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
    {L : NNReal} (hγLip : LipschitzWith L (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0)

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "hγF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (by simp))
local notation "bF" => physicalDrivenKernelInput hγLip hγF hW g hg hO

include hb hL hhol hC e he hsource hE in
/-- The normalized input of an actual driven observation-kernel vector
lies in the full nonpositive Fourier sector, including its constant mode. -/
theorem physicalDrivenKernelInput_nonpositive : IsNonpositiveFourierSupport bF := by
  have hinjc : InjOn F (closedBall (0 : ℂ) 1) := by
    intro z hz w hw hzw
    apply e.injOn (hsource hz) (hsource hw)
    simpa only [he] using hzw
  have hs := localConformal_physicalDrivenGauge_nonpositive_of_memLp hb hL hR F hFs
    hhol hinjc (driven_realization_closed_deriv_ne_zero hR F hFs hhol hC) rfl
    hγLip hE hW g hg hO 0
  intro n hn
  rw [physicalDrivenKernelInput_apply, hs n hn, mul_zero]

/-- The actual interior H¹ vector determined by the driven observation
kernel, centered at the same genuine boundary basepoint F(1). -/
def physicalDrivenKernelH1 : NeumannH1 ΩF :=
  localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK
    e he hsource hes (E : ℂ) bF

include hE in
/-- The all-input actual Volterra trace series reconstructs the genuine
driven zeroth row. No zero-trace kernel formula is used in this proof. -/
theorem physicalDrivenKernelH1_trace_reconstruction
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    hardyFourierTrace (normalizedHardyAverage
      (localConformalDiskHalfTrace hR F hFs hL
        (physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
          e he hsource hes hγLip hW g hg hO))) θ =
      physicalDrivenRow (physicalDrivenVector W g) 0 θ := by
  have hbn := physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC
    e he hsource hγLip hE hW g hg hO
  have hreg := fromL2_physicalDrivenKernelInput_isSobolevSeq_one hγLip hγF hW g hg hO
  have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 hR F hFs hb hL
    hhol hinj hC hK e he hsource hes (E : ℂ) bF hbn hreg θ
  have hprim (j : ℕ) :
      volterraPrimitiveIterate (fun s => star (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage bF)) j θ =
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (physicalDrivenGauge (physicalCircleTrace F) E (physicalDrivenVector W g) 0) j θ := by
    apply driven_realization_volterra_congrOn (T := 2 * Real.pi) ?_ j θ hθ
    intro s hs
    rw [hardyFourierTrace_physicalDrivenKernelInput,
      physicalDrivenPeriodicGauge_eqOn _ E W g hO 0 hs]
  have hcenter : F (circleMap 0 1 θ) - F 1 =
      physicalDrivenCentered (physicalCircleTrace F) θ := by
    simp [physicalDrivenCentered, physicalCircleTrace, circleMap_zero]
  change hardyFourierTrace (normalizedHardyAverage
    (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
      e he hsource hes (E : ℂ) bF)) θ = _
  calc
    _ = ∑' j : ℕ, physicalVekuaCoeff (E : ℂ) j *
        (F (circleMap 0 1 θ) - F 1) ^ j *
        volterraPrimitiveIterate (fun s => star (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (normalizedHardyAverage bF)) j θ := hs.tsum_eq.symm
    _ = ∑' j : ℕ, (-(E : ℂ) / 4) ^ j / (j.factorial : ℂ) *
        physicalDrivenCentered (physicalCircleTrace F) θ ^ j *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (physicalDrivenGauge (physicalCircleTrace F) E (physicalDrivenVector W g) 0) j θ := by
      apply tsum_congr
      intro j
      rw [hprim, hcenter]
      rfl
    _ = _ := (physicalDrivenRow_eq_volterraVekua_of_nonnegative_of_memLp
      hγLip hγF hE.le hW g hg hθ).symm

include hE in
/-- The actual ordinary coordinate trace of the constructed physical H¹
vector is the actual driven row in boundary L², with its correct scale. -/
theorem physicalDrivenKernelH1_coordinate_trace_ae :
    (localConformalDiskH1Trace hR F hFs hL
      (physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγLip hW g hg hO) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        physicalDrivenRow (physicalDrivenVector W g) 0 := by
  let u := physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγLip hW g hg hO
  have hbn := physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC
    e he hsource hγLip hE hW g hg hO
  have hraw := localConformalVekuaBoundary_raw_H1 hR F hFs hb hL hhol hinj hC hK
    e he hsource hes (E : ℂ) bF hbn
    (fromL2_physicalDrivenKernelInput_isSobolevSeq_one hγLip hγF hW g hg hO)
  have havg : IsSobolevSeq 1 (normalizedHardyAverage
      (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (E : ℂ) bF)) := isSobolevSeq_smul _ hraw
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace hR F hFs hL u
  change normalizedHardyAverage
      (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (E : ℂ) bF) =
    fourierCoeffOn Real.two_pi_pos (localConformalDiskH1Trace hR F hFs hL u) at hcoef
  have htrace := boundaryL2_ae_hardyFourierTrace_of_H1
    (localConformalDiskH1Trace hR F hFs hL u) (by rw [← hcoef]; exact havg)
  rw [← hcoef] at htrace
  filter_upwards [htrace, ae_restrict_mem measurableSet_Ioc] with θ ht hθ
  exact ht.trans (physicalDrivenKernelH1_trace_reconstruction hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγLip hE hW g hg hO (Ioc_subset_Icc_self hθ))

include hE in
/-- Equality in the genuine boundary L² space, rather than only a
formal coefficient reconstruction or a chosen pointwise representative. -/
theorem physicalDrivenKernelH1_coordinate_trace :
    localConformalDiskH1Trace hR F hFs hL
      (physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγLip hW g hg hO) =
      physicalDrivenRowZeroL2 hW.1 g (intervalIntegrable_boundary_of_memLp g hg) := by
  apply Lp.ext
  exact (physicalDrivenKernelH1_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγLip hE hW g hg hO).trans
      (physicalDrivenRowZeroL2_ae hW.1 g (intervalIntegrable_boundary_of_memLp g hg)).symm

include hE in
/-- The reconstructed coordinate trace is precisely `-i T g` for the
actual transport and arbitrary L² forcing in its observation kernel. -/
theorem physicalDrivenKernelH1_coordinate_trace_eq_volterra_ae :
    (localConformalDiskH1Trace hR F hFs hL
      (physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγLip hW g hg hO) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        (fun θ => -Complex.I * volterraOp W g θ) := by
  filter_upwards [physicalDrivenKernelH1_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγLip hE hW g hg hO, ae_restrict_mem measurableSet_Ioc]
    with θ ht hθ
  exact ht.trans (physicalDrivenRow_zero_eq_volterraOp_of_intervalIntegrable hW.1 g
    (intervalIntegrable_boundary_of_memLp g hg) (Ioc_subset_Icc_self hθ))

include hE in
/-- The constructed actual interior vector satisfies the real-energy
Helmholtz equation against every genuine compact interior test. -/
theorem physicalDrivenKernelH1_weakHelmholtz {φ : ℂ → ℂ} (hφ : TestFunction ΩF φ) :
    (∫ z in ΩF, h1Value ΩF (physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγLip hW g hg hO) z * (lap φ z + (E : ℂ) * φ z)) = 0 := by
  exact localConformalVekuaH1_weakHelmholtz hR F hFs hb hL hhol hinj hC hK
    e he hsource hes (F 1) (E : ℂ) bF
    (physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC e he hsource
      hγLip hE hW g hg hO) hφ

end PhysicalCoordinates

end PolyaNeumann

end
