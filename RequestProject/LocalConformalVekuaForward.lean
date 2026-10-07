module

public import RequestProject.LocalConformalReducedCoercivity
public import RequestProject.PeriodicForm

/-!
# Genuine forward Vekua transport with ordinary L2 forcing

The actual Fourier conormal identity is inverted using an interval
primitive of an ordinary boundary L2 element. This retains frequency zero
and the actual initial value; absolute continuity is a conclusion. The
positive rows are the already constructed absolutely convergent Ell2
series. Together they give the true driven integral equation and its
periodic observation identity.

All statements are conditional on the supplied conformal coordinates.
No existence of those coordinates or regularity of arbitrary negative
half-order boundary loads is inferred. These statements are part of the
verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology ComplexConjugate InnerProductSpace

local instance forwardTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Fourier inversion for an actual L2 derivative. No absolute continuity
or differentiability of the original continuous function is assumed. -/
theorem eq_add_integral_of_L2_periodic_fourier_derivative
    {v : ℝ → ℂ} (hv : Continuous v)
    (hvper : Function.Periodic v (2 * Real.pi)) (d : BoundaryL2)
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos (d : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos v n)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    v θ = v 0 + ∫ s in (0 : ℝ)..θ, d s := by
  let P : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, d s
  have hPi := intervalIntegrable_boundaryL2 d
  have hPAC : AbsolutelyContinuousOnInterval P 0 (2 * Real.pi) :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hPi
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hPC : ContinuousOn P (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hPAC.continuousOn
  have hPD : ∀ᵐ t, t ∈ Ioo 0 (2 * Real.pi) → HasDerivAt P (d t) t :=
    ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hPi
  have hP0 : P 0 = 0 := by simp [P]
  have hPT : P (2 * Real.pi) = 0 :=
    integral_eq_zero_of_periodic_fourier_derivative hcoeff
  have hPc (n : ℤ) : fourierCoeffOn Real.two_pi_pos (d : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos P n :=
    fourierCoeffOn_of_ac_ae_hasDerivAt hPAC (Lp.memLp d) hPD (hP0.trans hPT.symm) n
  have hncoeff (n : ℤ) (hn : n ≠ 0) :
      fourierCoeffOn Real.two_pi_pos v n = fourierCoeffOn Real.two_pi_pos P n :=
    mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))
      ((hcoeff n).symm.trans (hPc n))
  let f : ℝ → ℂ := fun t => v t - P t
  have hfc : ContinuousOn f (Icc 0 (2 * Real.pi)) := hv.continuousOn.sub hPC
  have hfe : f 0 = f (2 * Real.pi) := by
    dsimp only [f]
    rw [hP0, hPT, sub_zero, sub_zero]
    simpa only [zero_add] using (hvper 0).symm
  let F : ℝ → ℂ := fun t => AddCircle.liftIco (2 * Real.pi) 0 f
    (t : AddCircle (2 * Real.pi))
  have hFc : Continuous F :=
    (AddCircle.liftIco_zero_continuous hfe hfc).comp (AddCircle.continuous_mk' _)
  have hFp : Function.Periodic F (2 * Real.pi) := by
    intro t
    dsimp only [F]
    rw [AddCircle.coe_add_period]
  have hFf : EqOn F f (Icc 0 (2 * Real.pi)) := by
    intro t ht
    by_cases htT : t = 2 * Real.pi
    · subst t
      have hzero : AddCircle.liftIco (2 * Real.pi) 0 f
          (0 : AddCircle (2 * Real.pi)) = f 0 :=
        AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
      dsimp only [F]
      rw [AddCircle.coe_period, hzero, hfe]
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩
  have hcoeffF (n : ℤ) (hn : n ≠ 0) : fourierCoeffOn Real.two_pi_pos F n = 0 := by
    rw [fourierCoeffOn_congr_Icc hFf n]
    rw [fourierCoeffOn_sub_of_continuousOn hv.continuousOn hPC n, hncoeff n hn, sub_self]
  have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero hFc hFp hcoeffF θ
  rw [hFf hθ, hFf ⟨le_rfl, Real.two_pi_pos.le⟩] at hconst
  change v θ - P θ = v 0 - P 0 at hconst
  rw [hP0, sub_zero] at hconst
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hconst

/-- The actual L2 primitive reconstruction gives the genuine a.e.
derivative, including representatives of unbounded L2 loads. -/
theorem ae_hasDerivAt_of_L2_periodic_fourier_derivative
    {v : ℝ → ℂ} (hv : Continuous v)
    (hvper : Function.Periodic v (2 * Real.pi)) (d : BoundaryL2)
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos (d : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos v n) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt v (d θ) θ := by
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (intervalIntegrable_boundaryL2 d)] with θ hd hθ
  refine (((hasDerivAt_const θ (v 0)).add (hd hθ)).congr_deriv (zero_add _)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  exact eq_add_integral_of_L2_periodic_fourier_derivative hv hvper d hcoeff
    (Ioo_subset_Icc_self ht)

/-- Exact shift of the genuine Fourier Sobolev weights. -/
theorem isSobolevSeq_fromL2_shift_iff (s t : ℝ) (b : L2Z) :
    IsSobolevSeq (s + t) (fromL2 t b) ↔ IsSobolevSeq s (b : ℤ → ℂ) := by
  have he (n : ℤ) :
      (sobWeight n ^ (s + t) * ‖fromL2 t b n‖) ^ 2 =
        (sobWeight n ^ s * ‖b n‖) ^ 2 := by
    rw [fromL2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (sobWeight_pos n) (-t)),
      ← mul_assoc, ← Real.rpow_add (sobWeight_pos n)]
    rw [show (s + t) + -t = s by ring]
  simp only [IsSobolevSeq, he]

theorem isSobolevSeq_one_fromL2_half_of_half_regular (b : L2Z)
    (hb : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
  simpa only [show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num] using
    (isSobolevSeq_fromL2_shift_iff (1 / 2 : ℝ) (1 / 2 : ℝ) b).mpr hb

/-- The normalized conormal preserves true half-order regularity because
its difference from inclusion is the actual one-order smoothing map. -/
theorem normalizedConormal_preserves_half_regular
    {β a g : ℤ → ℂ} (hβ : IsWL1 (1 / 2 : ℝ) β)
    (ha : IsWL1 (1 / 2 : ℝ) a) (hg : IsWL1 (1 / 2 : ℝ) g)
    (E : ℂ) (b : L2Z) (hb : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ) (normalizedConormal hβ ha hg E b : ℤ → ℂ) := by
  have he := congrArg (fun A : L2Z →L[ℂ] L2Z => A b)
    (normalizedConormal_sub_one_eq hβ ha hg E)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply] at he
  have hr : IsSobolevSeq (1 / 2 : ℝ)
      (sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) : ℤ → ℂ) := by
    exact (sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (isSobolevSeq_fromL2 1 _)).1
  have hsum := isSobolevSeq_add hb hr
  have heq : normalizedConormal hβ ha hg E b =
      b + sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) := by
    rw [← he]
    abel
  rw [heq]
  simpa only [lp.coeFn_add] using hsum

/-- Variation of constants for actual ordinary L2 scalar forcing. The
inhomogeneous part is the genuine Duhamel construction. Uniqueness is
applied only to the homogeneous difference, whose forcing is zero. -/
theorem driven_eq_transport_add_physicalDrivenVector_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ)
    (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) {y : ℝ → Ell2} (hy : ContinuousOn y (Icc 0 (2 * Real.pi)))
    (hyint : ∀ θ ∈ Icc 0 (2 * Real.pi),
      y θ = y 0 + ∫ s in (0 : ℝ)..θ, transportCoeff γ E s (y s) +
        (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    y θ = W θ (y 0) + physicalDrivenVector W (g : ℝ → ℂ) θ := by
  let Y := physicalDrivenVector W (g : ℝ → ℂ)
  let f : ℝ → Ell2 := fun s => (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0
  have hg := intervalIntegrable_boundaryL2 g
  have hY := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1
    (g : ℝ → ℂ) hg
  have hC : Continuous (transportCoeff γ E) := by
    have hd := hγ.continuous_deriv_one
    have hc := Complex.continuous_conj.comp hd
    unfold transportCoeff
    fun_prop
  have hfi : IntegrableOn f (Icc 0 (2 * Real.pi)) := by
    have hgi : IntegrableOn (g : ℝ → ℂ) (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
    exact (hgi.const_mul (-(Complex.I / (Real.sqrt 2 : ℂ)))).smul_const _
  have hyi := ((hC.continuousOn.clm_apply hy).integrableOn_Icc).add hfi
  have hYi := ((hC.continuousOn.clm_apply hY).integrableOn_Icc).add hfi
  have hdiff (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
      (y t - Y t) = (y 0 - Y 0) + ∫ s in (0 : ℝ)..t,
        transportCoeff γ E s (y s - Y s) + (0 : Ell2) := by
    have hs : uIcc 0 t ⊆ Icc 0 (2 * Real.pi) := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hi1 : IntervalIntegrable (fun s => transportCoeff γ E s (y s) + f s)
        volume 0 t := by
      apply intervalIntegrable_iff.mpr
      apply MeasureTheory.IntegrableOn.mono_set hyi
      intro s hs'
      rw [uIoc_of_le ht.1] at hs'
      rw [uIcc_of_le ht.1] at hs
      exact hs ⟨hs'.1.le, hs'.2⟩
    have hi2 : IntervalIntegrable (fun s => transportCoeff γ E s (Y s) + f s)
        volume 0 t := by
      apply intervalIntegrable_iff.mpr
      apply MeasureTheory.IntegrableOn.mono_set hYi
      intro s hs'
      rw [uIoc_of_le ht.1] at hs'
      rw [uIcc_of_le ht.1] at hs
      exact hs ⟨hs'.1.le, hs'.2⟩
    dsimp only [Y]
    rw [hyint t ht, physicalDrivenVector_integral_eq_of_intervalIntegrable hγLip hγ hW
      (g : ℝ → ℂ) hg ht]
    simp only [physicalDrivenVector_zero, sub_zero]
    rw [show (fun s => transportCoeff γ E s (y s - Y s) + (0 : Ell2)) =
      fun s => (transportCoeff γ E s (y s) + f s) -
        (transportCoeff γ E s (Y s) + f s) by funext s; rw [map_sub]; abel,
      intervalIntegral.integral_sub hi1 hi2]
    abel
  have hd := driven_eq_transport hγLip hW
    (continuous_const.aestronglyMeasurable : AEStronglyMeasurable (fun _ : ℝ => (0 : Ell2)) volume)
    (B := 0) (fun _ => by simp) (hy.sub hY) hdiff θ hθ
  have heq : y θ - Y θ = W θ (y 0) := by
    simpa only [Y, physicalDrivenVector_zero, sub_zero, map_zero, Pi.sub_apply,
      intervalIntegral.integral_zero, add_zero] using hd
  simpa only [Y, add_comm] using sub_eq_iff_eq_add.mp heq

/-- The actual observation integral and Volterra trace agree for every
ordinary L2 input, including unbounded representatives. -/
theorem inner_transport_integral_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (g : BoundaryL2)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    ⟪basisVec 0, W θ (∫ s in (0 : ℝ)..θ,
      g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))⟫_ℂ =
        volterraOp W (g : ℝ → ℂ) θ := by
  have hi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      volume 0 θ := by
    apply intervalIntegrable_iff.mpr
    apply MeasureTheory.IntegrableOn.mono_set
      (integrable_boundary_observation_load hγLip hW g)
    rw [uIoc_of_le hθ.1]
    exact Ioc_subset_Ioc le_rfl hθ.2
  have h := ((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
  rw [← h, volterraOp]
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [map_smul, inner_smul_right, volterraKernel]
  ring

/-- The true Volterra plus adjoint identity holds for ordinary L2 inputs. -/
theorem volterraOp_add_adj_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (g : BoundaryL2)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    volterraOp W (g : ℝ → ℂ) θ + volterraOpAdj W (g : ℝ → ℂ) θ =
      observation W (observationAdj W (g : ℝ → ℂ)) θ := by
  have hk (s : ℝ) : conj (volterraKernel W s θ) = volterraKernel W θ s := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have hkc : ContinuousOn (fun s => volterraKernel W θ s) (Icc 0 (2 * Real.pi)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hg := intervalIntegrable_boundaryL2 g
  have hint : IntervalIntegrable (fun s => volterraKernel W θ s * g s)
      volume 0 (2 * Real.pi) := by
    exact hg.continuousOn_mul
      (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hkc)
  have hi0 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume 0 θ :=
    hint.mono_set' (by simp only [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le]
                       exact Ioc_subset_Ioc le_rfl hθ.2)
  have hi1 : IntervalIntegrable (fun s => volterraKernel W θ s * g s)
      volume θ (2 * Real.pi) :=
    hint.mono_set' (by simp only [uIoc_of_le hθ.2, uIoc_of_le Real.two_pi_pos.le]
                       exact Ioc_subset_Ioc hθ.1 le_rfl)
  simp only [volterraOp, volterraOpAdj, hk]
  rw [intervalIntegral.integral_add_adjacent_intervals hi0 hi1, observation, observationAdj]
  have hi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      volume 0 (2 * Real.pi) :=
    by
      apply intervalIntegrable_iff.mpr
      simpa only [IntegrableOn, uIoc_of_le Real.two_pi_pos.le] using
        (integrable_boundary_observation_load hγLip hW g)
  have h := ((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [map_smul, inner_smul_right, volterraKernel]
  ring

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

local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "UR" => localConformalVekuaTraceRow hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "YF" => localConformalVekuaTransportVector hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

/-- The ordinary coordinate load exists here as a conclusion of genuine
half-order input regularity and the proved normalized smoothing formula. -/
def localConformalVekuaForwardLoad (E : ℂ) (b : L2Z)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) : BoundaryL2 :=
  halfRegularCoordinateLoad (NF E b)
    (normalizedConormal_preserves_half_regular hβF haF hgF E b hbhalf)

theorem localConformalVekuaForwardLoad_normalized (E : ℂ) (b : L2Z)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
      (boundaryFourier (localConformalVekuaForwardLoad hR F hFs E b hbhalf)) = NF E b :=
  halfRegularCoordinateLoad_normalized _ _

private theorem forward_fourier_coeff_ae {f : ℝ → ℂ} (v : BoundaryL2)
    (hv : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f) (n : ℤ) :
    boundaryFourier v n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

/-- Actual Fourier inversion of the exceptional zeroth row with its
genuine coordinate L2 conormal forcing. The zeroth coefficient is used. -/
theorem localConformalVekuaForward_zero_fourier_derivative
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos
      (((2 * (-E / 4)) •
        boundaryContinuousMultiplier (localConformalVelocityCircle F)
          (TF (VF (F 1) E (JF b))) -
        Complex.I • localConformalVekuaForwardLoad hR F hFs E b hbhalf : BoundaryL2) : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos (UR E b 0) n := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let G : BoundaryL2 := boundaryContinuousMultiplier (localConformalVelocityCircle F)
    (TF (VF (F 1) E (JF b)))
  let g := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  let L : BoundaryL2 := (2 * (-E / 4)) • G - Complex.I • g
  have ht0 : (TF (VF (F 1) E b) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] UR E b 0 := by
    unfold localConformalVekuaTraceRow
    simpa only [pow_zero, ContinuousLinearMap.one_apply] using
      localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1
  have hNC := localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1 n
  have hload := congrArg (fun v : L2Z => v n)
    (localConformalVekuaForwardLoad_normalized hR F hFs E b hbhalf)
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boundaryFourier g n = NF E b n at hload
  simp only [localConformalVekuaGradientA_apply, map_smul, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul] at hNC
  have hw : (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-(1 / 2 : ℝ))).ne'
  have hn : -(n : ℂ) * boundaryFourier (TF (VF (F 1) E b)) n -
      2 * Complex.I * ((-E / 4) * boundaryFourier G n) = boundaryFourier g n :=
    mul_left_cancel₀ hw (hNC.symm.trans hload.symm)
  have hs0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  apply mul_left_cancel₀ hs0
  calc
    _ = boundaryFourier L n := (boundaryFourier_apply L n).symm
    _ = (Complex.I * (n : ℂ)) * boundaryFourier (TF (VF (F 1) E b)) n := by
      simp only [L, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [← hn]
      ring_nf
      simp [Complex.I_sq]
    _ = _ := by rw [forward_fourier_coeff_ae _ ht0]; ring

private theorem forward_zero_derivative_ae
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    (((2 * (-E / 4)) •
      boundaryContinuousMultiplier (localConformalVelocityCircle F)
        (TF (VF (F 1) E (JF b))) -
      Complex.I • localConformalVekuaForwardLoad hR F hFs E b hbhalf : BoundaryL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        fun t => 2 * (-E / 4) * deriv (physicalCircleTrace F) t * UR E b 1 t -
          Complex.I * localConformalVekuaForwardLoad hR F hFs E b hbhalf t := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let G : BoundaryL2 := boundaryContinuousMultiplier (localConformalVelocityCircle F)
    (TF (VF (F 1) E (JF b)))
  let g := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  have hJbn := localConformalHardyPrimitive_nonpositive hR F hFs hhol b hbn
  have hJ1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) (JF b)) := by
    simpa only [pow_one] using localConformalHardyPrimitive_pow_raw_H1 hR F hFs b hb1 1
  have ht1 := localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol
    hinj hC hK e he hsource hes E (JF b) hJbn hJ1
  filter_upwards [Lp.coeFn_sub ((2 * (-E / 4)) • G) (Complex.I • g),
    Lp.coeFn_smul (2 * (-E / 4)) G, Lp.coeFn_smul Complex.I g,
    boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
      (TF (VF (F 1) E (JF b))), ht1] with t hsub hs ht hG htrace
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hs, ht]
  simp only [Pi.smul_apply, smul_eq_mul, G, g, hG, htrace,
    localConformalVelocityCircle_apply hR F hFs, localConformalVekuaTraceRow, pow_one]
  ring

/-- The exceptional zero row has its true inhomogeneous primitive
formula, with the actual initial constant and ordinary L2 coordinate load. -/
theorem localConformalVekuaForward_zero_integral_eq
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    UR E b 0 θ = UR E b 0 0 + ∫ t in (0 : ℝ)..θ,
      2 * (-E / 4) * deriv (physicalCircleTrace F) t * UR E b 1 t -
        Complex.I * localConformalVekuaForwardLoad hR F hFs E b hbhalf t := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let L : BoundaryL2 := (2 * (-E / 4)) •
    boundaryContinuousMultiplier (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))) -
      Complex.I • localConformalVekuaForwardLoad hR F hFs E b hbhalf
  have hprimitive := eq_add_integral_of_L2_periodic_fourier_derivative
    (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 0)
    (localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b 0) L
    (localConformalVekuaForward_zero_fourier_derivative hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hbhalf) hθ
  rw [hprimitive]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hAE := (ae_restrict_iff' measurableSet_Ioc).mp
    (forward_zero_derivative_ae hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hbhalf)
  filter_upwards [hAE] with t ht hmem
  rw [uIoc_of_le hθ.1] at hmem
  exact ht ⟨hmem.1, hmem.2.trans hθ.2⟩

/-- The actual zero row is a.e. differentiable with the genuine L2 load.
No differentiability or boundedness of that load is an input. -/
theorem localConformalVekuaForward_zero_ae_hasDerivAt
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (UR E b 0)
        (2 * (-E / 4) * deriv (physicalCircleTrace F) θ * UR E b 1 θ -
          Complex.I * localConformalVekuaForwardLoad hR F hFs E b hbhalf θ) θ := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let L : BoundaryL2 := (2 * (-E / 4)) •
    boundaryContinuousMultiplier (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))) -
      Complex.I • localConformalVekuaForwardLoad hR F hFs E b hbhalf
  have hd := ae_hasDerivAt_of_L2_periodic_fourier_derivative
    (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 0)
    (localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b 0) L
    (localConformalVekuaForward_zero_fourier_derivative hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hbhalf)
  have hAE := (ae_restrict_iff' measurableSet_Ioc).mp
    (forward_zero_derivative_ae hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hbhalf)
  filter_upwards [hd, hAE] with θ hD hL hθ
  exact (hD hθ).congr_deriv (hL ⟨hθ.1, hθ.2.le⟩)

private theorem forward_zero_transportCoeff
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    (2 * (-(E : ℂ) / 4) * deriv (physicalCircleTrace F) θ * UR (E : ℂ) b 1 θ) /
        (Real.sqrt 2 : ℂ) =
      (transportCoeff (physicalCircleTrace F) E θ (YF E b θ) : ℕ → ℂ) 0 := by
  rw [transportCoeff_coord_zero,
    localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hθ 1]
  simp only [localConformalVekuaTransportCoordinate, if_false, Nat.one_ne_zero, pow_one]
  change _ = physicalDrivenQ E * _
  rw [← physicalDrivenQ_sq hE]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hs0]
  linear_combination -(physicalDrivenQ E ^ 2 * deriv (physicalCircleTrace F) θ *
    UR (E : ℂ) b 1 θ) * hs

/-- The full actual Ell2 trace vector obeys the driven integral equation.
Positive rows come from the genuine factorial series; only the exceptional
zeroth row uses the actual L2 primitive inversion. -/
theorem localConformalVekuaForward_transport_integral_eq
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    YF E b θ = YF E b 0 + ∫ s in (0 : ℝ)..θ,
      transportCoeff (physicalCircleTrace F) E s (YF E b s) +
        (-(Complex.I / (Real.sqrt 2 : ℂ)) *
          localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf s) • basisVec 0 := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let y := YF E b
  let p := localConformalVekuaPositiveTransportVector hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b
  let z : ℝ → ℂ := fun s => UR (E : ℂ) b 0 s / (Real.sqrt 2 : ℂ)
  let g := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  let Cg := fun s => transportCoeff (physicalCircleTrace F) E s (y s)
  let a : ℝ → ℂ := fun s =>
    (2 * (-(E : ℂ) / 4) * deriv (physicalCircleTrace F) s * UR (E : ℂ) b 1 s -
      Complex.I * g s) / (Real.sqrt 2 : ℂ)
  have hy := localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1
  have hΓ : ContDiff ℝ 1 (physicalCircleTrace F) :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hCoeff : Continuous (transportCoeff (physicalCircleTrace F) E) := by
    have hd := hΓ.continuous_deriv_one
    have hc := Complex.continuous_conj.comp hd
    unfold transportCoeff
    fun_prop
  have hCg : ContinuousOn Cg (Icc 0 (2 * Real.pi)) := hCoeff.continuousOn.clm_apply hy
  have hC0 : ContinuousOn (fun s => (Cg s : ℕ → ℂ) 0) (Icc 0 (2 * Real.pi)) := by
    have h := (innerSL ℂ (basisVec 0)).continuous.continuousOn.comp hCg
      (fun _ _ => Set.mem_univ _)
    convert h using 1
    · funext s
      simp only [Function.comp_apply, innerSL_apply_apply, inner_basisVec]
  have hpd : ContinuousOn (fun s => Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0)
      (Icc 0 (2 * Real.pi)) := hCg.sub (hC0.smul continuousOn_const)
  have hz : Continuous z :=
    (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
      e he hsource hes (E : ℂ) b hbn hb1 0).div_const _
  have hsplit (s : ℝ) (hs : s ∈ Icc 0 (2 * Real.pi)) : y s = z s • basisVec 0 + p s :=
    localConformalVekuaTransportVector_zero_add_positive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hs
  have hp : ContinuousOn p (Icc 0 (2 * Real.pi)) := by
    apply (hy.sub (hz.continuousOn.smul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => basisVec 0)
        (Icc 0 (2 * Real.pi))))).congr
    intro s hs
    change p s = y s - z s • basisVec 0
    rw [hsplit s hs]
    abel
  have hsub : Icc 0 θ ⊆ Icc 0 (2 * Real.pi) := Icc_subset_Icc le_rfl hθ.2
  have hpi : IntervalIntegrable (fun s => Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0)
      volume 0 θ := by
    exact (hpd.mono (by simpa only [uIcc_of_le hθ.1] using hsub)).intervalIntegrable
  have hip := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 (hp.mono hsub)
    (fun s hs => (localConformalVekuaPositiveTransportVector_hasDerivAt hR F hFs hb hL
      hhol hinj hC hK e he hsource hes E b hbn hb1 ⟨hs.1, hs.2.trans_le hθ.2⟩).congr_deriv (localConformalVekuaPositiveTransportDerivative_tsum_eq hR F hFs hb hL
        hhol hinj hC hK e he hsource hes E hE b hbn hb1 ⟨hs.1.le, hs.2.le.trans hθ.2⟩)) hpi
  have hzp : z θ = z 0 + ∫ s in (0 : ℝ)..θ, a s := by
    have h := congrArg (fun v : ℂ => v / (Real.sqrt 2 : ℂ))
      (localConformalVekuaForward_zero_integral_eq hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (E : ℂ) b hbn hbhalf hθ)
    simpa only [z, a, g, add_div, intervalIntegral.integral_div] using h
  have hac : Continuous (fun s => 2 * (-(E : ℂ) / 4) * deriv (physicalCircleTrace F) s *
      UR (E : ℂ) b 1 s) := (continuous_const.mul hΓ.continuous_deriv_one).mul
        (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
          e he hsource hes (E : ℂ) b hbn hb1 1)
  have hgi : IntervalIntegrable (g : ℝ → ℂ) volume 0 θ :=
    (intervalIntegrable_boundaryL2 g).mono_set' (by
      simp only [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le]
      exact Ioc_subset_Ioc le_rfl hθ.2)
  have hai : IntervalIntegrable a volume 0 θ :=
    ((hac.intervalIntegrable 0 θ).sub (hgi.const_mul Complex.I)).div_const _
  calc
    y θ = z θ • basisVec 0 + p θ := hsplit θ hθ
    _ = (z 0 • basisVec 0 + p 0) +
        ((∫ s in (0 : ℝ)..θ, a s) • basisVec 0 +
          ∫ s in (0 : ℝ)..θ, Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0) := by
      rw [hzp, sub_eq_iff_eq_add.mp hip.symm, add_smul]
      abel
    _ = y 0 + ∫ s in (0 : ℝ)..θ,
        (a s • basisVec 0 + (Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0)) := by
      have hai' : IntervalIntegrable (fun s => a s • basisVec 0)
          volume 0 θ := by
        exact ⟨MeasureTheory.Integrable.smul_const hai.1 _,
          MeasureTheory.Integrable.smul_const hai.2 _⟩
      rw [← hsplit 0 ⟨le_rfl, Real.two_pi_pos.le⟩,
        ← intervalIntegral.integral_smul_const,
        ← intervalIntegral.integral_add hai' hpi]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hθ.1] at hs
      have hsc : s ∈ Icc 0 (2 * Real.pi) := ⟨hs.1, hs.2.trans hθ.2⟩
      have hzero := forward_zero_transportCoeff hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E hE b hbn hb1 hsc
      have haeq : a s = (Cg s : ℕ → ℂ) 0 - (Complex.I / (Real.sqrt 2 : ℂ)) * g s := by
        dsimp only [a]
        rw [sub_div, hzero]
        ring
      change a s • basisVec 0 + (Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0) =
        Cg s + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0
      rw [haeq, sub_smul]
      simp only [neg_mul, neg_smul]
      abel

/-- The actual forward vector equals genuine homogeneous transport plus
the true L2 Duhamel vector. No forced ODE is assumed. -/
theorem localConformalVekuaForward_transport_eq
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    YF E b θ = W θ (YF E b 0) +
      physicalDrivenVector W (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  exact driven_eq_transport_add_physicalDrivenVector_boundaryL2 hΓLip
    (contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))) hW
    (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf)
    (localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1)
    (fun t ht => localConformalVekuaForward_transport_integral_eq hR F hFs hb hL hhol
      hinj hC hK e he hsource hes E hE b hbn hbhalf ht) hθ

include hb hL hhol hinj hC hK e he hsource hes in
/-- The periodic endpoint of the actual trace vector determines its true
adjoint observation, with the original initial constant and sqrt(2) scale. -/
theorem localConformalVekuaForward_observationAdj_eq_cut
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W) :
    observationAdj W
      (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf : ℝ → ℂ) =
        (Complex.I * hardyFourierTrace (normalizedHardyAverage b) 0) •
          cutC (W (2 * Real.pi)) (basisVec 0) := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let y := YF E b
  let g := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  let s := h0 / (Real.sqrt 2 : ℂ)
  have hinit : y 0 = s • basisVec 0 :=
    localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1
  have hper : y (2 * Real.pi) = y 0 := by
    simpa only [zero_add] using localConformalVekuaTransportVector_periodic hR F hFs
      hb hL hhol hinj hC hK e he hsource hes E b 0
  have hT : (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaForward_transport_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW hT
  change y (2 * Real.pi) = W (2 * Real.pi) (y 0) +
    (-(Complex.I / (Real.sqrt 2 : ℂ))) • W (2 * Real.pi)
      (observationAdj W (g : ℝ → ℂ)) at hform
  rw [hper] at hform
  have hu : ContinuousLinearMap.adjoint (W (2 * Real.pi)) * W (2 * Real.pi) = 1 := by
    have hm := transport_mem_unitary hΓLip hW hT
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hm
    exact hm.1
  have hadj := congrArg (fun z : Ell2 => ContinuousLinearMap.adjoint (W (2 * Real.pi)) z) hform
  change ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) =
    ContinuousLinearMap.adjoint (W (2 * Real.pi))
      (W (2 * Real.pi) (y 0) +
        (-(Complex.I / (Real.sqrt 2 : ℂ))) •
          W (2 * Real.pi) (observationAdj W (g : ℝ → ℂ))) at hadj
  rw [map_add, map_smul, ← ContinuousLinearMap.mul_apply, hu,
    ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hu,
    ContinuousLinearMap.one_apply] at hadj
  have hsub : ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0 =
      (-(Complex.I / (Real.sqrt 2 : ℂ))) • observationAdj W (g : ℝ → ℂ) := by
    rw [hadj]
    abel
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hcancel : (Real.sqrt 2 : ℂ) * Complex.I * -(Complex.I / (Real.sqrt 2 : ℂ)) = 1 := by
    field_simp [hs0] ; simp [Complex.I_sq]
  have hO : observationAdj W (g : ℝ → ℂ) = ((Real.sqrt 2 : ℂ) * Complex.I) •
      (ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0) := by
    rw [hsub, smul_smul, hcancel, one_smul]
  rw [hO, hinit, map_smul, ← smul_sub, smul_smul]
  have hscalar : ((Real.sqrt 2 : ℂ) * Complex.I) * s = Complex.I * h0 := by
    dsimp only [s]
    field_simp [hs0]
  simp only [hscalar, h0, cutC]

include hb hL hhol hinj hC hK e he hsource hes in
/-- The projected observation annihilates the genuine normalized conormal
range on every half-regular full Hardy input, including frequency zero. -/
theorem localConformalVekuaForward_projObsDual_eq_zero_of_half_regular
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W) :
    projObsDual W (NF (E : ℂ) b) = 0 := by
  have h := projObsDual_boundary_normalized hΓLip hW
    (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf)
  rw [localConformalVekuaForwardLoad_normalized, map_smul,
    localConformalVekuaForward_observationAdj_eq_cut hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hbhalf hΓLip hW,
    map_smul, cutProj_eq_starProjection,
    Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_span_singleton_self _),
    smul_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')

/-- The actual coordinate trace obeys the true forward observation and
Volterra identity for its derived ordinary L2 conormal load. -/
theorem localConformalVekuaForward_trace_eq
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    UR (E : ℂ) b 0 θ = hardyFourierTrace (normalizedHardyAverage b) 0 *
      observation W (basisVec 0) θ - Complex.I *
        volterraOp W (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let g := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  have hform := localConformalVekuaForward_transport_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW hθ
  have hinner := congrArg (fun v : Ell2 => ⟪basisVec 0, v⟫_ℂ) hform
  simp only [inner_add_right] at hinner
  have hleft : ⟪basisVec 0, YF E b θ⟫_ℂ = UR (E : ℂ) b 0 θ / (Real.sqrt 2 : ℂ) := by
    simpa only [inner_basisVec, localConformalVekuaTransportCoordinate, if_true] using
      localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1 hθ 0
  have hinit : ⟪basisVec 0, W θ (YF E b 0)⟫_ℂ =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / (Real.sqrt 2 : ℂ)) *
        observation W (basisVec 0) θ := by
    change ⟪basisVec 0, W θ (YF E b 0)⟫_ℂ =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / (Real.sqrt 2 : ℂ)) *
        ⟪basisVec 0, W θ (basisVec 0)⟫_ℂ
    rw [localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1, map_smul, inner_smul_right]
  have hforced : ⟪basisVec 0, physicalDrivenVector W (g : ℝ → ℂ) θ⟫_ℂ =
      -(Complex.I / (Real.sqrt 2 : ℂ)) * volterraOp W (g : ℝ → ℂ) θ := by
    rw [physicalDrivenVector, inner_smul_right, inner_transport_integral_boundaryL2 hΓLip hW g hθ]
  rw [hleft, hinit, hforced] at hinner
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  apply (div_left_inj' hs0).mp
  rw [hinner]
  dsimp only [g]
  ring

/-- The genuine periodic form vanishes on the actual forward Vekua trace
and its actual L2 load. A nonzero cut is used only by the correction B. -/
theorem localConformalVekuaForward_periodicP_eq_zero
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    periodicP W (UR (E : ℂ) b 0)
      (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf : ℝ → ℂ) θ = 0 := by
  let g := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  have hsum := volterraOp_add_adj_boundaryL2 hΓLip hW g hθ
  have hO := localConformalVekuaForward_observationAdj_eq_cut hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW
  change observationAdj W (g : ℝ → ℂ) = (Complex.I * h0) •
    cutC (W (2 * Real.pi)) (basisVec 0) at hO
  have hS : cutS (W (2 * Real.pi)) (basisVec 0) =
      (2 : ℂ) • basisVec 0 + cutC (W (2 * Real.pi)) (basisVec 0) := by
    simp only [cutS, cutC]
    rw [two_smul]
    abel
  have hA : periodicA W (UR (E : ℂ) b 0) (g : ℝ → ℂ) θ =
      h0 * observation W (cutS (W (2 * Real.pi)) (basisVec 0)) θ := by
    rw [hO] at hsum
    rw [periodicA, localConformalVekuaForward_trace_eq hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hbhalf hΓLip hW hθ, hS]
    simp only [observation, map_add, map_smul, inner_add_right, inner_smul_right] at hsum ⊢
    linear_combination (-Complex.I) * hsum - Complex.I_sq *
      (h0 * ⟪basisVec 0, W θ (cutC (W (2 * Real.pi)) (basisVec 0))⟫_ℂ)
  have hBc := (cutB_transport (transport_mem_unitary hΓLip hW
    ⟨Real.two_pi_pos.le, le_rfl⟩) (basisVec 0) hc).2
  rw [periodicP, hA, hO, map_smul, hBc, smul_smul]
  simp only [observation, map_smul, inner_smul_right]
  linear_combination Complex.I_sq *
    (h0 * ⟪basisVec 0, W θ (cutS (W (2 * Real.pi)) (basisVec 0))⟫_ℂ)

private theorem forward_half_regular_stdBasis (n : ℤ) :
    IsSobolevSeq (1 / 2 : ℝ) (stdBasisZ n : ℤ → ℂ) := by
  apply summable_of_ne_finset_zero (s := {n})
  intro k hk
  have hkn : k ≠ n := by simpa only [Finset.mem_singleton] using hk
  simp [stdBasisZ_apply, lp.single_apply, hkn]

include hb hL hhol hinj hC hK e he hsource hes in
/-- Genuine finite Fourier density extends the bounded projected-null
identity to every normalized full Hardy input. No L2 load for those
possibly rough inputs is asserted by this extension. -/
theorem localConformalVekuaForward_projObsDual_eq_zero
    (E : ℝ) (hE : 0 ≤ E)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    projObsDual W (NF (E : ℂ) b) = 0 := by
  have hop : (projObsDual W).comp ((NF (E : ℂ)).comp (1 - posProj)) = 0 := by
    apply ContinuousLinearMap.ext_on
      ((Submodule.dense_iff_topologicalClosure_eq_top).2 stdBasisZ.dense_span)
    rintro _ ⟨n, rfl⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    by_cases hn : 0 < n
    · have hzero : (1 - posProj) (stdBasisZ n) = 0 := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        · subst k
          simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
            posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hn]
        · simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
            posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hzero, map_zero, map_zero]
    · have hkeep : (1 - posProj) (stdBasisZ n) = stdBasisZ n := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        · subst k
          simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
            posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hn]
        · simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
            posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hkeep]
      apply localConformalVekuaForward_projObsDual_eq_zero_of_half_regular hR F hFs hb hL
        hhol hinj hC hK e he hsource hes E hE (stdBasisZ n) _
        (forward_half_regular_stdBasis n) hΓLip hW
      intro k hk
      have hkn : k ≠ n := by omega
      simp [stdBasisZ_apply, lp.single_apply, hkn]
  have hkeep : (1 - posProj) b = b := by
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        posProj, diagOp_apply, hn, hbn n hn]
    · simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        posProj, diagOp_apply, hn]
  have h := congrArg (fun A : L2Z →L[ℂ] Ell2 => A b) hop
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hkeep] using h

include hb hL hhol hinj hC hK e he hsource hes in
/-- The same bounded null identity is an exact operator statement on the
original closed Hardy space, whose zero frequency is retained. -/
theorem localConformalVekuaForward_projObsDual_comp_eq_zero
    (E : ℝ) (hE : 0 ≤ E)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W) :
    (projObsDual W).comp ((NF (E : ℂ)).comp nonpositiveFourierSubspace.starProjection) = 0 := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  apply localConformalVekuaForward_projObsDual_eq_zero hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE hΓLip hW
  rw [nonpositiveFourierSubspace_starProjection]
  exact one_sub_posProj_mem_nonpositive b

end PhysicalCoordinates

end PolyaNeumann

end
