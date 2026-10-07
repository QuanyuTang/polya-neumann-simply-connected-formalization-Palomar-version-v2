module

public import RequestProject.NormalizedPeriodicBoundary
public import RequestProject.LocalConformalRegularObservation
public import RequestProject.LocalConformalVekuaForward
public import RequestProject.LocalConformalVekuaConormalBridge

/-!
# The genuine full periodic family on the actual Vekua conormal range

At a nonresonant energy the actual Vekua weak equation identifies its
vector with the original normalized Neumann Poisson solution. The
ordinary L2 periodic expression agrees with the normalized Fourier
operator, including the constant mode. Finite Fourier density then
extends its proved vanishing to every original Hardy input.

The supplied physical boundary parametrization and its genuine C1
arclength coordinate are retained. No L2 representative is asserted for
an arbitrary normalized rough load. This source awaits root compilation.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real
open scoped Topology InnerProductSpace ComplexConjugate

local instance periodicNullTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

private theorem periodic_null_halfSmoothing_injective :
    Function.Injective (sobolevSmoothing (1 / 2 : ℝ) (by norm_num) : L2Z →L[ℂ] L2Z) := by
  intro f g h
  apply lp.ext
  funext n
  have hn := congrArg (fun v : L2Z => v n) h
  simp only [sobolevSmoothing, diagOp_apply] at hn
  have hw : (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) _).ne'
  exact mul_left_cancel₀ hw hn

/-- The actual circle kernel action on a genuine boundary L2 lift is its
ordinary interval integral, without a pointwise bound on the load. -/
theorem kernelL2Action_boundaryCircleLift {r : ℝ → ℝ → ℂ} {M : ℝ}
    (hmeas : ∀ θ, Measurable (r θ)) (hbd : ∀ θ s, ‖r θ s‖ ≤ M)
    (g : BoundaryL2) (θ : ℝ) :
    kernelL2Action hmeas hbd (boundaryCircleLift g) θ =
      ∫ s in (0 : ℝ)..(2 * Real.pi), r θ s * g s := by
  rw [kernelL2Action_eq_haar_integral]
  have he : (fun x : AddCircle (2 * Real.pi) =>
      r θ (circRep x) * boundaryCircleLift g x) =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIco (2 * Real.pi) 0 (fun s => r θ s * g s) := by
    filter_upwards [boundaryCircleLift_coe g,
      boundary_liftIoc_eq_liftIco_ae (g : ℝ → ℂ)] with x hx hrep
    rw [hx, hrep, liftIco_eq_comp, liftIco_eq_comp]
  rw [integral_congr_ae he]
  exact two_pi_mul_integral_liftIco _

/-- All L2 inputs, including unbounded representatives, have the actual
corrected-kernel Fourier action. This follows from the genuine circle
kernel operator and its true representative, not a density premise. -/
theorem regularCorrectedBoundaryOperator_fourier_integral_L2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0)
    (g : BoundaryL2) (n : ℤ) :
    boundaryFourier (regularCorrectedBoundaryOperator hγLip hW hc g) n =
      (Real.sqrt (2 * Real.pi) : ℂ) * fourierCoeffOn Real.two_pi_pos
        (fun θ => ∫ s in (0 : ℝ)..(2 * Real.pi), correctedKernel W θ s * g s) n := by
  change (fourierBasis (T := 2 * Real.pi)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hγLip hW hc (boundaryCircleUnitary g)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (fourierBasis (T := 2 * Real.pi)).repr
    (correctedKernelL2Op hγLip hW hc
      ((Real.sqrt (2 * Real.pi) : ℂ) • boundaryCircleLift g)) n = _
  rw [map_smul, map_smul]
  change (Real.sqrt (2 * Real.pi) : ℂ) *
    (fourierBasis (T := 2 * Real.pi)).repr
      (correctedKernelL2Op hγLip hW hc (boundaryCircleLift g)) n = _
  congr 1
  rw [fourierBasis_repr]
  change fourierCoeff ((memLp_kernelL2Action (measurable_ckPer hW)
    (norm_ckPer_le hγLip hW) (fun θ θ' s _ => ckPer_lip hγLip hW hc θ θ' s)
      (boundaryCircleLift g)).toLp _) n = _
  rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp
    (memLp_kernelL2Action (measurable_ckPer hW) (norm_ckPer_le hγLip hW)
      (fun θ θ' s _ => ckPer_lip hγLip hW hc θ θ' s) (boundaryCircleLift g))),
    fourierCoeff_liftIco_two_pi]
  refine congrFun (fourierCoeffOn_congr_ae Real.two_pi_pos ?_) n
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  rw [kernelL2Action_boundaryCircleLift
    (r := ckPer W) (M := 4 + ‖cutBE W‖)
    (measurable_ckPer hW) (norm_ckPer_le hγLip hW) g θ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le Real.two_pi_pos.le] at hs
  change ckPer W θ s * g s = correctedKernel W θ s * g s
  rw [ckPer_eq hγLip hW hc (Ioc_subset_Icc_self hθ) hs]

theorem regularCorrectedBoundaryOperator_eq_integral_L2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) (g : BoundaryL2) :
    regularCorrectedBoundaryOperator hγLip hW hc g =
      (memLp_regularCorrectedAction hγLip hW
        ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2))).toLp _ := by
  apply boundaryFourier.injective
  apply lp.ext
  funext n
  rw [regularCorrectedBoundaryOperator_fourier_integral_L2 hγLip hW hc g n,
    boundaryFourier_apply]
  congr 1
  exact (congrFun (fourierCoeffOn_congr_ae Real.two_pi_pos
    (MemLp.coeFn_toLp (memLp_regularCorrectedAction hγLip hW
      ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2))))) n).symm

private theorem periodic_null_continuous_row_intervalIntegrable
    {a : ℝ → ℂ} (ha : ContinuousOn a (Icc 0 (2 * Real.pi)))
    (g : BoundaryL2) {s t : ℝ} (hs : s ∈ Icc 0 (2 * Real.pi))
    (ht : t ∈ Icc 0 (2 * Real.pi)) :
    IntervalIntegrable (fun x => a x * g x) volume s t := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have hi : Integrable (fun x => a x * g x) μB := by
    apply ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)).bdd_mul (c := B)
      ((ha.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
      hB x (Ioc_subset_Icc_self hx)
  apply IntervalIntegrable.mono_set'
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr hi)
  exact uIoc_subset_uIoc_of_uIcc_subset_uIcc (by
    rw [uIcc_of_le Real.two_pi_pos.le]
    exact uIcc_subset_Icc hs ht)

/- The original kernel decomposition is valid on actual L2 loads. Its
proof uses integrable continuous rows and the true observation integral;
it never inserts a bounded representative of the load. -/
theorem periodicP_eq_kernel_integrals_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (t : ℝ → ℂ) (g : BoundaryL2) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    periodicP W t (g : ℝ → ℂ) θ = 2 * t θ +
      (∫ s in (0 : ℝ)..(2 * Real.pi), sawtoothKernel θ s * g s) +
      (∫ s in (0 : ℝ)..(2 * Real.pi), correctedKernel W θ s * g s) := by
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * Real.pi) := ⟨le_rfl, Real.two_pi_pos.le⟩
  have hT : (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hwc : ContinuousOn (fun s => volterraKernel W θ s) (Icc 0 (2 * Real.pi)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hwi : ∀ {s t : ℝ}, s ∈ Icc 0 (2 * Real.pi) → t ∈ Icc 0 (2 * Real.pi) →
      IntervalIntegrable (fun x => volterraKernel W θ x * g x) volume s t :=
    fun hs ht => periodic_null_continuous_row_intervalIntegrable hwc g hs ht
  have hk (s : ℝ) : conj (volterraKernel W s θ) = volterraKernel W θ s := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have hv : Complex.I * (volterraOp W (g : ℝ → ℂ) θ -
      volterraOpAdj W (g : ℝ → ℂ) θ) =
      ∫ s in (0 : ℝ)..(2 * Real.pi), Complex.I *
        ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_sign_mul_of_integrable hθ (hwi h0 hθ) (hwi hθ hT)]
    simp only [volterraOp, volterraOpAdj, hk]
  have hbi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
      (integrable_boundary_observation_load hγLip hW g)
  let A : Ell2 →L[ℂ] ℂ := (innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))
  have hobs := A.intervalIntegral_comp_comm hbi
  simp only [A, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    map_smul, smul_eq_mul] at hobs
  have ho : observation W (cutBE W (observationAdj W (g : ℝ → ℂ))) θ =
      ∫ s in (0 : ℝ)..(2 * Real.pi),
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
    rw [observation, observationAdj, ← hobs]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hs : IntervalIntegrable (fun s =>
      Complex.I * ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)))
      volume 0 (2 * Real.pi) :=
    (intervalIntegrable_sign_mul_of_integrable hθ (hwi h0 hθ) (hwi hθ hT)).const_mul _
  have hoc : ContinuousOn (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ)
      (Icc 0 (2 * Real.pi)) :=
    ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hoi := periodic_null_continuous_row_intervalIntegrable hoc g h0 hT
  have hgi : ∀ {s t : ℝ}, s ∈ Icc 0 (2 * Real.pi) → t ∈ Icc 0 (2 * Real.pi) →
      IntervalIntegrable (fun x => (1 : ℂ) * g x) volume s t :=
    fun hs ht => periodic_null_continuous_row_intervalIntegrable
      (continuousOn_const (c := (1 : ℂ))) g hs ht
  have hsign : IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ) * g s)
      volume 0 (2 * Real.pi) := by
    apply intervalIntegrable_sign_mul_of_integrable hθ
    · simpa only [one_mul] using hgi h0 hθ
    · simpa only [one_mul] using hgi hθ hT
  have hlin : IntervalIntegrable (fun s => (((θ - s) / Real.pi : ℝ) : ℂ) * g s)
      volume 0 (2 * Real.pi) :=
    periodic_null_continuous_row_intervalIntegrable
      (by fun_prop) g h0 hT
  have hsaw : IntervalIntegrable (fun s => sawtoothKernel θ s * g s)
      volume 0 (2 * Real.pi) := by
    refine ((hsign.const_mul Complex.I).sub (hlin.const_mul Complex.I)).congr fun s _ => ?_
    simp only [sawtoothKernel]
    push_cast
    ring
  have hcorr : IntervalIntegrable (fun s => correctedKernel W θ s * g s)
      volume 0 (2 * Real.pi) := by
    refine ((hs.add hoi).sub hsaw).congr fun s _ => ?_
    have he := sawtoothKernel_add_correctedKernel (W := W) θ s
    calc
      _ = (Complex.I * (Real.sign (θ - s) : ℂ) * volterraKernel W θ s +
          ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ) * g s -
          sawtoothKernel θ s * g s := by ring
      _ = correctedKernel W θ s * g s := by rw [← he]; ring
  rw [periodicP_eq_doubleTrace_add_correctedVolterraAction, correctedVolterraAction, hv, ho]
  rw [← intervalIntegral.integral_add hs hoi, add_assoc,
    ← intervalIntegral.integral_add hsaw hcorr]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change Complex.I * ((Real.sign (θ - s) : ℂ) *
      (volterraKernel W θ s * g s)) +
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s =
    sawtoothKernel θ s * g s + correctedKernel W θ s * g s
  have he := sawtoothKernel_add_correctedKernel (W := W) θ s
  calc
    _ = (Complex.I * (Real.sign (θ - s) : ℂ) * volterraKernel W θ s +
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ) * g s := by ring
    _ = (sawtoothKernel θ s + correctedKernel W θ s) * g s := by rw [← he]
    _ = sawtoothKernel θ s * g s + correctedKernel W θ s * g s := by ring

section ActualPeriodicL2

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))

local notation "ΩP" => F '' ball (0 : ℂ) 1
local notation "QP" => localConformalDiskHalfTrace hR F hFs hL
local notation "TP" => localConformalDiskH1Trace hR F hFs hL

/-- The genuine regular periodic boundary operator has its actual
periodic expression on every ordinary L2 load. No continuity or bounded
representative of the load is required. -/
theorem localConformalRegularPeriodicOperator_apply_ae_boundaryL2 (E₀ E : ℝ)
    {γ : ℝ → ℂ} {L : NNReal} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) (g : BoundaryL2) :
    (localConformalRegularPeriodicOperator hR F hFs hL E₀ E hγLip hW hc g : ℝ → ℂ)
      =ᵐ[μB] periodicP W
        (TP (h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP
          (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) : ℝ → ℂ)
        (g : ℝ → ℂ) := by
  let t : BoundaryL2 := TP (h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP
    (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g))))
  have hfI := (Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  let k : BoundaryL2 := (memLp_regularCorrectedAction hγLip hW hfI).toLp _
  have hop : localConformalRegularPeriodicOperator hR F hFs hL E₀ E hγLip hW hc g =
      (2 : ℂ) • t + sawtoothBoundaryAction g + k := by
    change (2 : ℂ) • t + sawtoothBoundaryOperator g +
      regularCorrectedBoundaryOperator hγLip hW hc g = _
    rw [sawtoothBoundaryOperator_eq_action,
      regularCorrectedBoundaryOperator_eq_integral_L2 hγLip hW hc g]
  rw [hop]
  filter_upwards [Lp.coeFn_add ((2 : ℂ) • t + sawtoothBoundaryAction g) k,
    Lp.coeFn_add ((2 : ℂ) • t) (sawtoothBoundaryAction g), Lp.coeFn_smul (2 : ℂ) t,
    MemLp.coeFn_toLp (memLp_sawtoothAction hfI),
    MemLp.coeFn_toLp (memLp_regularCorrectedAction hγLip hW hfI),
    ae_restrict_mem measurableSet_Ioc] with θ ha hb hc' hs hk hθ
  simp only [ha, hb, hc', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  dsimp only [sawtoothBoundaryAction, k]
  rw [hs, hk]
  exact (periodicP_eq_kernel_integrals_boundaryL2 hγLip hW (t : ℝ → ℂ) g
    (Ioc_subset_Icc_self hθ)).symm

end ActualPeriodicL2

section SuppliedCoordinates

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

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "ΓF" => physicalCircleTrace F
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK
  e he hsource hes
local notation "UR" => localConformalVekuaTraceRow hR F hFs hb hL hhol hinj hC hK
  e he hsource hes
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

include hR hFs in
/-- The actual smooth coordinate velocity supplies the true kernel
matrix square summability. No constant-speed premise is placed on ΓF. -/
theorem localConformal_correctedRemainderMatrix_summable
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2 := by
  have hΓ4 := contDiff_physicalCircleTrace_four_of_neighborhood hR F
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hΓ2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) ΓF := hΓ4.of_le (by norm_num)
  obtain ⟨B, hB⟩ := hΓ2.deriv'.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  have hdiff : ∀ x ∈ Icc 0 (2 * Real.pi), ∀ y ∈ Icc 0 (2 * Real.pi),
      ‖deriv ΓF x - deriv ΓF y‖ ≤ B * |x - y| := by
    intro x hx y hy
    have h := hB.dist_le_mul x hx y hy
    rwa [dist_eq_norm, Real.dist_eq] at h
  exact summable_correctedRemainderMatrix hΓLip hdiff hW hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

include hγ hτ hcoord in
/-- The genuine Vekua vector has the original physical Neumann weak
equation for its actual normalized conormal. This holds for every Hardy
input, without a Sobolev regularity premise. -/
theorem localConformalVekuaH1_isNormalizedNeumannSolution
    (E : ℝ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNormalizedNeumannSolution QF E (NF (E : ℂ) b) (VF (F 1) (E : ℂ) b) := by
  intro w
  exact localConformalVekuaH1_normalizedConormal_weak_form hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord (E : ℂ) b hbn w

include hγ hτ hcoord in
/-- Original spectral nonresonance, not a fictitious spectrum, identifies
the Vekua vector with the actual normalized Neumann Poisson solution. -/
theorem localConformalVekuaH1_eq_normalizedNeumannPoisson
    {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    VF (F 1) (E : ℂ) b = normalizedNeumannPoisson QF E (NF (E : ℂ) b) := by
  have hu := (isNormalizedNeumannSolution_iff QF E (NF (E : ℂ) b) _).mp
    (localConformalVekuaH1_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord E b hbn)
  have hp := (isNormalizedNeumannSolution_iff QF E (NF (E : ℂ) b) _).mp
    (normalizedNeumannPoisson_isSolution QF (h1HelmholtzForm_isUnit hb hL hE hnr) _)
  exact h1HelmholtzForm_injective hb hL hE hnr (hu.trans hp.symm)

include hγ hτ hcoord in
theorem normalizedNeumannBoundary_localConformalVekuaConormal
    {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    normalizedNeumannBoundary QF E (NF (E : ℂ) b) = QF (VF (F 1) (E : ℂ) b) := by
  change QF (normalizedNeumannPoisson QF E (NF (E : ℂ) b)) = _
  rw [← localConformalVekuaH1_eq_normalizedNeumannPoisson hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord hE hnr b hbn]

include hγ hτ hcoord in
private theorem periodic_null_regular_trace_eq_Vekua
    {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    TF (h1RegularResolvent ΩF E E (ContinuousLinearMap.adjoint QF (NF (E : ℂ) b))) =
      TF (VF (F 1) (E : ℂ) b) := by
  apply boundaryFourier.injective
  rw [← localConformal_halfSmoothing_halfTrace hR F hFs hL,
    ← localConformal_halfSmoothing_halfTrace hR F hFs hL]
  change sobolevSmoothing (1 / 2) (by norm_num)
    (normalizedNeumannRegular QF E E (NF (E : ℂ) b)) = _
  rw [← normalizedNeumannBoundary_eq_regular_at_nonresonant_reference QF hb hL hE
    (h1HelmholtzForm_isUnit hb hL hE hnr),
    normalizedNeumannBoundary_localConformalVekuaConormal hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord hE hnr b hbn]

include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord in
/-- Half-regular inputs have true L2 conormal loads. Their actual
periodic expression is zero, and its true Fourier normalization is the
full Neumann periodic family at the original nonresonant energy. -/
theorem localConformalPeriodicBoundaryNull_of_half_regular
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    normalizedPeriodicBoundaryFamily QF Ws E (NF (E : ℂ) b) = 0 := by
  let g : BoundaryL2 := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  have hload : sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g) = NF (E : ℂ) b :=
    localConformalVekuaForwardLoad_normalized hR F hFs (E : ℂ) b hbhalf
  have hbase := localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip hW hc
  have hop := localConformalRegularPeriodicOperator_apply_ae_boundaryL2 hR F hFs hL
    E E hΓLip hW hc g
  rw [hload, periodic_null_regular_trace_eq_Vekua hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord hE hnr b hbn] at hop
  have htrace := localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL
    hhol hinj hC hK e he hsource hes (E : ℂ) b hbn
    (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf)
  have hz : localConformalRegularPeriodicOperator hR F hFs hL E E hΓLip hW hc g = 0 := by
    apply Lp.ext
    filter_upwards [hop, htrace, Lp.coeFn_zero ℂ 2 μB,
      ae_restrict_mem measurableSet_Ioc] with θ hp ht hzero hθ
    rw [hzero]
    have hnull := localConformalVekuaForward_periodicP_eq_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hbhalf hΓLip hW hc (Ioc_subset_Icc_self hθ)
    exact hp.trans (by
      simpa only [periodicP, periodicA, ht, g, localConformalVekuaTraceRow, pow_zero,
        ContinuousLinearMap.one_apply, Pi.zero_apply] using hnull)
  have hfour := localConformalRegularPeriodicOperator_fourier hR F hFs hL
    E E hΓLip hW hc hbase g
  rw [hload] at hfour
  have hfamily : normalizedPeriodicBoundaryFamily QF Ws E =
      normalizedPeriodicRegularOperator QF E E (Ws E) hbase := by
    rw [normalizedPeriodicBoundaryFamily_eq_regular_at_nonresonant_reference QF hb hL Ws hE
      (h1HelmholtzForm_isUnit hb hL hE hnr),
      normalizedPeriodicRegularFamily_eq QF E E Ws hbase]
  apply periodic_null_halfSmoothing_injective
  rw [map_zero, hfamily, ← hfour, hz, map_zero]

private theorem periodic_null_stdBasis_half_regular (n : ℤ) :
    IsSobolevSeq (1 / 2 : ℝ) (stdBasisZ n : ℤ → ℂ) := by
  apply summable_of_ne_finset_zero (s := {n})
  intro k hk
  have hkn : k ≠ n := by simpa only [Finset.mem_singleton] using hk
  simp [stdBasisZ_apply, lp.single_apply, hkn]

include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord in
/-- The true normalized periodic boundary family annihilates the
actual conormal of every original nonpositive input. Only finite modes
are realized as ordinary L2 loads in the density proof. -/
theorem localConformalPeriodicBoundaryNull
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    normalizedPeriodicBoundaryFamily QF Ws E (NF (E : ℂ) b) = 0 := by
  let A : L2Z →L[ℂ] L2Z :=
    (normalizedPeriodicBoundaryFamily QF Ws E).comp (NF (E : ℂ))
  have hop : A.comp (1 - posProj) = 0 := by
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
      rw [hzero, map_zero]
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
      change normalizedPeriodicBoundaryFamily QF Ws E (NF (E : ℂ) (stdBasisZ n)) = 0
      apply localConformalPeriodicBoundaryNull_of_half_regular hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγ hτ hcoord Ws hE hnr hΓLip hW hc (stdBasisZ n) _
        (periodic_null_stdBasis_half_regular n)
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
  have h := congrArg (fun T : L2Z →L[ℂ] L2Z => T b) hop
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hkeep, A] using h

include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord in
/-- The exact operator null identity on the genuine closed Hardy space,
including its zero Fourier mode. -/
theorem localConformalPeriodicBoundaryNull_comp_subtype
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0) :
    (normalizedPeriodicBoundaryFamily QF Ws E).comp
      ((NF (E : ℂ)).comp nonpositiveFourierSubspace.subtypeL) = 0 := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    Submodule.subtypeL_apply]
  exact localConformalPeriodicBoundaryNull hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord Ws hE hnr hΓLip hW hc (b : L2Z) b.property

include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord in
theorem localConformalPeriodicBoundaryNull_comp_starProjection
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0) :
    (normalizedPeriodicBoundaryFamily QF Ws E).comp
      ((NF (E : ℂ)).comp nonpositiveFourierSubspace.starProjection) = 0 := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  apply localConformalPeriodicBoundaryNull hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord Ws hE hnr hΓLip hW hc
  rw [nonpositiveFourierSubspace_starProjection]
  exact one_sub_posProj_mem_nonpositive b

end SuppliedCoordinates

end PolyaNeumann
end
