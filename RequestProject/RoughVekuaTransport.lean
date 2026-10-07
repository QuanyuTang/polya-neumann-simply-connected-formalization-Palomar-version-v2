module

public import RequestProject.RoughNormalizedPrimitive
public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.ObservationLp

/-!
# A true regular correction for the rough driven equation

The mean-zero primitive is an actual BoundaryL2 element. Subtracting its
zeroth coordinate leaves an ordinary L2-forced Banach ODE, whose correction
is constructed by the genuine transport and Bochner primitive. Thus its
positive coordinates are absolutely continuous without taking an endpoint
value of the original half-order primitive.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped InnerProductSpace ComplexConjugate Topology

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

private theorem rough_continuousOn_memLp_two
    {V : Type*} [NormedAddCommGroup V] {f : ℝ → V}
    (hf : ContinuousOn f (Icc 0 (2 * Real.pi))) : MemLp f 2 μB := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    C ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
    hC x (Ioc_subset_Icc_self hx)

def roughBoundaryOneReal : Lp ℝ 2 μB :=
  (memLp_const (1 : ℝ)).toLp (fun _ : ℝ => (1 : ℝ))

private theorem rough_boundary_integral_norm_le (p : BoundaryL2) :
    (∫ θ, ‖p θ‖ ∂μB) ≤ ‖roughBoundaryOneReal‖ * ‖p‖ := by
  let a : Lp ℝ 2 μB := (Lp.memLp p).norm.toLp (fun θ => ‖p θ‖)
  have he : ⟪roughBoundaryOneReal, a⟫_ℝ = ∫ θ, ‖p θ‖ ∂μB := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μB).coeFn_toLp,
      (Lp.memLp p).norm.coeFn_toLp] with θ h1 ha
    change ⟪roughBoundaryOneReal θ, a θ⟫_ℝ = ‖p θ‖
    simp only [roughBoundaryOneReal, a, h1, ha, RCLike.inner_apply]
    norm_num
  have ha : ‖a‖ = ‖p‖ := by
    change ‖(Lp.memLp p).norm.toLp (fun θ => ‖p θ‖)‖ = ‖p‖
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable p), Lp.norm_def]
  have h := norm_inner_le_norm (𝕜 := ℝ) (E := Lp ℝ 2 μB)
    roughBoundaryOneReal a
  rw [he, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), ha] at h
  exact h

section BoundaryVectorIntegral

variable (k : ℝ → Ell2) (hk : ContinuousOn k (Icc 0 (2 * Real.pi)))

def roughBoundaryKernelBound : ℝ :=
  Classical.choose (isCompact_Icc.exists_bound_of_continuousOn hk)

private theorem roughBoundaryKernelBound_spec (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    ‖k θ‖ ≤ roughBoundaryKernelBound k hk :=
  Classical.choose_spec (isCompact_Icc.exists_bound_of_continuousOn hk) θ hθ

include hk in
theorem roughBoundaryVectorProduct_memLp (p : BoundaryL2) :
    MemLp (fun θ => p θ • k θ) 2 μB := by
  apply (Lp.memLp p).of_le_mul (c := roughBoundaryKernelBound k hk)
    ((Lp.memLp p).aestronglyMeasurable.smul
      ((hk.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change ‖p θ • k θ‖ ≤ _
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (roughBoundaryKernelBound_spec k hk θ (Ioc_subset_Icc_self hθ)) (norm_nonneg _)

include hk in
theorem roughBoundaryVectorProduct_intervalIntegrable (p : BoundaryL2) :
    IntervalIntegrable (fun θ => p θ • k θ) volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact (roughBoundaryVectorProduct_memLp k hk p).integrable (by norm_num)

include hk in
def roughBoundaryVectorIntegralLin : BoundaryL2 →ₗ[ℂ] Ell2 where
  toFun p := ∫ θ in (0 : ℝ)..(2 * Real.pi), p θ • k θ
  map_add' p q := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le]
    calc
      _ = ∫ θ, p θ • k θ + q θ • k θ ∂μB := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add p q] with θ hθ
        rw [hθ]
        exact add_smul _ _ _
      _ = _ := integral_add
        ((roughBoundaryVectorProduct_memLp k hk p).integrable (by norm_num))
        ((roughBoundaryVectorProduct_memLp k hk q).integrable (by norm_num))
  map_smul' c p := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le]
    calc
      _ = ∫ θ, c • (p θ • k θ) ∂μB := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c p] with θ hθ
        rw [hθ]
        exact (smul_smul c (p θ) (k θ)).symm
      _ = _ := integral_smul _ _

theorem roughBoundaryVectorIntegralLin_norm_le (p : BoundaryL2) :
    ‖roughBoundaryVectorIntegralLin k hk p‖ ≤
      (roughBoundaryKernelBound k hk * ‖roughBoundaryOneReal‖) * ‖p‖ := by
  have hM : 0 ≤ roughBoundaryKernelBound k hk :=
    (norm_nonneg (k 0)).trans
      (roughBoundaryKernelBound_spec k hk 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  change ‖∫ θ in (0 : ℝ)..(2 * Real.pi), p θ • k θ‖ ≤ _
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc
    _ ≤ ∫ θ, roughBoundaryKernelBound k hk * ‖p θ‖ ∂μB := by
      apply norm_integral_le_of_norm_le (((Lp.memLp p).integrable (by norm_num)).norm.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (roughBoundaryKernelBound_spec k hk θ (Ioc_subset_Icc_self hθ)) (norm_nonneg _)
    _ = roughBoundaryKernelBound k hk * (∫ θ, ‖p θ‖ ∂μB) := integral_const_mul _ _
    _ ≤ roughBoundaryKernelBound k hk * (‖roughBoundaryOneReal‖ * ‖p‖) :=
      mul_le_mul_of_nonneg_left (rough_boundary_integral_norm_le p) hM
    _ = _ := by ring

/-- A bounded actual Bochner integral, ready for extension on the Fourier
basis. Its kernel is a true continuous Ell2-valued function. -/
def roughBoundaryVectorIntegral : BoundaryL2 →L[ℂ] Ell2 :=
  (roughBoundaryVectorIntegralLin k hk).mkContinuous
    (roughBoundaryKernelBound k hk * ‖roughBoundaryOneReal‖)
    (roughBoundaryVectorIntegralLin_norm_le k hk)

@[simp] theorem roughBoundaryVectorIntegral_apply (p : BoundaryL2) :
    roughBoundaryVectorIntegral k hk p =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), p θ • k θ := rfl

end BoundaryVectorIntegral

/-- The zeroth unitary Fourier coordinate is an actual bounded functional. -/
def roughNormalizedMean : L2Z →L[ℂ] ℂ :=
  ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹) • innerSL ℂ (stdBasisZ 0)

theorem roughNormalizedMean_apply (y : L2Z) :
    roughNormalizedMean y = y 0 / (Real.sqrt (2 * Real.pi) : ℂ) := by
  have h : ⟪stdBasisZ 0, y⟫_ℂ = y 0 := by
    rw [stdBasisZ_apply, lp.inner_single_left]
    simp
  simp only [roughNormalizedMean, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    h, smul_eq_mul]
  ring

/-- True ordinary L2 forcing after the rough primitive is removed. -/
def roughVekuaRegularForce (γ : ℝ → ℂ) (E : ℝ) (p : BoundaryL2) (m : ℂ) (θ : ℝ) : Ell2 :=
  p θ • transportCoeff γ E θ (basisVec 0) + m • basisVec 0

/-- The genuine correction; no endpoint of p occurs in this definition. -/
def roughVekuaRegularCorrection (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (p : BoundaryL2) (m α : ℂ) (θ : ℝ) : Ell2 :=
  W θ (α • basisVec 0 + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
    (∫ s in (0 : ℝ)..θ,
      ContinuousLinearMap.adjoint (W s) (roughVekuaRegularForce γ E p m s)))

/-- Only coordinate zero contains the rough L2 primitive. -/
def roughVekuaDrivenVector (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (p : BoundaryL2) (m α : ℂ) (θ : ℝ) : Ell2 :=
  (-(Complex.I / (Real.sqrt 2 : ℂ)) * p θ) • basisVec 0 +
    roughVekuaRegularCorrection γ E W p m α θ

section GenuineTransport

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hγ : ContDiff ℝ 1 γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W)

include hγ in
private theorem rough_transportCoeff_continuous : Continuous (transportCoeff γ E) := by
  have hd := hγ.continuous_deriv_one
  have hc := Complex.continuous_conj.comp hd
  unfold transportCoeff
  fun_prop

include hγ in
theorem roughVekuaRegularForce_memLp (p : BoundaryL2) (m : ℂ) :
    MemLp (roughVekuaRegularForce γ E p m) 2 μB := by
  have hk : ContinuousOn (fun θ => transportCoeff γ E θ (basisVec 0))
      (Icc 0 (2 * Real.pi)) :=
    (rough_transportCoeff_continuous (E := E) hγ).continuousOn.clm_apply continuousOn_const
  exact (roughBoundaryVectorProduct_memLp _ hk p).add (memLp_const (m • basisVec 0))

include hK hγ hW in
theorem roughVekuaRegularIntegrand_memLp (p : BoundaryL2) (m : ℂ) :
    MemLp (fun θ => ContinuousLinearMap.adjoint (W θ)
      (roughVekuaRegularForce γ E p m θ)) 2 μB := by
  have hA := roughVekuaRegularForce_memLp (E := E) hγ p m
  have hWa := (ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW.1).mono Ioc_subset_Icc_self
  have heval : Continuous (fun q : (Ell2 →L[ℂ] Ell2) × Ell2 => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  apply hA.of_le_mul (c := 1)
    (heval.comp_aestronglyMeasurable
      ((hWa.aestronglyMeasurable measurableSet_Ioc).prodMk hA.aestronglyMeasurable))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  refine ((ContinuousLinearMap.adjoint (W θ)).le_opNorm
    (roughVekuaRegularForce γ E p m θ)).trans ?_
  rw [LinearIsometryEquiv.norm_map, one_mul]
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right
      (norm_transport_le_one (E := E) (W := W) hK hW
        (Ioc_subset_Icc_self hθ))
      (norm_nonneg (roughVekuaRegularForce γ E p m θ)))

include hK hγ hW in
theorem roughVekuaRegularIntegrand_intervalIntegrable (p : BoundaryL2) (m : ℂ) :
    IntervalIntegrable (fun θ => ContinuousLinearMap.adjoint (W θ)
      (roughVekuaRegularForce γ E p m θ)) volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact (roughVekuaRegularIntegrand_memLp hK hγ hW p m).integrable (by norm_num)

include hK hγ hW in
theorem roughVekuaRegularCorrection_continuousOn (p : BoundaryL2) (m α : ℂ) :
    ContinuousOn (roughVekuaRegularCorrection γ E W p m α) (Icc 0 (2 * Real.pi)) := by
  have hi : IntegrableOn (fun θ => ContinuousLinearMap.adjoint (W θ)
      (roughVekuaRegularForce γ E p m θ)) (uIcc 0 (2 * Real.pi)) := by
    rw [uIcc_of_le Real.two_pi_pos.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (roughVekuaRegularIntegrand_memLp hK hγ hW p m).integrable (by norm_num)
  have hp := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le Real.two_pi_pos.le] at hp
  have hc : ContinuousOn (fun θ => α • basisVec 0 + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
      (∫ s in (0 : ℝ)..θ,
        ContinuousLinearMap.adjoint (W s) (roughVekuaRegularForce γ E p m s)))
      (Icc 0 (2 * Real.pi)) :=
    continuousOn_const.add (ContinuousOn.const_smul hp (-(Complex.I / (Real.sqrt 2 : ℂ))))
  exact hW.1.clm_apply hc

include hK hγ hW in
theorem roughVekuaRegularCorrection_absolutelyContinuous (p : BoundaryL2) (m α : ℂ) :
    AbsolutelyContinuousOnInterval (roughVekuaRegularCorrection γ E W p m α)
      0 (2 * Real.pi) := by
  obtain ⟨L, hL⟩ := volterra_lipschitzOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2
  have hWA : AbsolutelyContinuousOnInterval W 0 (2 * Real.pi) := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hL
  have hp := absolutelyContinuousOnInterval_intervalIntegral_banach
    (roughVekuaRegularIntegrand_intervalIntegrable hK hγ hW p m)
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => α • basisVec 0) 0 (2 * Real.pi) := by
    exact (LipschitzWith.const (α • basisVec 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact absolutelyContinuousOnInterval_clm_apply hWA
    (hconst.add (hp.const_smul _))

include hK hγ hW in
theorem roughVekuaRegularCorrection_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (roughVekuaRegularCorrection γ E W p m α)
        (transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
          (-(Complex.I / (Real.sqrt 2 : ℂ))) • roughVekuaRegularForce γ E p m θ) θ := by
  have hdA := ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (roughVekuaRegularIntegrand_intervalIntegrable hK hγ hW p m)
  filter_upwards [hdA] with θ hA hθ
  have hc := Ioo_subset_Icc_self hθ
  have hdW := (hasDerivWithinAt_transport hγ.continuous_deriv_one.continuousOn hW hc).hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)
  have hconst : HasDerivAt (fun _ : ℝ => α • basisVec 0) 0 θ :=
    hasDerivAt_const θ (α • basisVec 0)
  have hd := hasDerivAt_clm_apply_real hdW
    (hconst.add ((hA hθ).const_smul (-(Complex.I / (Real.sqrt 2 : ℂ)))))
  have hu := transport_mul_adjoint hK hW hc
  have hcancel : W θ (ContinuousLinearMap.adjoint (W θ)
      (roughVekuaRegularForce γ E p m θ)) = roughVekuaRegularForce γ E p m θ := by
    rw [← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply]
  have hd' : HasDerivAt (roughVekuaRegularCorrection γ E W p m α)
      ((transportCoeff γ E θ * W θ)
          (α • basisVec 0 + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
            (∫ s in (0 : ℝ)..θ,
              ContinuousLinearMap.adjoint (W s) (roughVekuaRegularForce γ E p m s))) +
        W θ (0 + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
          (ContinuousLinearMap.adjoint (W θ)) (roughVekuaRegularForce γ E p m θ))) θ := by
    exact hd
  convert hd' using 1
  dsimp only [roughVekuaRegularCorrection]
  simp only [ContinuousLinearMap.mul_apply, map_zero, add_zero, zero_add,
    map_smul, hcancel]

include hK hγ hW in
theorem roughVekuaRegularCorrection_derivative_memLp (p : BoundaryL2) (m α : ℂ) :
    MemLp (fun θ => transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ))) • roughVekuaRegularForce γ E p m θ) 2 μB := by
  have hc := (rough_transportCoeff_continuous (E := E) hγ).continuousOn.clm_apply
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hci : MemLp (fun θ => transportCoeff γ E θ
      (roughVekuaRegularCorrection γ E W p m α θ)) 2 μB := by
    apply MemLp.of_bound ((hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) M
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hM θ (Ioc_subset_Icc_self hθ)
  exact hci.add (by
    exact (roughVekuaRegularForce_memLp (E := E) hγ p m).const_smul
      (-(Complex.I / (Real.sqrt 2 : ℂ))))

include hγ hW in
private theorem rough_adjoint_transport_row_hasDerivAt {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt (fun t => ContinuousLinearMap.adjoint (W t) (basisVec 0))
      (-(ContinuousLinearMap.adjoint (W θ)
        (transportCoeff γ E θ (basisVec 0)))) θ := by
  have hdW := (hasDerivWithinAt_transport hγ.continuous_deriv_one.continuousOn hW
    (Ioo_subset_Icc_self hθ)).hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)
  have hdA : HasDerivAt (fun t => ContinuousLinearMap.adjoint (W t))
      (-(ContinuousLinearMap.adjoint (W θ) * transportCoeff γ E θ)) θ := by
    have hs : star (transportCoeff γ E θ) = -transportCoeff γ E θ :=
      transportCoeff_star γ E θ
    have hstar := hdW.star
    rw [star_mul, hs, ContinuousLinearMap.star_eq_adjoint] at hstar
    have h_simpa := hstar
    simp only [mul_neg] at h_simpa ⊢
    exact h_simpa
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply,
    map_zero, add_zero] using
    hasDerivAt_clm_apply_real hdA (hasDerivAt_const θ (basisVec 0))

/-- The actual derivative of the projected observation test. -/
def roughProjectedObservationDerivative (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (v : Ell2) (θ : ℝ) : ℂ :=
  -⟪ContinuousLinearMap.adjoint (W θ) (transportCoeff γ E θ (basisVec 0)),
    cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v⟫_ℂ

include hγ hW in
theorem roughProjectedObservation_hasDerivAt (v : Ell2) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt (fun t => ⟪projObsRow W t, v⟫_ℂ)
      (roughProjectedObservationDerivative γ E W v θ) θ := by
  let Q := cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
  have hp := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ
    (rough_adjoint_transport_row_hasDerivAt hγ hW hθ)
  convert hp.inner ℂ (hasDerivAt_const θ v) using 1 <;>
    simp [projObsRow, roughProjectedObservationDerivative, Q, Function.comp_def,
      ContinuousLinearMap.coe_restrictScalars, map_neg, inner_zero_right,
      inner_neg_left, inner_cutProj_left, inner_conj_symm]

include hγ hW in
theorem roughProjectedObservationDerivative_memLp (v : Ell2) :
    MemLp (roughProjectedObservationDerivative γ E W v) 2 μB := by
  have hc : ContinuousOn (roughProjectedObservationDerivative γ E W v)
      (Icc 0 (2 * Real.pi)) :=
    ((ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW.1).clm_apply
      ((rough_transportCoeff_continuous (E := E) hγ).continuousOn.clm_apply
        continuousOn_const)).inner continuousOn_const |>.neg
  exact rough_continuousOn_memLp_two hc

include hK hW in
theorem roughProjectedObservation_absolutelyContinuous (v : Ell2) :
    AbsolutelyContinuousOnInterval (fun t => ⟪projObsRow W t, v⟫_ℂ)
      0 (2 * Real.pi) := by
  let M : NNReal := ⟨Real.sqrt E * shiftConst * K * ‖v‖, by
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) shiftConst_nonneg)
      K.coe_nonneg) (norm_nonneg _)⟩
  have hl : LipschitzOnWith M (fun t => ⟪projObsRow W t, v⟫_ℂ)
      (Icc 0 (2 * Real.pi)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, ← inner_sub_left]
    calc
      _ ≤ ‖projObsRow W x - projObsRow W y‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ (Real.sqrt E * shiftConst * K * |x - y|) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (norm_projObsRow_sub_le hK hW hx hy) (norm_nonneg _)
      _ = M * dist x y := by
        rw [Real.dist_eq]
        change _ = (Real.sqrt E * shiftConst * K * ‖v‖) * |x - y|
        ring
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le Real.two_pi_pos.le] using hl

include hK hγ hW in
theorem boundaryFourier_projectedObservation_sobolev_one (v : Ell2) :
    IsSobolevSeq 1
      (boundaryFourier (projectedObservationBoundary hK hW v) : ℤ → ℂ) := by
  have hp : (⟪projObsRow W 0, v⟫_ℂ) = ⟪projObsRow W (2 * Real.pi), v⟫_ℂ := by
    rw [projObsRow_endpoint hW]
  have hr := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (roughProjectedObservation_absolutelyContinuous hK hW v)
    (roughProjectedObservationDerivative_memLp hγ hW v)
    (Eventually.of_forall fun θ hθ => roughProjectedObservation_hasDerivAt hγ hW v hθ) hp
  have hcoef : (boundaryFourier (projectedObservationBoundary hK hW v) : ℤ → ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) •
        fourierCoeffOn Real.two_pi_pos (fun θ => ⟪projObsRow W θ, v⟫_ℂ) := by
    funext n
    rw [boundaryFourier_apply,
      fourierCoeffOn_congr_ae Real.two_pi_pos (projectedObservationBoundary_coe hK hW v)]
    rfl
  rw [hcoef]
  exact isSobolevSeq_smul _ hr

include hK hγ hW in
theorem roughProjectedObservation_fourier_derivative (v : Ell2) :
    roughFourierTestDerivative
      (boundaryFourier (projectedObservationBoundary hK hW v))
      (boundaryFourier_projectedObservation_sobolev_one hK hγ hW v) =
    boundaryFourier ((roughProjectedObservationDerivative_memLp hγ hW v).toLp
      (roughProjectedObservationDerivative γ E W v)) := by
  apply lp.ext
  funext n
  rw [roughFourierTestDerivative_apply]
  simp only [boundaryFourier_apply]
  rw [fourierCoeffOn_congr_ae Real.two_pi_pos
      (roughProjectedObservationDerivative_memLp hγ hW v).coeFn_toLp,
    fourierCoeffOn_of_ac_ae_hasDerivAt
      (roughProjectedObservation_absolutelyContinuous hK hW v)
      (roughProjectedObservationDerivative_memLp hγ hW v)
      (Eventually.of_forall fun θ hθ => roughProjectedObservation_hasDerivAt hγ hW v hθ)
      (by rw [projObsRow_endpoint hW]),
    fourierCoeffOn_congr_ae Real.two_pi_pos (projectedObservationBoundary_coe hK hW v)]
  ring

include hγ hW in
theorem rough_endpoint_kernel_continuousOn :
    ContinuousOn (fun θ => ContinuousLinearMap.adjoint (W θ)
      (transportCoeff γ E θ (basisVec 0))) (Icc 0 (2 * Real.pi)) :=
  (ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW.1).clm_apply
    ((rough_transportCoeff_continuous (E := E) hγ).continuousOn.clm_apply continuousOn_const)

include hγ hW in
/-- The endpoint source is a bounded operator of the arbitrary normalized
input. This permits a genuine finite-mode density argument. -/
def roughVekuaEndpointCore : L2Z →L[ℂ] Ell2 := by
  exact (roughBoundaryVectorIntegral
    (fun θ => ContinuousLinearMap.adjoint (W θ) (transportCoeff γ E θ (basisVec 0)))
    (rough_endpoint_kernel_continuousOn hγ hW)).comp roughNormalizedPrimitive +
  (ContinuousLinearMap.toSpanSingleton ℂ (∫ θ in (0 : ℝ)..(2 * Real.pi),
    ContinuousLinearMap.adjoint (W θ) (basisVec 0))).comp roughNormalizedMean

include hγ hW in
theorem roughVekuaEndpointCore_apply (y : L2Z) :
    roughVekuaEndpointCore hγ hW y =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ContinuousLinearMap.adjoint (W θ)
        (roughVekuaRegularForce γ E (roughNormalizedPrimitive y) (roughNormalizedMean y) θ) := by
  have hk := rough_endpoint_kernel_continuousOn hγ hW
  have h0 := continuousOn_adjoint_apply hW.1 (basisVec 0)
  have hi0 : IntervalIntegrable (fun θ => roughNormalizedMean y •
      ContinuousLinearMap.adjoint (W θ) (basisVec 0)) volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable
    have h_simpa := h0.const_smul (roughNormalizedMean y)
    simp only [uIcc_of_le Real.two_pi_pos.le] at h_simpa ⊢
    exact h_simpa
  simp only [roughVekuaEndpointCore, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, roughBoundaryVectorIntegral_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_add
    (roughBoundaryVectorProduct_intervalIntegrable _ hk (roughNormalizedPrimitive y)) hi0]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [roughVekuaRegularForce, map_add, map_smul]

include hK hγ hW in
private theorem rough_projectedObservation_weightedFourier (v : Ell2) :
    sobVec (1 / 2 : ℝ)
      (boundaryFourier (projectedObservationBoundary hK hW v) : ℤ → ℂ)
      ((sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (boundaryFourier_projectedObservation_sobolev_one hK hγ hW v)).1) =
    (Real.sqrt (2 * Real.pi) : ℂ) •
      rowAnalysis (normProjObsRow W) (summable_normProjObsRow hK hW) v := by
  apply lp.ext
  funext n
  simp only [sobVec_apply, boundaryFourier_projectedObservation hK hW,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, rowAnalysis_apply, normProjObsRow,
    inner_smul_left, Complex.conj_ofReal]
  rw [← Real.sqrt_eq_rpow]
  change (Real.sqrt (sobWeight n) : ℂ) *
      ((Real.sqrt (2 * Real.pi) : ℂ) * ⟪projObsCoeffVec W n, v⟫_ℂ) =
    (Real.sqrt (2 * Real.pi) : ℂ) *
      ((Real.sqrt (sobWeight n) : ℂ) * ⟪projObsCoeffVec W n, v⟫_ℂ)
  ring

include hK hγ hW in
private theorem rough_endpoint_mean_pairing (y : L2Z) (v : Ell2) :
    ⟪cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v,
      roughNormalizedMean y • (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ContinuousLinearMap.adjoint (W θ) (basisVec 0))⟫_ℂ =
    ⟪sobVec (1 / 2 : ℝ)
      (boundaryFourier (projectedObservationBoundary hK hW v) : ℤ → ℂ)
      ((sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (boundaryFourier_projectedObservation_sobolev_one hK hγ hW v)).1),
      zeroModeProjection y⟫_ℂ := by
  have hi : IntervalIntegrable (fun θ => ContinuousLinearMap.adjoint (W θ) (basisVec 0))
      volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le Real.two_pi_pos.le] using
      continuousOn_adjoint_apply hW.1 (basisVec 0)
  rw [inner_smul_right]
  have hcomp := ContinuousLinearMap.intervalIntegral_comp_comm
    (innerSL ℂ (cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v)) hi
  simp only [innerSL_apply_apply] at hcomp
  rw [← hcomp]
  simp only [innerSL_apply_apply]
  have hinner (θ : ℝ) :
      ⟪cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v,
        ContinuousLinearMap.adjoint (W θ) (basisVec 0)⟫_ℂ =
      conj (⟪projObsRow W θ, v⟫_ℂ) := by
    rw [projObsRow]
    exact (inner_cutProj_left _ v _).trans (inner_conj_symm v _).symm
  simp_rw [hinner]
  rw [intervalIntegral_conj, zeroModeProjection_eq_single, lp.inner_single_right,
    RCLike.inner_apply', sobVec_apply]
  simp only [sobWeight, Int.cast_zero, abs_zero, add_zero, Real.one_rpow,
    Complex.ofReal_one, one_mul]
  rw [boundaryFourier_apply,
    fourierCoeffOn_congr_ae Real.two_pi_pos (projectedObservationBoundary_coe hK hW v),
    fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, sub_zero, Complex.real_smul,
    map_mul, Complex.conj_ofReal]
  rw [roughNormalizedMean_apply]
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  have hT : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have hsq : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = ((2 * Real.pi : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.two_pi_pos.le
  field_simp [hs, hT, Real.pi_ne_zero]
  rw [hsq]
  have hprod : ((Real.pi * 2 : ℝ) : ℂ) *
      ((Real.pi⁻¹ * (1 / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast (by
      field_simp [Real.pi_ne_zero] :
        (Real.pi * 2) * (Real.pi⁻¹ * (1 / 2)) = (1 : ℝ))
  calc
    _ = (y 0) *
        (starRingEnd ℂ) (∫ (x : ℝ) in 0..Real.pi * 2,
          ⟪projObsRow W x, v⟫_ℂ) * 1 := by ring
    _ = (y 0) *
        (starRingEnd ℂ) (∫ (x : ℝ) in 0..Real.pi * 2,
          ⟪projObsRow W x, v⟫_ℂ) *
        (((Real.pi * 2 : ℝ) : ℂ) * ((Real.pi⁻¹ * (1 / 2) : ℝ) : ℂ)) := by rw [hprod]
    _ = _ := by ring

include hK hγ hW in
private theorem rough_endpoint_primitive_pairing (y : L2Z) (v : Ell2) :
    ⟪cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v,
      roughBoundaryVectorIntegral
        (fun θ => ContinuousLinearMap.adjoint (W θ)
          (transportCoeff γ E θ (basisVec 0)))
        (rough_endpoint_kernel_continuousOn hγ hW) (roughNormalizedPrimitive y)⟫_ℂ =
    -⟪roughFourierTestDerivative
      (boundaryFourier (projectedObservationBoundary hK hW v))
      (boundaryFourier_projectedObservation_sobolev_one hK hγ hW v),
      boundaryFourier (roughNormalizedPrimitive y)⟫_ℂ := by
  rw [roughProjectedObservation_fourier_derivative hK hγ hW,
    boundaryFourier.inner_map_map, L2.inner_def, roughBoundaryVectorIntegral_apply]
  have hcomp := ContinuousLinearMap.intervalIntegral_comp_comm
    (innerSL ℂ (cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v))
    (roughBoundaryVectorProduct_intervalIntegrable _
      (rough_endpoint_kernel_continuousOn hγ hW) (roughNormalizedPrimitive y))
  simp only [innerSL_apply_apply] at hcomp
  rw [← hcomp, intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(roughProjectedObservationDerivative_memLp hγ hW v).coeFn_toLp]
    with θ hθ
  simp only [innerSL_apply_apply, inner_smul_right, RCLike.inner_apply', hθ,
    roughProjectedObservationDerivative, map_neg, inner_conj_symm]
  ring

include hK hγ hW in
/-- The true endpoint defect agrees with the original projected observation
for every normalized negative-half-order load. The proof uses actual H1
observation tests and Fourier weak integration by parts; no primitive
endpoint value is assigned. -/
theorem roughVekuaEndpointCore_projected (y : L2Z) :
    cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
      (roughVekuaEndpointCore hγ hW y) =
    (Real.sqrt (2 * Real.pi) : ℂ) • projObsDual W y := by
  apply ext_inner_left ℂ
  intro v
  rw [← inner_cutProj_left]
  simp only [roughVekuaEndpointCore, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    inner_add_right]
  rw [rough_endpoint_primitive_pairing hK hγ hW,
    rough_endpoint_mean_pairing hK hγ hW,
    roughNormalizedPrimitive_weak_pairing, neg_neg, ← inner_add_right, sub_add_cancel,
    rough_projectedObservation_weightedFourier hK hγ hW,
    inner_smul_left, Complex.conj_ofReal, inner_smul_right,
    projObsDual_eq hK hW]
  congr 1
  exact (ContinuousLinearMap.adjoint_inner_right
    (rowAnalysis (normProjObsRow W) (summable_normProjObsRow hK hW)) v y).symm

include hK hγ hW in
theorem roughVekuaEndpointCore_eq_smul_of_projObsDual_eq_zero (y : L2Z)
    (hy : projObsDual W y = 0) :
    ∃ β : ℂ, roughVekuaEndpointCore hγ hW y =
      β • cutC (W (2 * Real.pi)) (basisVec 0) := by
  have hp := roughVekuaEndpointCore_projected hK hγ hW y
  rw [hy, smul_zero] at hp
  refine ⟨(((‖cutC (W (2 * Real.pi)) (basisVec 0)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
    ⟪cutC (W (2 * Real.pi)) (basisVec 0), roughVekuaEndpointCore hγ hW y⟫_ℂ), ?_⟩
  simp only [cutProj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul] at hp
  exact sub_eq_zero.mp hp

include hW in
theorem roughVekuaRegularCorrection_zero (p : BoundaryL2) (m α : ℂ) :
    roughVekuaRegularCorrection γ E W p m α 0 = α • basisVec 0 := by
  simp [roughVekuaRegularCorrection, transport_zero_eq hW]

include hK hγ hW in
/-- The actual endpoint compatibility is an explicit computed source
integral; it does not involve an endpoint value of the rough primitive. -/
theorem roughVekuaRegularCorrection_endpoint_of_core_eq_smul (y : L2Z) (β : ℂ)
    (hcore : roughVekuaEndpointCore hγ hW y =
      β • cutC (W (2 * Real.pi)) (basisVec 0)) :
    roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * β) (2 * Real.pi) =
    roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * β) 0 := by
  rw [roughVekuaRegularCorrection_zero hW]
  change W (2 * Real.pi)
    ((-(Complex.I / (Real.sqrt 2 : ℂ)) * β) • basisVec 0 +
      (-(Complex.I / (Real.sqrt 2 : ℂ))) •
        (∫ θ in (0 : ℝ)..(2 * Real.pi), ContinuousLinearMap.adjoint (W θ)
          (roughVekuaRegularForce γ E (roughNormalizedPrimitive y) (roughNormalizedMean y) θ))) = _
  rw [← roughVekuaEndpointCore_apply hγ hW, hcore, smul_smul, ← smul_add]
  have hu := transport_mul_adjoint hK hW ⟨Real.two_pi_pos.le, le_rfl⟩
  have hcut : basisVec 0 + cutC (W (2 * Real.pi)) (basisVec 0) =
      ContinuousLinearMap.adjoint (W (2 * Real.pi)) (basisVec 0) := by
    simp only [cutC]
    abel
  rw [hcut, map_smul, ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply]

include hK hγ hW in
/-- Original projected-observation nullity supplies the actual periodic
regular correction. Only this continuous correction has endpoint values. -/
theorem roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero
    (y : L2Z) (hy : projObsDual W y = 0) :
    ∃ α : ℂ,
      roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α 0 = α • basisVec 0 ∧
      roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α (2 * Real.pi) = α • basisVec 0 := by
  obtain ⟨β, hβ⟩ := roughVekuaEndpointCore_eq_smul_of_projObsDual_eq_zero hK hγ hW y hy
  refine ⟨-(Complex.I / (Real.sqrt 2 : ℂ)) * β,
    roughVekuaRegularCorrection_zero hW _ _ _, ?_⟩
  rw [roughVekuaRegularCorrection_endpoint_of_core_eq_smul hK hγ hW y β hβ,
    roughVekuaRegularCorrection_zero hW]

theorem roughVekuaDrivenVector_positive_coord (p : BoundaryL2) (m α : ℂ)
    (n : ℕ) (θ : ℝ) :
    (roughVekuaDrivenVector γ E W p m α θ : ℕ → ℂ) (n + 1) =
      (roughVekuaRegularCorrection γ E W p m α θ : ℕ → ℂ) (n + 1) := by
  simp only [roughVekuaDrivenVector, lp.coeFn_add, Pi.add_apply,
    lp.coeFn_smul, Pi.smul_apply, basisVec_coord, Nat.succ_ne_zero,
    if_false, smul_eq_mul, mul_zero, zero_add]

include hK hγ hW in
theorem roughVekuaDrivenRow_succ_absolutelyContinuous (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 1))
      0 (2 * Real.pi) := by
  have he : physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 1) =
      fun θ => (innerSL ℂ (basisVec (n + 1)))
        (roughVekuaRegularCorrection γ E W p m α θ) := by
    funext θ
    simp only [physicalDrivenRow, Nat.succ_ne_zero, if_false,
      roughVekuaDrivenVector_positive_coord, innerSL_apply_apply, inner_basisVec]
  rw [he]
  exact absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec (n + 1)))
    (roughVekuaRegularCorrection_absolutelyContinuous hK hγ hW p m α)

include hK hγ hW in
theorem roughVekuaDrivenScaledRow_succ_absolutelyContinuous
    (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 1))
      0 (2 * Real.pi) := by
  exact (roughVekuaDrivenRow_succ_absolutelyContinuous hK hγ hW p m α n).const_smul (physicalDrivenQ E ^ (n + 1))

theorem roughVekuaRegularCorrection_derivative_eq_transportCoeff
    (p : BoundaryL2) (m α : ℂ) (θ : ℝ) :
    transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ))) • roughVekuaRegularForce γ E p m θ =
    transportCoeff γ E θ (roughVekuaDrivenVector γ E W p m α θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * m) • basisVec 0 := by
  simp only [roughVekuaRegularForce, roughVekuaDrivenVector, map_add, map_smul,
    smul_add, smul_smul, smul_eq_mul]
  abel

include hK hγ hW in
/-- Every positive row has the genuine driven recurrence even though the
zeroth row contains only an L2 primitive. This includes the n=1 coupling
to the exceptional sqrt(2)-scaled zeroth row. -/
theorem roughVekuaDrivenRow_succ_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 1))
        (physicalDrivenQ E *
          (deriv γ θ * physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 2) θ +
            conj (deriv γ θ) * physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) n θ)) θ := by
  filter_upwards [roughVekuaRegularCorrection_ae_hasDerivAt hK hγ hW p m α]
    with θ hθ hmem
  have hd := ((innerSL ℂ (basisVec (n + 1))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hθ hmem)
  simp only [ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at hd
  rw [roughVekuaRegularCorrection_derivative_eq_transportCoeff] at hd
  convert hd using 1
  · funext t
    simp only [Function.comp_apply, physicalDrivenRow, Nat.succ_ne_zero, if_false,
      roughVekuaDrivenVector_positive_coord]
    change (roughVekuaRegularCorrection γ E W p m α t : ℕ → ℂ) (n + 1) =
      ⟪basisVec (n + 1), roughVekuaRegularCorrection γ E W p m α t⟫_ℂ
    rw [inner_basisVec]
  · simp only [inner_basisVec, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, basisVec_coord, Nat.succ_ne_zero, if_false,
      mul_zero, add_zero]
    rw [transportCoeff_apply_coord, shiftN_apply_succ]
    cases n with
    | zero => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight]
    | succ n => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight, Nat.add_assoc]

include hK hγ hW in
theorem roughVekuaDrivenScaledRow_succ_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 1))
        (deriv γ θ * physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 2) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) n θ) θ := by
  filter_upwards [roughVekuaDrivenRow_succ_ae_hasDerivAt hK hγ hW p m α n] with θ hθ hmem
  convert (hθ hmem).const_mul (physicalDrivenQ E ^ (n + 1)) using 1
  · funext t
    rfl
  · simp only [physicalDrivenScaledRow]
    ring

include hK hγ hW in
theorem roughVekuaDrivenVector_memLp (p : BoundaryL2) (m α : ℂ) :
    MemLp (roughVekuaDrivenVector γ E W p m α) 2 μB := by
  have hfirst := (roughBoundaryVectorProduct_memLp
    (fun _ : ℝ => basisVec 0) continuousOn_const p).const_smul
    (-(Complex.I / (Real.sqrt 2 : ℂ)))
  have hsecond := rough_continuousOn_memLp_two
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α)
  refine MemLp.ae_eq (Eventually.of_forall ?_) (hfirst.add hsecond)
  intro θ
  simp only [roughVekuaDrivenVector, Pi.add_apply, Pi.smul_apply,
    smul_smul, smul_eq_mul]

include hK hγ hW in
theorem roughVekuaDrivenRow_succ_derivative_memLp (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    MemLp (fun θ =>
      physicalDrivenQ E *
        (deriv γ θ * physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 2) θ +
          conj (deriv γ θ) * physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) n θ))
      2 μB := by
  let A := innerSL ℂ (basisVec (n + 1))
  have hd := (roughVekuaRegularCorrection_derivative_memLp hK hγ hW p m α).continuousLinearMap_comp A
  apply MemLp.ae_eq (hf_Lp := hd)
  refine Eventually.of_forall fun θ => ?_
  simp only [A, Function.comp_def, innerSL_apply_apply, inner_basisVec,
    roughVekuaRegularCorrection_derivative_eq_transportCoeff,
    lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    basisVec_coord, Nat.succ_ne_zero, if_false, mul_zero, add_zero]
  rw [transportCoeff_apply_coord, shiftN_apply_succ]
  cases n with
  | zero => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight]
  | succ n => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight, Nat.add_assoc]

include hW in
theorem roughVekuaDrivenRow_succ_zero (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 1) 0 = 0 := by
  simp only [physicalDrivenRow, Nat.succ_ne_zero, if_false,
    roughVekuaDrivenVector_positive_coord, roughVekuaRegularCorrection_zero hW,
    lp.coeFn_smul, Pi.smul_apply, basisVec_coord, if_false, smul_eq_mul, mul_zero]

theorem roughVekuaDrivenRow_succ_endpoint (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0) (n : ℕ) :
    physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 1) (2 * Real.pi) = 0 := by
  simp only [physicalDrivenRow, Nat.succ_ne_zero, if_false,
    roughVekuaDrivenVector_positive_coord, hα, lp.coeFn_smul,
    Pi.smul_apply, basisVec_coord, Nat.succ_ne_zero, if_false, smul_eq_mul, mul_zero]

include hK hγ hW in
theorem roughVekuaDrivenRow_succ_sobolev_one (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0) (n : ℕ) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 1))) := by
  exact isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (roughVekuaDrivenRow_succ_absolutelyContinuous hK hγ hW p m α n)
    (roughVekuaDrivenRow_succ_derivative_memLp hK hγ hW p m α n)
    (roughVekuaDrivenRow_succ_ae_hasDerivAt hK hγ hW p m α n)
    ((roughVekuaDrivenRow_succ_zero hW p m α n).trans
      (roughVekuaDrivenRow_succ_endpoint p m α hα n).symm)

include hK hγ hW in
/-- Arbitrary normalized observation-kernel data have genuine H1 positive
driven rows, derived from the true ODE and its computed endpoint defect.
The rough zeroth row has not acquired an unsupported point value or H1
claim. -/
theorem roughVekuaDrivenRows_exists_sobolev_one_of_projObsDual_eq_zero
    (y : L2Z) (hy : projObsDual W y = 0) :
    ∃ α : ℂ,
      roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α 0 = α • basisVec 0 ∧
      roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α (2 * Real.pi) = α • basisVec 0 ∧
      ∀ n : ℕ, IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos
        (physicalDrivenRow (roughVekuaDrivenVector γ E W
          (roughNormalizedPrimitive y) (roughNormalizedMean y) α) (n + 1))) := by
  obtain ⟨α, hα0, hαT⟩ :=
    roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero hK hγ hW y hy
  exact ⟨α, hα0, hαT, fun n => roughVekuaDrivenRow_succ_sobolev_one hK hγ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α hαT n⟩

end GenuineTransport

end PolyaNeumann

end
