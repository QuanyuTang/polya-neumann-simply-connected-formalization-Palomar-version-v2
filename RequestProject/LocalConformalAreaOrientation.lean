module

public import RequestProject.LocalConformalBoundaryGeometry
public import RequestProject.DiskHarmonicModes
public import RequestProject.LocalConformalH1
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Positive orientation of actual supplied conformal disk coordinates

The real Cauchy--Riemann identity and symmetry of mixed real derivatives
prove that the actual supplied map is harmonic inside the unit disk. A
genuine smooth compact cutoff agrees with that map near the closed disk.
Applying the proved disk Green identity to the cutoff and its conjugate
gives twice the conformal Jacobian integral. Actual change of variables
identifies this integral with the ordinary area of the open-disk image.

The unit-circle conormal is `-i` times the angular derivative, so the real
part of the Green boundary pairing is precisely the signed-area density.
This proves positive orientation without assuming a winding or area
identity. The exact normalized arclength change preserves that integral,
and the resulting curve satisfies all six actual `IsBoundaryParam` fields.
The existence of the initial supplied conformal map remains separate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate Topology

private theorem area_dirD_comm {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v w z : ℂ) :
    dirD (dirD φ v) w z = dirD (dirD φ w) v z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiable (by simp) z
  have hv : fderiv ℝ (dirD φ v) z w = fderiv ℝ (fderiv ℝ φ) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ φ x v) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hw : fderiv ℝ (dirD φ w) z v = fderiv ℝ (fderiv ℝ φ) z v w := by
    change fderiv ℝ (fun x => fderiv ℝ φ x w) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change fderiv ℝ (dirD φ v) z w = fderiv ℝ (dirD φ w) z v
  rw [hv, hw]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).eq w v

/-- Differentiating the actual CR identity on an open set and commuting
the mixed derivatives gives the classical Laplacian zero. -/
private theorem area_lap_eq_zero_of_CR {U : Set ℂ} (hU : IsOpen U)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hCR : ∀ z ∈ U, dirD φ Complex.I z = Complex.I * dirD φ 1 z)
    {z : ℂ} (hz : z ∈ U) : lap φ z = 0 := by
  have heq : dirD φ Complex.I =ᶠ[𝓝 z] fun w => Complex.I * dirD φ 1 w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hCR w hw
  have hd : DifferentiableAt ℝ (dirD φ 1) z :=
    ((hφ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply
      contDiff_const).differentiable (by simp) z
  have hD (v : ℂ) :
      dirD (dirD φ Complex.I) v z = Complex.I * dirD (dirD φ 1) v z := by
    simpa only [dirD, ContinuousLinearMap.smul_apply, smul_eq_mul] using
      congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
        (heq.fderiv_eq.trans (fderiv_const_mul hd Complex.I))
  rw [lap, hD Complex.I, area_dirD_comm hφ 1 Complex.I z, hD 1]
  ring_nf; simp only [Complex.I_sq]; ring

private theorem area_cutoff_dirD_disk {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (v : ℂ) :
    dirD (smoothDiskCutoff R hR F) v z = deriv F z * v := by
  unfold dirD
  rw [fderiv_smoothDiskCutoff_eq hR F (ball_subset_closedBall hz),
    (hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  change fderiv ℂ F z v = _
  exact fderiv_eq_deriv_mul

theorem localConformal_cutoff_lap_eq_zero {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    lap (smoothDiskCutoff R hR F) z = 0 := by
  apply area_lap_eq_zero_of_CR isOpen_ball (contDiff_smoothDiskCutoff hR hFs) _ hz
  intro w hw
  rw [area_cutoff_dirD_disk hR F hhol hw Complex.I,
    area_cutoff_dirD_disk hR F hhol hw 1, mul_one, mul_comm]

/-- The cutoff is equal in a neighbourhood, so its proved harmonicity is
the harmonicity of the actual F, expressed with the project's real lap. -/
theorem localConformal_lap_eq_zero {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : lap F z = 0 := by
  have heq := smoothDiskCutoff_eventuallyEq hR F
    (closedBall_subset_ball (show (1 : ℝ) < (R + 1) / 2 by linarith)
      (ball_subset_closedBall hz))
  have hdir (v : ℂ) :
      dirD (smoothDiskCutoff R hR F) v =ᶠ[𝓝 z] dirD F v :=
    (heq.fderiv (𝕜 := ℝ)).fun_comp (fun A : ℂ →L[ℝ] ℂ => A v)
  have hlap : lap (smoothDiskCutoff R hR F) z = lap F z := by
    change fderiv ℝ (dirD (smoothDiskCutoff R hR F) 1) z 1 +
      fderiv ℝ (dirD (smoothDiskCutoff R hR F) Complex.I) z Complex.I =
        fderiv ℝ (dirD F 1) z 1 + fderiv ℝ (dirD F Complex.I) z Complex.I
    rw [(hdir 1).fderiv_eq, (hdir Complex.I).fderiv_eq]
  exact hlap.symm.trans (localConformal_cutoff_lap_eq_zero hR F hFs hhol hz)

private theorem area_conj_mul_self (a : ℂ) : conj a * a = (‖a‖ ^ 2 : ℝ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

private theorem area_cutoff_gradient_density {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (∑ i : Fin 2, dirD (fun w => conj (smoothDiskCutoff R hR F w)) (coordDir i) z *
      dirD (smoothDiskCutoff R hR F) (coordDir i) z) =
        ((2 * ‖deriv F z‖ ^ 2 : ℝ) : ℂ) := by
  have hφ := contDiff_smoothDiskCutoff hR hFs
  simp only [Fin.sum_univ_two, show coordDir 0 = 1 from rfl,
    show coordDir 1 = Complex.I from rfl,
    dirD_conj (hφ.of_le (by simp))]
  rw [area_conj_mul_self, area_conj_mul_self,
    area_cutoff_dirD_disk hR F hhol hz 1,
    area_cutoff_dirD_disk hR F hhol hz Complex.I]
  simp only [mul_one, norm_mul, Complex.norm_I]
  push_cast
  ring

/-- The ordinary area is exactly the genuine conformal Jacobian integral. -/
theorem localConformal_jacobian_integral_eq_volume (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) :
    (∫ z in ball (0 : ℂ) 1, ‖deriv F z‖ ^ 2) =
      (volume (F '' ball (0 : ℂ) 1)).toReal := by
  have hcv := localConformal_integral_image isOpen_ball hhol hinj (fun _ => (1 : ℝ))
  simpa only [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] using hcv.symm

private theorem area_cutoff_conormal {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (θ : ℝ) :
    fderiv ℝ (smoothDiskCutoff R hR F) (circleMap 0 1 θ)
        (-(Complex.I * deriv (circleMap 0 1) θ)) =
      -(Complex.I * deriv (physicalCircleTrace F) θ) := by
  have hz := circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ
  rw [unitCircle_conormalDirection, fderiv_smoothDiskCutoff_eq hR F hz,
    localConformal_fderiv_closedDisk hR F hFs hhol hz,
    localConformal_circleTrace_deriv hR F hFs hhol]
  ring_nf; simp only [Complex.I_sq]; ring

/-- Disk Green applied to the actual compact cutoff gives the complex
boundary energy. All factors use ordinary area and angular measures. -/
theorem localConformal_disk_green_energy {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) :
    doubleLayer (circleMap 0 1) (fun θ => conj (physicalCircleTrace F θ))
      (smoothDiskCutoff R hR F) =
        ((2 * (volume (F '' ball (0 : ℂ) 1)).toReal : ℝ) : ℂ) := by
  have hφ := smoothDiskCutoff_testFunction hR hFs
  have hV := hφ.conj
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
  have htrace : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      conj (smoothDiskCutoff R hR F (circleMap 0 1 θ)) =
        conj (physicalCircleTrace F θ) := by
    intro θ _
    exact congrArg conj (smoothDiskCutoff_eq_closedDisk hR F
      (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))
  have hgreen := doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam hK hV.2.1 htrace hφ.1
  calc
    _ = ∫ z in ball (0 : ℂ) 1,
        (conj (smoothDiskCutoff R hR F z) * lap (smoothDiskCutoff R hR F) z +
          ∑ i : Fin 2,
            dirD (fun w => conj (smoothDiskCutoff R hR F w)) (coordDir i) z *
              dirD (smoothDiskCutoff R hR F) (coordDir i) z) := hgreen
    _ = ∫ z in ball (0 : ℂ) 1, ((2 * ‖deriv F z‖ ^ 2 : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change conj (smoothDiskCutoff R hR F z) * lap (smoothDiskCutoff R hR F) z +
        (∑ i : Fin 2, dirD (fun w => conj (smoothDiskCutoff R hR F w)) (coordDir i) z *
          dirD (smoothDiskCutoff R hR F) (coordDir i) z) = ((2 * ‖deriv F z‖ ^ 2 : ℝ) : ℂ)
      rw [localConformal_cutoff_lap_eq_zero hR F hFs hhol hz, mul_zero, zero_add]
      exact area_cutoff_gradient_density hR F hFs hhol hz
    _ = ((2 * (∫ z in ball (0 : ℂ) 1, ‖deriv F z‖ ^ 2) : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, integral_const_mul]
    _ = _ := by rw [localConformal_jacobian_integral_eq_volume F hhol hinj]

/-- The actual circle trace has the positive physical signed area. -/
theorem localConformal_circleTrace_signedArea {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ).im) =
        2 * (volume (F '' ball (0 : ℂ) 1)).toReal := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  let G : ℝ → ℂ := fun θ => conj (physicalCircleTrace F θ) *
    (-(Complex.I * deriv (physicalCircleTrace F) θ))
  have hi : IntervalIntegrable G volume 0 (2 * Real.pi) :=
    ((Complex.continuous_conj.comp hγ.continuous).mul
      ((continuous_const.mul hγ.continuous_deriv_one).neg)).intervalIntegrable _ _
  have hbd : doubleLayer (circleMap 0 1) (fun θ => conj (physicalCircleTrace F θ))
      (smoothDiskCutoff R hR F) = ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ := by
    unfold doubleLayer
    apply intervalIntegral.integral_congr
    intro θ _
    change conj (physicalCircleTrace F θ) *
      fderiv ℝ (smoothDiskCutoff R hR F) (circleMap 0 1 θ)
        (-(Complex.I * deriv (circleMap 0 1) θ)) =
      conj (physicalCircleTrace F θ) * (-(Complex.I * deriv (physicalCircleTrace F) θ))
    rw [area_cutoff_conormal hR F hFs hhol]
  have hre : (∫ θ in (0 : ℝ)..(2 * Real.pi), G θ).re =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ).im := by
    change Complex.reCLM (∫ θ in (0 : ℝ)..(2 * Real.pi), G θ) = _
    rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
    apply intervalIntegral.integral_congr
    intro θ _
    change (conj (physicalCircleTrace F θ) *
      (-(Complex.I * deriv (physicalCircleTrace F) θ))).re = _
    rw [show conj (physicalCircleTrace F θ) *
        (-(Complex.I * deriv (physicalCircleTrace F) θ)) =
      -(Complex.I * (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ)) by ring]
    simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, neg_neg]
  have he := congrArg Complex.re (localConformal_disk_green_energy hR F hFs hhol hinj)
  rw [hbd, hre, Complex.ofReal_re] at he
  exact he

/-- The exact normalized arclength map preserves the actual signed area. -/
theorem normalizedArcCurve_signedArea {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hnz : ∀ θ, deriv γ θ ≠ 0) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity (normalizedArcCurve hγ hper hnz) θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity γ θ := by
  obtain ⟨c, hτ, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  obtain ⟨K, hK⟩ := hτ.lipschitz
  let e := normalizedArcOrderIso hγ hper hnz
  have he : LipschitzWith K e := hK
  have hcomp : normalizedArcCurve hγ hper hnz ∘ e = γ :=
    funext fun θ => (normalizedArcCurve_factorization hγ hper hnz θ).symm
  have hchain := ae_deriv_comp (normalizedArcCurve_lipschitz hγ hper hnz) e.monotone he
  rw [hcomp] at hchain
  have hcv := integral_comp_orderIso he (normalizedArcOrderIso_zero hγ hper hnz)
    (normalizedArcOrderIso_endpoint hγ hper hnz)
    (signedAreaDensity (normalizedArcCurve hγ hper hnz))
  rw [hcv]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hchain] with θ hθ _
  have hpoint : normalizedArcCurve hγ hper hnz (e θ) = γ θ := congrFun hcomp θ
  simp only [signedAreaDensity]
  rw [hpoint, hθ, mul_left_comm, Complex.im_ofReal_mul]

/-- The constructed exact arclength curve is now a genuine positively
oriented physical boundary parameter, with all six fields proved. -/
theorem exists_localConformal_isBoundaryParam {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) :
    ∃ (β : ℝ → ℂ) (c : ℝ),
      IsBoundaryParam (F '' ball (0 : ℂ) 1) β ∧
      IsC1TraceReparam (normalizedArcReparam (physicalCircleTrace F)) c ∧
      ∀ θ, physicalCircleTrace F θ = β (normalizedArcReparam (physicalCircleTrace F) θ) := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  have him := localConformal_circleTrace_image_frontier hR F hFs hinj hL.1.1
  obtain ⟨c, hc, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hp hv
  refine ⟨normalizedArcCurve hγ hp hv, c, ?_, hc,
    normalizedArcCurve_factorization hγ hp hv⟩
  refine
    { lipschitz := ⟨_, normalizedArcCurve_lipschitz hγ hp hv⟩
      periodic := normalizedArcCurve_periodic hγ hp hv
      injOn := normalizedArcCurve_injOn hγ hp hv
        (physicalCircleTrace_injOn_of_closedDisk_inj F hinj)
      image := normalizedArcCurve_image_frontier hγ hp hv him
      const_speed := ⟨arcLen (physicalCircleTrace F) (2 * Real.pi) / (2 * Real.pi),
        div_pos (arcLen_period_pos_of_regular hγ hv) Real.two_pi_pos,
        Filter.Eventually.of_forall (normalizedArcCurve_speed hγ hp hv)⟩
      area := ?_ }
  exact (normalizedArcCurve_signedArea hγ hp hv).trans
    (localConformal_circleTrace_signedArea hR F hFs hhol (hinj.mono ball_subset_closedBall))

end PolyaNeumann

end
