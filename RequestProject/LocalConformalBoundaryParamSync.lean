module

public import RequestProject.SmoothBoundaryParamUniqueness
public import RequestProject.LocalConformalAreaOrientation
public import RequestProject.LocalConformalRotation

/-!
# Actual supplied coordinates synchronized with the original boundary

The canonical normalized-arclength curve is proved C¹ from its actual inverse
derivative.  Its actual physical boundary predicate and the proved uniqueness
of constant-speed boundary parameters then select a genuine circle rotation.
Rebasing the genuine arclength lift synchronizes the rotated supplied map with
the original physical boundary parameter, including both fixed endpoints.

Every rotated coordinate property follows from the original supplied map and
its actual smooth inverse.  This constructs no initial conformal map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology Real

/-- The canonical arc curve is genuinely C¹: its previously proved inverse
derivative is continuous because the original speed is continuous and nonzero. -/
theorem normalizedArcCurve_contDiff {Γ : ℝ → ℂ}
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ (2 * Real.pi))
    (hnz : ∀ θ, deriv Γ θ ≠ 0) :
    ContDiff ℝ 1 (normalizedArcCurve hΓ hper hnz) := by
  let σ : ℝ → ℝ := (normalizedArcOrderIso hΓ hper hnz).symm
  let a : ℝ := 2 * Real.pi / arcLen Γ (2 * Real.pi)
  have ha : 0 < a := div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hΓ hnz)
  have hσ : Continuous σ := (normalizedArcOrderIso hΓ hper hnz).symm.continuous
  have hv : Continuous (fun t : ℝ => deriv Γ (σ t)) :=
    hΓ.continuous_deriv_one.comp hσ
  have hd : Continuous (fun t : ℝ => a * ‖deriv Γ (σ t)‖) := continuous_const.mul hv.norm
  have hdne (t : ℝ) : a * ‖deriv Γ (σ t)‖ ≠ 0 :=
    (mul_pos ha (norm_pos_iff.mpr (hnz (σ t)))).ne'
  have hformula : deriv (normalizedArcCurve hΓ hper hnz) =
      fun t : ℝ => (a * ‖deriv Γ (σ t)‖)⁻¹ • deriv Γ (σ t) :=
    funext (fun t => (normalizedArcCurve_hasDerivAt hΓ hper hnz t).deriv)
  refine contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩
  · exact fun t => (normalizedArcCurve_hasDerivAt hΓ hper hnz t).differentiableAt
  · rw [hformula]
    exact (hd.inv₀ hdne).smul hv

/-- The canonical arc curve has a genuinely nonzero velocity everywhere. -/
theorem normalizedArcCurve_deriv_ne_zero {Γ : ℝ → ℂ}
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ (2 * Real.pi))
    (hnz : ∀ θ, deriv Γ θ ≠ 0) (t : ℝ) :
    deriv (normalizedArcCurve hΓ hper hnz) t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [normalizedArcCurve_speed hΓ hper hnz]
  exact div_pos (arcLen_period_pos_of_regular hΓ hnz) Real.two_pi_pos

/-- The actual canonical arc parameter, not merely an existential reference,
is a physical boundary parameter.  Its identification with the proved reference
uses surjectivity of the actual normalized-arclength map. -/
theorem localConformal_normalizedArcCurve_isBoundaryParam
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) :
    let hΓ : ContDiff ℝ 1 (physicalCircleTrace F) :=
      contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
    let hp := physicalCircleTrace_periodic F
    let hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
    IsBoundaryParam (F '' ball (0 : ℂ) 1) (normalizedArcCurve hΓ hp hv) := by
  dsimp only
  let hΓ : ContDiff ℝ 1 (physicalCircleTrace F) :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  let hp := physicalCircleTrace_periodic F
  let hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  obtain ⟨β, c, hβ, _, hfactor⟩ :=
    exists_localConformal_isBoundaryParam hR F hFs hhol hinj hnz hL
  have heq : β = normalizedArcCurve hΓ hp hv := by
    funext t
    obtain ⟨θ, hθ⟩ := normalizedArcReparam_surjective hΓ hp hv t
    calc
      β t = β (normalizedArcReparam (physicalCircleTrace F) θ) := by rw [hθ]
      _ = physicalCircleTrace F θ := (hfactor θ).symm
      _ = normalizedArcCurve hΓ hp hv
          (normalizedArcReparam (physicalCircleTrace F) θ) :=
        normalizedArcCurve_factorization hΓ hp hv θ
      _ = normalizedArcCurve hΓ hp hv t := by rw [hθ]
  rw [heq] at hβ
  exact hβ

/-- Given the proved canonical physical arc parameter, select the actual
circle phase and the genuine endpoint-preserving C¹ arclength lift for any
original physical boundary parameter. -/
theorem exists_normalizedArc_origin_sync {Ω : Set ℂ} {Γ γ : ℝ → ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ (2 * Real.pi))
    (hnz : ∀ θ, deriv Γ θ ≠ 0)
    (hβ : IsBoundaryParam Ω (normalizedArcCurve hΓ hper hnz))
    (hγ : IsBoundaryParam Ω γ) :
    ∃ φ ∈ Icc 0 (2 * Real.pi), ∃ c : ℝ,
      IsC1TraceReparam (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam Γ) φ (θ + 2 * Real.pi) =
          localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ + 2 * Real.pi) ∧
      (∀ θ : ℝ, Γ (θ + φ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ)) := by
  obtain ⟨t, ht, hshift⟩ := exists_boundaryParam_shift_of_bounded_domain hb hΩ hβ
    (normalizedArcCurve_contDiff hΓ hper hnz)
    (normalizedArcCurve_deriv_ne_zero hΓ hper hnz) hγ
  let φ : ℝ := (normalizedArcOrderIso hΓ hper hnz).symm t
  have hφ : φ ∈ Icc 0 (2 * Real.pi) := by
    constructor
    · simpa only [normalizedArcOrderIso_symm_zero] using
        (normalizedArcOrderIso hΓ hper hnz).symm.monotone ht.1
    · simpa only [normalizedArcOrderIso_symm_endpoint] using
        (normalizedArcOrderIso hΓ hper hnz).symm.monotone ht.2
  have hφval : normalizedArcReparam Γ φ = t :=
    (normalizedArcOrderIso hΓ hper hnz).apply_symm_apply t
  obtain ⟨c, hτ, _, hτper⟩ := exists_isC1TraceReparam_normalizedArc hΓ hper hnz
  refine ⟨φ, hφ, c, localConformalRotateTraceReparam_isC1 hτ hτper φ,
    localConformalRotateTraceReparam_add_period hτper φ, ?_⟩
  intro θ
  calc
    Γ (θ + φ) = normalizedArcCurve hΓ hper hnz (normalizedArcReparam Γ (θ + φ)) :=
      normalizedArcCurve_factorization hΓ hper hnz (θ + φ)
    _ = normalizedArcCurve hΓ hper hnz
        (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ + t) := by
      congr 1
      simp only [localConformalRotateTraceReparam, hφval, sub_add_cancel]
    _ = γ (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ) :=
      (hshift _).symm

/-- Closed-disk injectivity follows from the genuine supplied inverse, so no
additional boundary injectivity premise is needed by synchronization. -/
theorem localConformal_closedDisk_inj_of_supplied_inverse
    (F : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source) :
    InjOn F (closedBall (0 : ℂ) 1) := by
  intro z hz w hw hzw
  have hzw' : e z = e w := by simpa only [he] using hzw
  have h := congrArg (fun x : ℂ => e.symm x) hzw'
  change e.symm (e z) = e.symm (e w) at h
  rw [e.left_inv (hsource hz), e.left_inv (hsource hw)] at h
  exact h

/-- Actual rotation of supplied coordinates synchronizes their genuine
circle trace with the original physical boundary parameter. -/
theorem exists_localConformal_boundaryParam_sync
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ) :
    ∃ φ ∈ Icc 0 (2 * Real.pi), ∃ c : ℝ,
      IsC1TraceReparam
        (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ
            (θ + 2 * Real.pi) =
          localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ +
            2 * Real.pi) ∧
      (∀ θ : ℝ, localConformalRotate F φ (circleMap 0 1 θ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ)) := by
  have hinj := localConformal_closedDisk_inj_of_supplied_inverse F e he hsource
  have hnzclosed := localConformalRotation_closedDifferential_ne_zero_of_inverse
    hR F hFs e he hsource hes
  have hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0 :=
    fun z hz => hnzclosed z (sphere_subset_closedBall hz)
  have hΓ : ContDiff ℝ 1 (physicalCircleTrace F) :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  have hβ := localConformal_normalizedArcCurve_isBoundaryParam hR F hFs hhol hinj hnz hL
  obtain ⟨φ, hφ, c, hτ, hτper, hcoord⟩ :=
    exists_normalizedArc_origin_sync hb hL.1 hΓ hp hv hβ hγ
  refine ⟨φ, hφ, c, hτ, hτper, ?_⟩
  intro θ
  calc
    localConformalRotate F φ (circleMap 0 1 θ) =
        physicalCircleTrace (localConformalRotate F φ) θ := rfl
    _ = physicalCircleTrace F (θ + φ) := physicalCircleTrace_localConformalRotate F φ θ
    _ = _ := hcoord θ

/-- Genuine C¹ regularity and periodicity give a finite global speed bound,
and hence a genuine Lipschitz constant for the actual circle trace. -/
theorem exists_regularPeriodicCurve_lipschitz {Γ : ℝ → ℂ}
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ (2 * Real.pi))
    (hnz : ∀ θ, deriv Γ θ ≠ 0) : ∃ L : NNReal, LipschitzWith L Γ := by
  obtain ⟨m, M, hm, hM, hbounds⟩ := exists_regular_periodic_speed_bounds hΓ hper hnz
  refine ⟨Real.toNNReal M, ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le hΓ.differentiable_one
  intro θ
  apply NNReal.coe_le_coe.mp
  change ‖deriv Γ θ‖ ≤ (Real.toNNReal M : ℝ)
  rw [Real.coe_toNNReal _ hM]
  exact (hbounds θ).2

/-- The complete actual supplied-coordinate package at the original physical
boundary origin.  The displayed maps are genuine rotations of the original
map and its genuine inverse; the original constants `C` and `K` are retained.
This theorem selects no nonzero transport cut. -/
theorem exists_localConformal_original_boundary_coordinates
    {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ) :
    ∃ φ ∈ Icc 0 (2 * Real.pi), ∃ c : ℝ, ∃ L : NNReal,
      (localConformalRotate F φ '' ball (0 : ℂ) 1 = F '' ball (0 : ℂ) 1) ∧
      (localConformalRotate F φ '' closedBall (0 : ℂ) 1 = F '' closedBall (0 : ℂ) 1) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (localConformalRotate F φ) (ball (0 : ℂ) R) ∧
      Bornology.IsBounded (localConformalRotate F φ '' ball (0 : ℂ) 1) ∧
      IsLipschitzDomain (localConformalRotate F φ '' ball (0 : ℂ) 1) ∧
      DifferentiableOn ℂ (localConformalRotate F φ) (ball (0 : ℂ) 1) ∧
      InjOn (localConformalRotate F φ) (closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv (localConformalRotate F φ) z‖ ^ 2) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (localConformalRotate F φ) z 1‖ ≤ K) ∧
      ((localConformalRotatePartialHomeomorph e φ : ℂ → ℂ) = localConformalRotate F φ) ∧
      (closedBall (0 : ℂ) 1 ⊆ (localConformalRotatePartialHomeomorph e φ).source) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (localConformalRotatePartialHomeomorph e φ).symm
        (localConformalRotatePartialHomeomorph e φ).target ∧
      IsBoundaryParam (localConformalRotate F φ '' ball (0 : ℂ) 1) γ ∧
      IsC1TraceReparam
        (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ
            (θ + 2 * Real.pi) =
          localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ +
            2 * Real.pi) ∧
      (∀ θ : ℝ, localConformalRotate F φ (circleMap 0 1 θ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ)) ∧
      LipschitzWith L (physicalCircleTrace (localConformalRotate F φ)) ∧
      localConformalRotate F φ 1 = γ 0 := by
  obtain ⟨φ, hφ, c, hτ, hτper, hcoord⟩ :=
    exists_localConformal_boundaryParam_sync hR F hFs hb hL hhol e he hsource hes hγ
  have hnzclosed := localConformalRotation_closedDifferential_ne_zero_of_inverse
    hR F hFs e he hsource hes
  have hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0 :=
    fun z hz => hnzclosed z (sphere_subset_closedBall hz)
  have hΓ : ContDiff ℝ 1 (physicalCircleTrace F) :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  obtain ⟨L, hΓLip⟩ := exists_regularPeriodicCurve_lipschitz hΓ hp hv
  have himage := localConformalRotate_image_ball F φ 1
  have hbφ : Bornology.IsBounded (localConformalRotate F φ '' ball (0 : ℂ) 1) := by
    rw [himage]
    exact hb
  have hLφ : IsLipschitzDomain (localConformalRotate F φ '' ball (0 : ℂ) 1) := by
    rw [himage]
    exact hL
  have hγφ : IsBoundaryParam (localConformalRotate F φ '' ball (0 : ℂ) 1) γ := by
    rw [himage]
    exact hγ
  refine ⟨φ, hφ, c, L, himage, localConformalRotate_image_closedBall F φ 1,
    localConformalRotate_contDiffOn hFs φ, hbφ, hLφ,
    localConformalRotate_holomorphic hhol φ,
    localConformalRotate_injOn_closedBall
      (localConformal_closedDisk_inj_of_supplied_inverse F e he hsource) φ,
    localConformalRotate_lower_deriv_bound hhol hC φ,
    localConformalRotate_upper_differential_bound hR F hFs hhol hK φ,
    localConformalRotatePartialHomeomorph_coe e he φ,
    localConformalRotatePartialHomeomorph_closedDisk_source e hsource φ,
    localConformalRotatePartialHomeomorph_smoothInverse e hes φ,
    hγφ, hτ, hτper, hcoord,
    physicalCircleTrace_localConformalRotate_lipschitz hΓLip φ, ?_⟩
  have hc0 : circleMap (0 : ℂ) 1 (0 : ℝ) = 1 := by simp [circleMap]
  simpa only [hc0, hτ.zero] using hcoord 0

end PolyaNeumann

end
