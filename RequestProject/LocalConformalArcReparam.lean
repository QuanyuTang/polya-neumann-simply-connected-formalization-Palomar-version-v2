module

public import RequestProject.PhysicalHardySupport
public import RequestProject.LocalConformalInverse
public import RequestProject.TraceReparam
public import RequestProject.ArcLength
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Normalized arclength of the actual supplied circle trace

The map is exactly `τ θ = (2π / arcLen γ (2π)) * arcLen γ θ`.
For a regular periodic C¹ curve its speed has genuine positive lower and finite
upper bounds, derived from compactness on one period. The fundamental theorem
of calculus proves every pointwise derivative of τ. These facts construct the
existing `IsC1TraceReparam` witness, including its actual endpoints.

For supplied smooth conformal coordinates, the real boundary differential gives
the actual nonvanishing circle velocity. Holomorphicity is required only inside
the disk. No constant-speed hypothesis for the circle trace, boundary image or
orientation hypothesis, or synchronization with another parametrization is
assumed or concluded here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

/-- The precise normalized arclength change of parameter. -/
def normalizedArcReparam (γ : ℝ → ℂ) (θ : ℝ) : ℝ :=
  (2 * Real.pi / arcLen γ (2 * Real.pi)) * arcLen γ θ

@[simp] theorem normalizedArcReparam_zero (γ : ℝ → ℂ) :
    normalizedArcReparam γ 0 = 0 := by
  simp [normalizedArcReparam, arcLen]

/-- Actual pointwise FTC, including the endpoints and every other real input. -/
theorem hasDerivAt_normalizedArcReparam {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (θ : ℝ) :
    HasDerivAt (normalizedArcReparam γ)
      ((2 * Real.pi / arcLen γ (2 * Real.pi)) * ‖deriv γ θ‖) θ :=
  ((hγ.continuous_deriv_one.norm.integral_hasStrictDerivAt 0 θ).hasDerivAt).const_mul _

theorem deriv_normalizedArcReparam {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (θ : ℝ) :
    deriv (normalizedArcReparam γ) θ =
      (2 * Real.pi / arcLen γ (2 * Real.pi)) * ‖deriv γ θ‖ :=
  (hasDerivAt_normalizedArcReparam hγ θ).deriv

theorem contDiff_normalizedArcReparam {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    ContDiff ℝ 1 (normalizedArcReparam γ) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun θ => (hasDerivAt_normalizedArcReparam hγ θ).differentiableAt, ?_⟩
  have heq : deriv (normalizedArcReparam γ) =
      fun θ => (2 * Real.pi / arcLen γ (2 * Real.pi)) * ‖deriv γ θ‖ :=
    funext (deriv_normalizedArcReparam hγ)
  rw [heq]
  exact continuous_const.mul hγ.continuous_deriv_one.norm

/-- Compactness supplies true lower and upper velocity bounds on the whole
real line, using exact periodicity to extend one period's bounds. -/
theorem exists_regular_periodic_speed_bounds {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hnz : ∀ θ, deriv γ θ ≠ 0) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∀ θ, m ≤ ‖deriv γ θ‖ ∧ ‖deriv γ θ‖ ≤ M := by
  have hs : Continuous (fun θ => ‖deriv γ θ‖) := hγ.continuous_deriv_one.norm
  have hsp : Function.Periodic (fun θ => ‖deriv γ θ‖) (2 * Real.pi) := by
    intro θ
    change ‖deriv γ (θ + 2 * Real.pi)‖ = ‖deriv γ θ‖
    rw [deriv_periodic hper θ]
  obtain ⟨m, hm, hmlocal⟩ := isCompact_Icc.exists_forall_le' hs.continuousOn
    (fun θ (_ : θ ∈ Icc (0 : ℝ) (2 * Real.pi)) => norm_pos_iff.mpr (hnz θ))
  obtain ⟨θ₀, hθ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (2 * Real.pi)).Nonempty from
      ⟨0, le_refl 0, Real.two_pi_pos.le⟩) hs.continuousOn
  refine ⟨m, ‖deriv γ θ₀‖, hm, norm_nonneg _, fun θ => ?_⟩
  let θ' := toIcoMod Real.two_pi_pos 0 θ
  have hθ' : θ' ∈ Ico 0 (2 * Real.pi) := by
    simpa only [zero_add, θ'] using toIcoMod_mem_Ico Real.two_pi_pos 0 θ
  have heq : ‖deriv γ θ'‖ = ‖deriv γ θ‖ := by
    dsimp only [θ']
    rw [toIcoMod, hsp.sub_zsmul_eq]
  rw [← heq]
  exact ⟨hmlocal θ' (Ico_subset_Icc_self hθ'), hmax (Ico_subset_Icc_self hθ')⟩

theorem arcLen_period_pos_of_regular {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hnz : ∀ θ, deriv γ θ ≠ 0) :
    0 < arcLen γ (2 * Real.pi) := by
  apply intervalIntegral.integral_pos Real.two_pi_pos hγ.continuous_deriv_one.norm.continuousOn
    (fun _ _ => norm_nonneg _)
  exact ⟨0, ⟨le_refl 0, Real.two_pi_pos.le⟩, norm_pos_iff.mpr (hnz 0)⟩

theorem normalizedArcReparam_endpoint {γ : ℝ → ℂ}
    (hL : 0 < arcLen γ (2 * Real.pi)) :
    normalizedArcReparam γ (2 * Real.pi) = 2 * Real.pi := by
  unfold normalizedArcReparam
  exact div_mul_cancel₀ _ hL.ne'

theorem normalizedArcReparam_add_period {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hL : 0 < arcLen γ (2 * Real.pi)) (θ : ℝ) :
    normalizedArcReparam γ (θ + 2 * Real.pi) =
      normalizedArcReparam γ θ + 2 * Real.pi := by
  simp only [normalizedArcReparam]
  rw [arcLen_add_period hK hper, mul_add, div_mul_cancel₀ _ hL.ne']

/-- Construction of all seven fields of the genuine trace-reparametrization
structure. The returned lower bound also holds pointwise on the whole line. -/
theorem exists_isC1TraceReparam_normalizedArc {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hnz : ∀ θ, deriv γ θ ≠ 0) :
    ∃ c : ℝ, IsC1TraceReparam (normalizedArcReparam γ) c ∧
      (∀ θ, c ≤ deriv (normalizedArcReparam γ) θ) ∧
      (∀ θ, normalizedArcReparam γ (θ + 2 * Real.pi) =
        normalizedArcReparam γ θ + 2 * Real.pi) := by
  obtain ⟨m, M, hm, hM, hbounds⟩ := exists_regular_periodic_speed_bounds hγ hper hnz
  have hγlip : LipschitzWith (Real.toNNReal M) γ := by
    apply lipschitzWith_of_nnnorm_deriv_le hγ.differentiable_one
    intro θ
    apply NNReal.coe_le_coe.mp
    change ‖deriv γ θ‖ ≤ (Real.toNNReal M : ℝ)
    rw [Real.coe_toNNReal _ hM]
    exact (hbounds θ).2
  have hL := arcLen_period_pos_of_regular hγ hnz
  let a := 2 * Real.pi / arcLen γ (2 * Real.pi)
  have ha : 0 < a := div_pos Real.two_pi_pos hL
  have hτlip : LipschitzWith (Real.toNNReal a * Real.toNNReal M)
      (normalizedArcReparam γ) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := (arcLen_lipschitz hγlip).dist_le_mul x y
    rw [Real.dist_eq] at h ⊢
    change |a * arcLen γ x - a * arcLen γ y| ≤ _
    rw [← mul_sub, abs_mul, abs_of_pos ha, NNReal.coe_mul,
      Real.coe_toNNReal _ ha.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left h ha.le
  have hlower (θ : ℝ) : a * m ≤ deriv (normalizedArcReparam γ) θ := by
    rw [deriv_normalizedArcReparam hγ]
    exact mul_le_mul_of_nonneg_left (hbounds θ).1 ha.le
  have hsm : StrictMono (normalizedArcReparam γ) :=
    strictMono_of_deriv_pos fun θ => (mul_pos ha hm).trans_le (hlower θ)
  refine ⟨a * m, ?_, hlower, normalizedArcReparam_add_period hγlip hper hL⟩
  exact ⟨hsm.monotone, ⟨_, hτlip⟩, contDiff_normalizedArcReparam hγ,
    normalizedArcReparam_zero γ, normalizedArcReparam_endpoint hL,
    mul_pos ha hm, Eventually.of_forall hlower⟩

section SuppliedCoordinates

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))

include hR hFs hhol in
/-- The actual real boundary chain rule, with complex linearity extended from
the interior to the closed disk by the existing smooth-coordinate theorem. -/
theorem localConformal_circleTrace_hasDerivAt (θ : ℝ) :
    HasDerivAt (physicalCircleTrace F)
      (fderiv ℝ F (circleMap 0 1 θ) 1 * (circleMap 0 1 θ * Complex.I)) θ := by
  have hz : circleMap 0 1 θ ∈ closedBall (0 : ℂ) 1 :=
    circleMap_mem_closedBall 0 (by norm_num) θ
  have hfd : HasFDerivAt F (fderiv ℝ F (circleMap 0 1 θ)) (circleMap 0 1 θ) :=
    ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt
      (by simp)).hasFDerivAt
  have hd := hfd.comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ)
  rw [localConformal_fderiv_closedDisk hR F hFs hhol hz] at hd
  exact hd

include hR hFs hhol in
theorem localConformal_circleTrace_deriv (θ : ℝ) :
    deriv (physicalCircleTrace F) θ =
      fderiv ℝ F (circleMap 0 1 θ) 1 * (circleMap 0 1 θ * Complex.I) :=
  (localConformal_circleTrace_hasDerivAt hR F hFs hhol θ).deriv

include hR hFs hhol in
theorem localConformal_circleTrace_speed (θ : ℝ) :
    ‖deriv (physicalCircleTrace F) θ‖ = ‖fderiv ℝ F (circleMap 0 1 θ) 1‖ := by
  rw [localConformal_circleTrace_deriv hR F hFs hhol]
  simp only [norm_mul, norm_circleMap_zero, abs_one, Complex.norm_I, mul_one]

include hR hFs hhol in
theorem localConformal_circleTrace_deriv_ne_zero
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) (θ : ℝ) :
    deriv (physicalCircleTrace F) θ ≠ 0 := by
  rw [localConformal_circleTrace_deriv hR F hFs hhol]
  exact mul_ne_zero (hnz _ (circleMap_mem_sphere 0 (by norm_num) θ))
    (mul_ne_zero (circleMap_ne_center (by norm_num)) Complex.I_ne_zero)

include hR hFs hhol in
/-- The exact normalized arclength map for the actual nonconstant-speed circle
trace satisfies the genuine C¹ trace-reparametrization predicate. -/
theorem exists_localConformalArcReparam
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) :
    ∃ c : ℝ, IsC1TraceReparam (normalizedArcReparam (physicalCircleTrace F)) c ∧
      (∀ θ, c ≤ deriv (normalizedArcReparam (physicalCircleTrace F)) θ) ∧
      (∀ θ, normalizedArcReparam (physicalCircleTrace F) (θ + 2 * Real.pi) =
        normalizedArcReparam (physicalCircleTrace F) θ + 2 * Real.pi) :=
  exists_isC1TraceReparam_normalizedArc
    (contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp)))
    (physicalCircleTrace_periodic F)
    (localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz)

end SuppliedCoordinates

end PolyaNeumann

end
