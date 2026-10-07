module

public import RequestProject.LocalConformalArcReparam
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Exact factorization through normalized arclength

The precise `normalizedArcReparam` is shown to be an increasing order
isomorphism of the real line. Its period increment and fixed endpoints prove
surjectivity. Composing the actual curve with its genuine inverse constructs
the constant-speed curve and proves the exact factorization.

Nonvanishing velocity gives a pointwise inverse derivative, hence pointwise
constant speed, rather than only an almost-everywhere speed statement. The
supplied-coordinate corollary preserves the actual circle image and proves
interval injectivity from closed-disk injectivity. Boundary orientation and
matching to an arbitrary different parametrization remain separate questions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

theorem normalizedArcReparam_strictMono {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hnz : ∀ θ, deriv γ θ ≠ 0) : StrictMono (normalizedArcReparam γ) := by
  apply strictMono_of_deriv_pos
  intro θ
  rw [deriv_normalizedArcReparam hγ]
  exact mul_pos (div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hγ hnz))
    (norm_pos_iff.mpr (hnz θ))

/-- The period increment prevents either end of the normalized arclength map
from remaining bounded, and continuity then proves actual surjectivity. -/
theorem normalizedArcReparam_surjective {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hnz : ∀ θ, deriv γ θ ≠ 0) : Function.Surjective (normalizedArcReparam γ) := by
  obtain ⟨c, hτ, _, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  have hbound : ∀ θ, |normalizedArcReparam γ θ - θ| ≤ 2 * Real.pi := by
    refine abs_le_of_periodic
      (g := fun θ => normalizedArcReparam γ θ - θ) (fun θ => ?_) (fun x hx => ?_)
    · simp only
      rw [hperiod]
      ring
    · have h0 := hτ.monotone hx.1
      have h2 := hτ.monotone hx.2.le
      rw [hτ.zero] at h0
      rw [hτ.endpoint] at h2
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
  refine hτ.continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun θ => ?_)
      (tendsto_atTop_add_const_right _ (-(2 * Real.pi)) tendsto_id)
    have h := hbound θ
    rw [abs_le] at h
    simp only [id]
    linarith
  · refine tendsto_atBot_mono (fun θ => ?_)
      (tendsto_atBot_add_const_right _ (2 * Real.pi) tendsto_id)
    have h := hbound θ
    rw [abs_le] at h
    simp only [id]
    linarith

section RegularCurve

variable {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hnz : ∀ θ, deriv γ θ ≠ 0)

/-- The genuine increasing order isomorphism whose forward map is exactly τ. -/
def normalizedArcOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (normalizedArcReparam γ)
    (normalizedArcReparam_strictMono hγ hnz) (normalizedArcReparam_surjective hγ hper hnz)

@[simp] theorem normalizedArcOrderIso_apply (θ : ℝ) :
    normalizedArcOrderIso hγ hper hnz θ = normalizedArcReparam γ θ := rfl

@[simp] theorem normalizedArcOrderIso_zero : normalizedArcOrderIso hγ hper hnz 0 = 0 :=
  normalizedArcReparam_zero γ

@[simp] theorem normalizedArcOrderIso_endpoint :
    normalizedArcOrderIso hγ hper hnz (2 * Real.pi) = 2 * Real.pi :=
  normalizedArcReparam_endpoint (arcLen_period_pos_of_regular hγ hnz)

@[simp] theorem normalizedArcOrderIso_symm_zero :
    (normalizedArcOrderIso hγ hper hnz).symm 0 = 0 := by
  apply (normalizedArcOrderIso hγ hper hnz).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_zero]

@[simp] theorem normalizedArcOrderIso_symm_endpoint :
    (normalizedArcOrderIso hγ hper hnz).symm (2 * Real.pi) = 2 * Real.pi := by
  apply (normalizedArcOrderIso hγ hper hnz).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_endpoint]

theorem normalizedArcOrderIso_add_period (θ : ℝ) :
    normalizedArcOrderIso hγ hper hnz (θ + 2 * Real.pi) =
      normalizedArcOrderIso hγ hper hnz θ + 2 * Real.pi := by
  obtain ⟨c, _, _, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  exact hperiod θ

theorem normalizedArcOrderIso_symm_add_period (t : ℝ) :
    (normalizedArcOrderIso hγ hper hnz).symm (t + 2 * Real.pi) =
      (normalizedArcOrderIso hγ hper hnz).symm t + 2 * Real.pi := by
  apply (normalizedArcOrderIso hγ hper hnz).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_add_period,
    OrderIso.apply_symm_apply]

/-- The actual curve in its normalized arclength parameter. -/
def normalizedArcCurve (t : ℝ) : ℂ := γ ((normalizedArcOrderIso hγ hper hnz).symm t)

/-- Exact recovery of the original curve with the precise normalized τ. -/
theorem normalizedArcCurve_factorization (θ : ℝ) :
    γ θ = normalizedArcCurve hγ hper hnz (normalizedArcReparam γ θ) := by
  change γ θ = γ ((normalizedArcOrderIso hγ hper hnz).symm
    (normalizedArcOrderIso hγ hper hnz θ))
  rw [OrderIso.symm_apply_apply]

theorem normalizedArcCurve_periodic :
    Function.Periodic (normalizedArcCurve hγ hper hnz) (2 * Real.pi) := by
  intro t
  simp only [normalizedArcCurve, normalizedArcOrderIso_symm_add_period]
  exact hper _

/-- The true derivative of the inverse map, obtained from its proved inverse
identity and continuity, not assumed as an auxiliary transfer formula. -/
theorem normalizedArcOrderIso_symm_hasDerivAt (t : ℝ) :
    HasDerivAt (normalizedArcOrderIso hγ hper hnz).symm
      (((2 * Real.pi / arcLen γ (2 * Real.pi)) *
        ‖deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)‖)⁻¹) t := by
  have hL := arcLen_period_pos_of_regular hγ hnz
  have hpos : 0 < (2 * Real.pi / arcLen γ (2 * Real.pi)) *
      ‖deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)‖ :=
    mul_pos (div_pos Real.two_pi_pos hL) (norm_pos_iff.mpr (hnz _))
  apply HasDerivAt.of_local_left_inverse
    (normalizedArcOrderIso hγ hper hnz).symm.continuous.continuousAt
    (hasDerivAt_normalizedArcReparam hγ _) hpos.ne'
  exact Eventually.of_forall (normalizedArcOrderIso hγ hper hnz).apply_symm_apply

theorem normalizedArcCurve_hasDerivAt (t : ℝ) :
    HasDerivAt (normalizedArcCurve hγ hper hnz)
      ((((2 * Real.pi / arcLen γ (2 * Real.pi)) *
        ‖deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)‖)⁻¹) •
        deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)) t :=
  (hγ.differentiable_one _).hasDerivAt.scomp t
    (normalizedArcOrderIso_symm_hasDerivAt hγ hper hnz t)

/-- Constant speed holds at every parameter because the initial velocity is
nonzero everywhere; this is stronger than the usual almost-everywhere statement. -/
theorem normalizedArcCurve_speed (t : ℝ) :
    ‖deriv (normalizedArcCurve hγ hper hnz) t‖ = arcLen γ (2 * Real.pi) / (2 * Real.pi) := by
  have hL := arcLen_period_pos_of_regular hγ hnz
  have hv : 0 < ‖deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)‖ :=
    norm_pos_iff.mpr (hnz _)
  have hp : 0 < ((2 * Real.pi / arcLen γ (2 * Real.pi)) *
      ‖deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)‖)⁻¹ :=
    inv_pos.mpr (mul_pos (div_pos Real.two_pi_pos hL) hv)
  rw [(normalizedArcCurve_hasDerivAt hγ hper hnz t).deriv, norm_smul,
    Real.norm_eq_abs, abs_of_pos hp]
  field_simp [hL.ne', hv.ne', Real.two_pi_pos.ne']

theorem normalizedArcCurve_lipschitz :
    LipschitzWith (Real.toNNReal (arcLen γ (2 * Real.pi) / (2 * Real.pi)))
      (normalizedArcCurve hγ hper hnz) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (normalizedArcCurve_hasDerivAt hγ hper hnz t).differentiableAt)
  intro t
  apply NNReal.coe_le_coe.mp
  change ‖deriv (normalizedArcCurve hγ hper hnz) t‖ ≤
    (Real.toNNReal (arcLen γ (2 * Real.pi) / (2 * Real.pi)) : ℝ)
  rw [Real.coe_toNNReal _ (div_pos (arcLen_period_pos_of_regular hγ hnz) Real.two_pi_pos).le]
  exact le_of_eq (normalizedArcCurve_speed hγ hper hnz t)

theorem normalizedArcCurve_image_Icc :
    normalizedArcCurve hγ hper hnz '' Icc 0 (2 * Real.pi) = γ '' Icc 0 (2 * Real.pi) := by
  change (γ ∘ (normalizedArcOrderIso hγ hper hnz).symm) '' Icc 0 (2 * Real.pi) = _
  rw [image_comp, OrderIso.image_Icc, normalizedArcOrderIso_symm_zero,
    normalizedArcOrderIso_symm_endpoint]

theorem normalizedArcCurve_injOn (hinj : InjOn γ (Ico 0 (2 * Real.pi))) :
    InjOn (normalizedArcCurve hγ hper hnz) (Ico 0 (2 * Real.pi)) := by
  have hm : ∀ x ∈ Ico 0 (2 * Real.pi),
      (normalizedArcOrderIso hγ hper hnz).symm x ∈ Ico 0 (2 * Real.pi) := by
    intro x hx
    constructor
    · simpa only [normalizedArcOrderIso_symm_zero] using
        (normalizedArcOrderIso hγ hper hnz).symm.monotone hx.1
    · simpa only [normalizedArcOrderIso_symm_endpoint] using
        (normalizedArcOrderIso hγ hper hnz).symm.strictMono hx.2
  intro x hx y hy hxy
  exact (normalizedArcOrderIso hγ hper hnz).symm.injective (hinj (hm x hx) (hm y hy) hxy)

end RegularCurve

/-- Closed-disk injectivity of the actual supplied F proves circle-trace
injectivity on one half-open period by genuine circle-map injectivity. -/
theorem physicalCircleTrace_injOn_of_closedDisk_inj (F : ℂ → ℂ)
    (hinj : InjOn F (closedBall (0 : ℂ) 1)) :
    InjOn (physicalCircleTrace F) (Ico 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  have hz := hinj (circleMap_mem_closedBall 0 (by norm_num) x)
    (circleMap_mem_closedBall 0 (by norm_num) y) hxy
  exact injOn_circleMap_of_abs_sub_le' (by norm_num : (1 : ℝ) ≠ 0)
    (by simp : (2 * Real.pi) - 0 ≤ 2 * Real.pi) hx hy hz

/-- Exact supplied-coordinate arclength factorization. Every returned property
concerns the actual trace and its proved normalized τ; no boundary image or
orientation is supplied as a substitute for a proof. -/
theorem exists_localConformalArcFactorization {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) :
    ∃ (β : ℝ → ℂ) (c : ℝ),
      IsC1TraceReparam (normalizedArcReparam (physicalCircleTrace F)) c ∧
      (∀ θ, physicalCircleTrace F θ = β (normalizedArcReparam (physicalCircleTrace F) θ)) ∧
      Function.Periodic β (2 * Real.pi) ∧
      LipschitzWith (Real.toNNReal
        (arcLen (physicalCircleTrace F) (2 * Real.pi) / (2 * Real.pi))) β ∧
      (∀ θ, ‖deriv β θ‖ = arcLen (physicalCircleTrace F) (2 * Real.pi) / (2 * Real.pi)) ∧
      InjOn β (Ico 0 (2 * Real.pi)) ∧
      β '' Icc 0 (2 * Real.pi) = physicalCircleTrace F '' Icc 0 (2 * Real.pi) := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  obtain ⟨c, hc, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hp hv
  refine ⟨normalizedArcCurve hγ hp hv, c, hc,
    normalizedArcCurve_factorization hγ hp hv, normalizedArcCurve_periodic hγ hp hv,
    normalizedArcCurve_lipschitz hγ hp hv, normalizedArcCurve_speed hγ hp hv,
    normalizedArcCurve_injOn hγ hp hv (physicalCircleTrace_injOn_of_closedDisk_inj F hinj),
    normalizedArcCurve_image_Icc hγ hp hv⟩

end PolyaNeumann

end
