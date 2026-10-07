module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import RequestProject.LocalSmoothInverse
public import RequestProject.LocalConformalPullback

/-!
# The actual inverse of given closed-disk conformal coordinates

Holomorphicity in the open disk and smoothness near its closure imply
complex linearity of the real differential even on the boundary. With
closed-disk injectivity and a nonzero differential this gives a smooth
inverse on a neighborhood of the closed image. No global plane
homeomorphism is required. Existence of the initial conformal map remains
a separate obligation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped Topology

theorem localConformal_fderiv_closedDisk {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (v : ℂ) :
    fderiv ℝ F z v = fderiv ℝ F z 1 * v := by
  have hc := hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have heq : EqOn (fun w => fderiv ℝ F w v)
      (fun w => fderiv ℝ F w 1 * v) (ball (0 : ℂ) 1) := by
    intro w hw
    have hfd (a : ℂ) : fderiv ℝ F w a = deriv F w * a := by
      rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hw)).fderiv_restrictScalars ℝ]
      change fderiv ℂ F w a = _
      exact fderiv_eq_deriv_mul
    dsimp only
    rw [hfd v, hfd 1, mul_one]
  exact heq.of_subset_closure
    ((hc.clm_apply continuousOn_const).mono (closedBall_subset_ball hR))
    (((hc.clm_apply continuousOn_const).mul continuousOn_const).mono
      (closedBall_subset_ball hR)) ball_subset_closedBall
    (by simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
      (subset_rfl : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1)) hz

theorem exists_localConformalInverse {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ) = F ∧
      closedBall (0 : ℂ) 1 ⊆ e.source ∧ e.source ⊆ ball (0 : ℂ) R ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  apply exists_localSmoothInverse_of_compact_differential
    (isCompact_closedBall (0 : ℂ) 1) isOpen_ball (closedBall_subset_ball hR)
    F hFs hinj
  intro z hz
  let D : ℂ ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ F z 1)).restrictScalars ℝ)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ F z 1)⁻¹).restrictScalars ℝ)
      (fun x => by
        change (x * fderiv ℝ F z 1) * (fderiv ℝ F z 1)⁻¹ = x
        rw [mul_assoc, mul_inv_cancel₀ (hnz z hz), mul_one])
      (fun x => by
        change (x * (fderiv ℝ F z 1)⁻¹) * fderiv ℝ F z 1 = x
        rw [mul_assoc, inv_mul_cancel₀ (hnz z hz), mul_one])
  have hDeq : (D : ℂ →L[ℝ] ℂ) = fderiv ℝ F z := by
    apply ContinuousLinearMap.ext
    intro v
    change v * fderiv ℝ F z 1 = fderiv ℝ F z v
    rw [localConformal_fderiv_closedDisk hR F hFs hhol hz v]
    exact mul_comm _ _
  refine ⟨D, ?_⟩
  rw [hDeq]
  have hsd := hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))
  exact (hsd.differentiableAt (by simp)).hasFDerivAt

theorem localConformalInverse_holomorphic (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source) :
    DifferentiableOn ℂ e.symm (F '' ball (0 : ℂ) 1) := by
  rintro w ⟨z, hz, rfl⟩
  have hes : e.symm (F z) = z := by
    rw [← he]
    exact e.left_inv (hsource (ball_subset_closedBall hz))
  have hFd := (hhol.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hd1 : fderiv ℝ F z 1 = deriv F z := by
    rw [hFd.differentiableAt.fderiv_restrictScalars ℝ]
    change fderiv ℂ F z 1 = _
    rw [fderiv_eq_deriv_mul, mul_one]
  have hderiv : deriv F z ≠ 0 := by
    rw [← hd1]
    exact hnz z (ball_subset_closedBall hz)
  have htarget : F z ∈ e.target := by
    rw [← he]
    exact e.mapsTo (hsource (ball_subset_closedBall hz))
  have hfd : HasDerivAt e (deriv F z) (e.symm (F z)) := by
    rw [hes, he]
    exact hFd
  exact (e.hasDerivAt_symm htarget hderiv hfd).differentiableAt.differentiableWithinAt

end PolyaNeumann

end
