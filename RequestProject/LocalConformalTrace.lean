module

public import RequestProject.LocalConformalPullback
public import RequestProject.DiskHalfTrace
public import RequestProject.TraceReparam

/-!
# Physical half-order traces in local conformal coordinates

The disk estimates and the proved H¹ pullback construct the half-order
trace for a given local smooth conformal coordinate map. Its ordinary
boundary values agree with `f(F(exp(iθ)))` on all smooth restrictions.
When these coordinates are a C¹ reparametrization of the physical
boundary parameter, uniqueness identifies the constructed ordinary trace
with the previously constructed reparametrized physical trace.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real ContDiff Topology

def localConformalDiskH1Trace {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] BoundaryL2 :=
  diskH1Trace.comp (localConformalH1Pullback hR F hFs hL)

def localConformalDiskHalfTrace {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  diskHalfTrace.comp (localConformalH1Pullback hR F hFs hL)

@[simp] theorem localConformalDiskHalfTrace_apply {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) (n : ℤ) :
    localConformalDiskHalfTrace hR F hFs hL u n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
        boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) n :=
  diskHalfTrace_apply _ n

theorem localConformalDiskH1Trace_smooth_ae {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (f : smoothTraceTests) :
    (localConformalDiskH1Trace hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => f (F (circleMap 0 1 θ)) := by
  change (diskH1Trace (localConformalH1Pullback hR F hFs hL
    (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)) : ℝ → ℂ) =ᵐ[_] _
  rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f]
  have h := h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam (smoothDiskCompositionLin hR F hFs f)
  filter_upwards [h] with θ hθ
  rw [diskH1Trace, hθ]
  exact smoothDiskCompositionLin_eq_closedDisk hR F hFs f
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))

theorem norm_localConformalDiskHalfTrace_apply_le {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖localConformalDiskHalfTrace hR F hFs hL u‖ ≤
      Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) * Real.sqrt (max C 1) * ‖u‖ := by
  calc
    _ ≤ Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) * ‖localConformalH1Pullback hR F hFs hL u‖ :=
      norm_diskHalfTrace_le _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (norm_localConformalH1Pullback_apply_le hR F hFs hb hL hhol hinj hC u)
        (Real.sqrt_nonneg _)

theorem localConformalDiskH1Trace_eq_reparam {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ)) :
    h1ReparamBoundaryTrace hL hγ hτ = localConformalDiskH1Trace hR F hFs hL := by
  apply h1ReparamBoundaryTrace_unique hb hL hγ hτ
  intro f
  apply Lp.ext
  have h := localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f
  have h' : (smoothReparamBoundaryLin hγ hτ f : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => f (γ (τ θ)) :=
    (smoothReparamBoundary_memLp hγ hτ f).coeFn_toLp
  filter_upwards [h, h'] with θ hθ hθ'
  rw [hθ, hθ', hcoord]

end PolyaNeumann

end
