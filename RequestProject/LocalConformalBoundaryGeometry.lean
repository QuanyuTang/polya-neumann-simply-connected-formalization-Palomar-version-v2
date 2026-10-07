module

public import RequestProject.LocalConformalArcFactorization
public import Mathlib.Topology.ContinuousOn

/-!
# Boundary geometry of actual supplied disk coordinates

Continuity on the closed unit disk identifies its compact image with the
closure of the open-disk image. Closed-disk injectivity then identifies the
image of the unit sphere with the frontier whenever the open-disk image is
open. These are consequences of the supplied map, rather than additional
boundary-image assumptions.

The actual circle trace and its exact inverse-arclength curve therefore have
the physical boundary image. The final theorem constructs all five
orientation-free fields of a boundary parametrization, together with the
precise normalized arclength factorization and its C1 witness. The signed-area
field of `IsBoundaryParam` still requires a proof of positive orientation.
Existence of the initial supplied conformal map is a separate obligation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

/-- Compactness and continuity give the exact closed-disk image. No
injectivity or holomorphicity is needed for this topological identity. -/
theorem unitDisk_closed_image_eq_closure (F : ℂ → ℂ)
    (hF : ContinuousOn F (closedBall (0 : ℂ) 1)) :
    F '' closedBall (0 : ℂ) 1 = closure (F '' ball (0 : ℂ) 1) := by
  have hclosure : closure (ball (0 : ℂ) 1) = closedBall (0 : ℂ) 1 :=
    closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)
  have hFc : ContinuousOn F (closure (ball (0 : ℂ) 1)) := by
    simpa only [hclosure] using hF
  apply Subset.antisymm
  · simpa only [hclosure] using hFc.image_closure
  · apply closure_minimal
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨z, ball_subset_closedBall hz, rfl⟩
    · exact ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hF).isClosed

/-- For an injective closed-disk map, removing the open-disk image removes
exactly the interior source points. Openness of the image identifies the
remaining points with its frontier. -/
theorem unitDisk_sphere_image_eq_frontier (F : ℂ → ℂ)
    (hF : ContinuousOn F (closedBall (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hΩ : IsOpen (F '' ball (0 : ℂ) 1)) :
    F '' sphere (0 : ℂ) 1 = frontier (F '' ball (0 : ℂ) 1) := by
  calc
    F '' sphere (0 : ℂ) 1 =
        F '' (closedBall (0 : ℂ) 1 \ ball (0 : ℂ) 1) := by
      rw [closedBall_diff_ball]
    _ = F '' closedBall (0 : ℂ) 1 \ F '' ball (0 : ℂ) 1 :=
      hinj.image_diff_subset ball_subset_closedBall
    _ = closure (F '' ball (0 : ℂ) 1) \ F '' ball (0 : ℂ) 1 := by
      rw [unitDisk_closed_image_eq_closure F hF]
    _ = frontier (F '' ball (0 : ℂ) 1) := hΩ.frontier_eq.symm

theorem localConformal_closedDisk_image_eq_closure {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    F '' closedBall (0 : ℂ) 1 = closure (F '' ball (0 : ℂ) 1) :=
  unitDisk_closed_image_eq_closure F
    (hFs.continuousOn.mono (closedBall_subset_ball hR))

theorem localConformal_unitSphere_image_eq_frontier {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hΩ : IsOpen (F '' ball (0 : ℂ) 1)) :
    F '' sphere (0 : ℂ) 1 = frontier (F '' ball (0 : ℂ) 1) :=
  unitDisk_sphere_image_eq_frontier F
    (hFs.continuousOn.mono (closedBall_subset_ball hR)) hinj hΩ

/-- The closed angular interval has exactly the unit-circle image, including
both representations of its common endpoint. -/
theorem unitCircleMap_image_Icc :
    circleMap 0 1 '' Icc (0 : ℝ) (2 * Real.pi) = sphere (0 : ℂ) 1 := by
  have hIoc : circleMap 0 1 '' Ioc (0 : ℝ) (2 * Real.pi) = sphere (0 : ℂ) 1 := by
    simpa only [abs_one] using image_circleMap_Ioc 0 1
  apply Subset.antisymm
  · intro w hw
    have hwr : w ∈ range (circleMap 0 1) :=
      image_subset_range (circleMap 0 1) (Icc 0 (2 * Real.pi)) hw
    simpa only [range_circleMap, abs_one] using hwr
  · rw [← hIoc]
    rintro w ⟨θ, hθ, rfl⟩
    exact ⟨θ, ⟨hθ.1.le, hθ.2⟩, rfl⟩

theorem physicalCircleTrace_image_Icc (F : ℂ → ℂ) :
    physicalCircleTrace F '' Icc (0 : ℝ) (2 * Real.pi) = F '' sphere (0 : ℂ) 1 := by
  change (F ∘ circleMap 0 1) '' Icc (0 : ℝ) (2 * Real.pi) = _
  rw [image_comp, unitCircleMap_image_Icc]

/-- The boundary image is proved from F itself; it is not supplied as an
independent premise. -/
theorem localConformal_circleTrace_image_frontier {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hΩ : IsOpen (F '' ball (0 : ℂ) 1)) :
    physicalCircleTrace F '' Icc (0 : ℝ) (2 * Real.pi) =
      frontier (F '' ball (0 : ℂ) 1) := by
  rw [physicalCircleTrace_image_Icc]
  exact localConformal_unitSphere_image_eq_frontier hR F hFs hinj hΩ

/-- Exact inverse arclength preserves an already proved boundary image. -/
theorem normalizedArcCurve_image_frontier {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hnz : ∀ θ, deriv γ θ ≠ 0)
    (him : γ '' Icc (0 : ℝ) (2 * Real.pi) = frontier Ω) :
    normalizedArcCurve hγ hper hnz '' Icc (0 : ℝ) (2 * Real.pi) = frontier Ω := by
  rw [normalizedArcCurve_image_Icc hγ hper hnz, him]

/-- Actual supplied-coordinate construction of the exact arclength curve
and all orientation-free boundary fields. The only use of the Lipschitz
domain assumption here is openness of the actual image. -/
theorem exists_localConformalBoundaryGeometry {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) :
    ∃ (β : ℝ → ℂ) (c : ℝ),
      IsC1TraceReparam (normalizedArcReparam (physicalCircleTrace F)) c ∧
      (∀ θ, physicalCircleTrace F θ = β (normalizedArcReparam (physicalCircleTrace F) θ)) ∧
      (∃ K, LipschitzWith K β) ∧
      Function.Periodic β (2 * Real.pi) ∧
      InjOn β (Ico 0 (2 * Real.pi)) ∧
      β '' Icc (0 : ℝ) (2 * Real.pi) = frontier (F '' ball (0 : ℂ) 1) ∧
      (∃ v : ℝ, 0 < v ∧ ∀ᵐ θ, ‖deriv β θ‖ = v) := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  have him := localConformal_circleTrace_image_frontier hR F hFs hinj hL.1.1
  obtain ⟨c, hc, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hp hv
  refine ⟨normalizedArcCurve hγ hp hv, c, hc,
    normalizedArcCurve_factorization hγ hp hv,
    ⟨_, normalizedArcCurve_lipschitz hγ hp hv⟩,
    normalizedArcCurve_periodic hγ hp hv,
    normalizedArcCurve_injOn hγ hp hv (physicalCircleTrace_injOn_of_closedDisk_inj F hinj),
    normalizedArcCurve_image_frontier hγ hp hv him,
    arcLen (physicalCircleTrace F) (2 * Real.pi) / (2 * Real.pi),
    div_pos (arcLen_period_pos_of_regular hγ hv) Real.two_pi_pos, ?_⟩
  exact Filter.Eventually.of_forall (normalizedArcCurve_speed hγ hp hv)

end PolyaNeumann

end
