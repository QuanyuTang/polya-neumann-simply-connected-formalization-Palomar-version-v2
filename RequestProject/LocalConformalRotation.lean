module

public import RequestProject.LocalConformalArcReparam
public import RequestProject.BoundaryOrigin
public import RequestProject.BoundaryParamShift
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Rotation of the actual supplied conformal coordinates. Multiplication by
`circleMap 0 1 t` preserves the disk and every centered collar. Precomposition
therefore retains the original physical domain, real smoothness, complex
holomorphicity, and the actual inverse. The circle trace is precisely shifted
by `t`; this connects the genuine choice of transport cut to the same supplied
coordinate interface. The final lift lemmas concern a given genuine C¹ lift
with its proved period increment, and do not assert initial map existence.
This module is part of the verified dependency chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology

/-- The real linear isometry that rotates the actual complex plane. -/
def localConformalRotationLIE (t : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation (Circle.exp t)

/-- The actual rotation, with its coefficient visible for complex calculus. -/
def localConformalRotation (t : ℝ) (z : ℂ) : ℂ := circleMap 0 1 t * z

@[simp] theorem localConformalRotationLIE_apply (t : ℝ) (z : ℂ) :
    localConformalRotationLIE t z = localConformalRotation t z := by
  simp [localConformalRotationLIE, rotation_apply, Circle.coe_exp,
    localConformalRotation, circleMap_zero]

theorem localConformalRotationLIE_coe (t : ℝ) :
    (localConformalRotationLIE t : ℂ → ℂ) = localConformalRotation t :=
  funext (localConformalRotationLIE_apply t)

@[simp] theorem localConformalRotation_zero (t : ℝ) :
    localConformalRotation t 0 = 0 := by
  simp [localConformalRotation]

@[simp] theorem localConformalRotation_norm (t : ℝ) (z : ℂ) :
    ‖localConformalRotation t z‖ = ‖z‖ := by
  simp [localConformalRotation]

@[simp] theorem localConformalRotation_mem_ball (t : ℝ) (z : ℂ) (r : ℝ) :
    localConformalRotation t z ∈ ball (0 : ℂ) r ↔ z ∈ ball (0 : ℂ) r := by
  simp only [mem_ball, dist_zero_right, localConformalRotation_norm]

@[simp] theorem localConformalRotation_mem_closedBall (t : ℝ) (z : ℂ) (r : ℝ) :
    localConformalRotation t z ∈ closedBall (0 : ℂ) r ↔
      z ∈ closedBall (0 : ℂ) r := by
  simp only [mem_closedBall, dist_zero_right, localConformalRotation_norm]

@[simp] theorem localConformalRotation_mem_sphere (t : ℝ) (z : ℂ) (r : ℝ) :
    localConformalRotation t z ∈ sphere (0 : ℂ) r ↔ z ∈ sphere (0 : ℂ) r := by
  simp only [mem_sphere, dist_zero_right, localConformalRotation_norm]

@[simp] theorem localConformalRotation_neg_left (t : ℝ) (z : ℂ) :
    localConformalRotation (-t) (localConformalRotation t z) = z := by
  unfold localConformalRotation
  rw [← mul_assoc, circleMap_zero_mul, one_mul, neg_add_cancel]
  simp [circleMap]

@[simp] theorem localConformalRotation_neg_right (t : ℝ) (z : ℂ) :
    localConformalRotation t (localConformalRotation (-t) z) = z := by
  unfold localConformalRotation
  rw [← mul_assoc, circleMap_zero_mul, one_mul, add_neg_cancel]
  simp [circleMap]

theorem localConformalRotation_injective (t : ℝ) :
    Function.Injective (localConformalRotation t) :=
  Function.LeftInverse.injective (localConformalRotation_neg_left t)

theorem localConformalRotation_surjective (t : ℝ) :
    Function.Surjective (localConformalRotation t) := by
  intro z
  exact ⟨localConformalRotation (-t) z, localConformalRotation_neg_right t z⟩

theorem localConformalRotation_contDiff (t : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (localConformalRotation t) := by
  rw [← localConformalRotationLIE_coe]
  exact (localConformalRotationLIE t).contDiff

theorem localConformalRotation_hasFDerivAt (t : ℝ) (z : ℂ) :
    HasFDerivAt (localConformalRotation t)
      (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z := by
  have h : HasFDerivAt (localConformalRotationLIE t)
      (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z :=
    (localConformalRotationLIE t : ℂ →L[ℝ] ℂ).hasFDerivAt
  rw [localConformalRotationLIE_coe] at h
  exact h

theorem localConformalRotation_hasDerivAt (t : ℝ) (z : ℂ) :
    HasDerivAt (localConformalRotation t) (circleMap 0 1 t) z :=
  hasDerivAt_const_mul (circleMap 0 1 t)

theorem localConformalRotation_image_ball (t : ℝ) (r : ℝ) :
    localConformalRotation t '' ball (0 : ℂ) r = ball (0 : ℂ) r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (localConformalRotation_mem_ball t z r).mpr hz
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_ball (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

theorem localConformalRotation_image_closedBall (t : ℝ) (r : ℝ) :
    localConformalRotation t '' closedBall (0 : ℂ) r = closedBall (0 : ℂ) r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (localConformalRotation_mem_closedBall t z r).mpr hz
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_closedBall (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

/-- Rotation of the given coordinate map, with no replacement of its image. -/
def localConformalRotate (F : ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  F ∘ localConformalRotation t

@[simp] theorem localConformalRotate_apply (F : ℂ → ℂ) (t : ℝ) (z : ℂ) :
    localConformalRotate F t z = F (circleMap 0 1 t * z) := rfl

theorem localConformalRotate_image_ball (F : ℂ → ℂ) (t r : ℝ) :
    localConformalRotate F t '' ball (0 : ℂ) r = F '' ball (0 : ℂ) r := by
  calc
    _ = F '' (localConformalRotation t '' ball (0 : ℂ) r) :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_ball]

theorem localConformalRotate_image_closedBall (F : ℂ → ℂ) (t r : ℝ) :
    localConformalRotate F t '' closedBall (0 : ℂ) r = F '' closedBall (0 : ℂ) r := by
  calc
    _ = F '' (localConformalRotation t '' closedBall (0 : ℂ) r) :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_closedBall]

theorem localConformalRotate_contDiffOn {F : ℂ → ℂ} {r : ℝ}
    {n : WithTop ℕ∞} (hF : ContDiffOn ℝ n F (ball (0 : ℂ) r)) (t : ℝ) :
    ContDiffOn ℝ n (localConformalRotate F t) (ball (0 : ℂ) r) :=
  hF.comp (localConformalRotation_contDiff t).contDiffOn
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_holomorphic {F : ℂ → ℂ} {r : ℝ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) r)) (t : ℝ) :
    DifferentiableOn ℂ (localConformalRotate F t) (ball (0 : ℂ) r) :=
  hF.comp (fun z _ => (localConformalRotation_hasDerivAt t z).differentiableAt.differentiableWithinAt)
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_injOn_ball {F : ℂ → ℂ} {r : ℝ}
    (hF : InjOn F (ball (0 : ℂ) r)) (t : ℝ) :
    InjOn (localConformalRotate F t) (ball (0 : ℂ) r) := by
  intro z hz w hw hzw
  exact localConformalRotation_injective t (hF
    ((localConformalRotation_mem_ball t z r).mpr hz)
    ((localConformalRotation_mem_ball t w r).mpr hw) hzw)

theorem localConformalRotate_injOn_closedBall {F : ℂ → ℂ} {r : ℝ}
    (hF : InjOn F (closedBall (0 : ℂ) r)) (t : ℝ) :
    InjOn (localConformalRotate F t) (closedBall (0 : ℂ) r) := by
  intro z hz w hw hzw
  exact localConformalRotation_injective t (hF
    ((localConformalRotation_mem_closedBall t z r).mpr hz)
    ((localConformalRotation_mem_closedBall t w r).mpr hw) hzw)

theorem localConformalRotate_hasDerivAt {F : ℂ → ℂ} (t : ℝ) {z : ℂ}
    (hF : DifferentiableAt ℂ F (localConformalRotation t z)) :
    HasDerivAt (localConformalRotate F t)
      (deriv F (localConformalRotation t z) * circleMap 0 1 t) z := by
  exact hF.hasDerivAt.comp z (localConformalRotation_hasDerivAt t z)

theorem localConformalRotate_deriv_norm {F : ℂ → ℂ} {r : ℝ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) r)) (t : ℝ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    ‖deriv (localConformalRotate F t) z‖ = ‖deriv F (localConformalRotation t z)‖ := by
  rw [(localConformalRotate_hasDerivAt t
    (hF.differentiableAt (isOpen_ball.mem_nhds
      ((localConformalRotation_mem_ball t z r).mpr hz)))).deriv]
  simp

theorem localConformalRotate_lower_deriv_bound {F : ℂ → ℂ} {C : ℝ}
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2) (t : ℝ) :
    ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv (localConformalRotate F t) z‖ ^ 2 := by
  intro z hz
  rw [localConformalRotate_deriv_norm hhol t hz]
  exact hC _ ((localConformalRotation_mem_ball t z 1).mpr hz)

theorem localConformalRotate_fderiv {F : ℂ → ℂ} (t : ℝ) {z : ℂ}
    (hF : DifferentiableAt ℝ F (localConformalRotation t z)) (v : ℂ) :
    fderiv ℝ (localConformalRotate F t) z v =
      fderiv ℝ F (localConformalRotation t z) (localConformalRotation t v) := by
  change fderiv ℝ (F ∘ localConformalRotation t) z v = _
  rw [(hF.hasFDerivAt.comp z (localConformalRotation_hasFDerivAt t z)).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change fderiv ℝ F (localConformalRotation t z) (localConformalRotationLIE t v) = _
  rw [localConformalRotationLIE_apply]

theorem localConformalRotate_closedDifferential_norm {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (t : ℝ)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖fderiv ℝ (localConformalRotate F t) z 1‖ =
      ‖fderiv ℝ F (localConformalRotation t z) 1‖ := by
  have hzt := (localConformalRotation_mem_closedBall t z 1).mpr hz
  rw [localConformalRotate_fderiv t
    ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hzt))).differentiableAt
      (by simp)),
    localConformal_fderiv_closedDisk hR F hFs hhol hzt]
  simp [localConformalRotation]

theorem localConformalRotate_upper_differential_bound {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) {K : ℝ}
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K) (t : ℝ) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (localConformalRotate F t) z 1‖ ≤ K := by
  intro z hz
  rw [localConformalRotate_closedDifferential_norm hR F hFs hhol t
    (ball_subset_closedBall hz)]
  exact hK _ ((localConformalRotation_mem_ball t z 1).mpr hz)

theorem localConformalRotate_closedDifferential_ne_zero {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) (t : ℝ) :
    ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ (localConformalRotate F t) z 1 ≠ 0 := by
  intro z hz
  apply norm_ne_zero_iff.mp
  rw [localConformalRotate_closedDifferential_norm hR F hFs hhol t hz]
  exact norm_ne_zero_iff.mpr (hnz _
    ((localConformalRotation_mem_closedBall t z 1).mpr hz))

/-- The actual new boundary origin is the old point at parameter `t`. -/
theorem physicalCircleTrace_localConformalRotate (F : ℂ → ℂ) (t θ : ℝ) :
    physicalCircleTrace (localConformalRotate F t) θ = physicalCircleTrace F (θ + t) := by
  simp only [physicalCircleTrace, localConformalRotate_apply, circleMap_zero_mul,
    one_mul, add_comm t θ]

theorem physicalCircleTrace_localConformalRotate_eq (F : ℂ → ℂ) (t : ℝ) :
    physicalCircleTrace (localConformalRotate F t) = fun θ => physicalCircleTrace F (θ + t) :=
  funext (physicalCircleTrace_localConformalRotate F t)

theorem physicalCircleTrace_localConformalRotate_lipschitz
    {F : ℂ → ℂ} {K : NNReal} (hΓ : LipschitzWith K (physicalCircleTrace F)) (t : ℝ) :
    LipschitzWith K (physicalCircleTrace (localConformalRotate F t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [physicalCircleTrace_localConformalRotate, Real.dist_eq] using
    hΓ.dist_le_mul (x + t) (y + t)

@[simp] theorem physicalCircleTrace_localConformalRotate_zero (F : ℂ → ℂ) (t : ℝ) :
    physicalCircleTrace (localConformalRotate F t) 0 = physicalCircleTrace F t := by
  rw [physicalCircleTrace_localConformalRotate, zero_add]

@[simp] theorem localConformalRotationLIE_symm (t : ℝ) :
    (localConformalRotationLIE t).symm = localConformalRotationLIE (-t) := by
  simp [localConformalRotationLIE, rotation_symm]

/-- Precomposition of the supplied actual local homeomorphism by rotation. -/
def localConformalRotatePartialHomeomorph (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) :
    OpenPartialHomeomorph ℂ ℂ :=
  (localConformalRotationLIE t).toHomeomorph.transOpenPartialHomeomorph e

@[simp] theorem localConformalRotatePartialHomeomorph_apply
    (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) (z : ℂ) :
    localConformalRotatePartialHomeomorph e t z = e (localConformalRotation t z) := by
  change e (localConformalRotationLIE t z) = _
  rw [localConformalRotationLIE_apply]

@[simp] theorem localConformalRotatePartialHomeomorph_symm_apply
    (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) (w : ℂ) :
    (localConformalRotatePartialHomeomorph e t).symm w =
      localConformalRotation (-t) (e.symm w) := by
  change (localConformalRotationLIE t).symm (e.symm w) = _
  rw [localConformalRotationLIE_symm, localConformalRotationLIE_apply]

theorem localConformalRotatePartialHomeomorph_source
    (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) :
    (localConformalRotatePartialHomeomorph e t).source =
      localConformalRotation t ⁻¹' e.source := by
  ext z
  change localConformalRotationLIE t z ∈ e.source ↔ _
  rw [localConformalRotationLIE_apply]
  rfl

@[simp] theorem localConformalRotatePartialHomeomorph_target
    (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) :
    (localConformalRotatePartialHomeomorph e t).target = e.target := rfl

theorem localConformalRotatePartialHomeomorph_coe {F : ℂ → ℂ}
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F) (t : ℝ) :
    (localConformalRotatePartialHomeomorph e t : ℂ → ℂ) = localConformalRotate F t := by
  funext z
  rw [localConformalRotatePartialHomeomorph_apply, he]
  rfl

theorem localConformalRotatePartialHomeomorph_closedDisk_source
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source) (t : ℝ) :
    closedBall (0 : ℂ) 1 ⊆ (localConformalRotatePartialHomeomorph e t).source := by
  rw [localConformalRotatePartialHomeomorph_source]
  intro z hz
  exact hsource ((localConformalRotation_mem_closedBall t z 1).mpr hz)

theorem localConformalRotatePartialHomeomorph_source_subset_ball
    (e : OpenPartialHomeomorph ℂ ℂ) {R : ℝ}
    (hsource : e.source ⊆ ball (0 : ℂ) R) (t : ℝ) :
    (localConformalRotatePartialHomeomorph e t).source ⊆ ball (0 : ℂ) R := by
  rw [localConformalRotatePartialHomeomorph_source]
  intro z hz
  exact (localConformalRotation_mem_ball t z R).mp (hsource hz)

theorem localConformalRotatePartialHomeomorph_smoothInverse
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) (t : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (localConformalRotatePartialHomeomorph e t).symm
      (localConformalRotatePartialHomeomorph e t).target := by
  have hfun : ((localConformalRotatePartialHomeomorph e t).symm : ℂ → ℂ) =
      localConformalRotation (-t) ∘ e.symm :=
    funext (localConformalRotatePartialHomeomorph_symm_apply e t)
  rw [localConformalRotatePartialHomeomorph_target, hfun]
  exact (localConformalRotation_contDiff (-t)).comp_contDiffOn hes

/-- The smooth inverse forces the actual closed-disk real differential to
be nonzero, including at the boundary. -/
theorem localConformalRotation_closedDifferential_ne_zero_of_inverse
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) :
    ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0 := by
  intro z hz
  have hzs := hsource hz
  have hzt : F z ∈ e.target := by
    rw [← he]
    exact e.mapsTo hzs
  have hdF := ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt
    (by simp)).hasFDerivAt
  have hdG := ((hes.contDiffAt (e.open_target.mem_nhds hzt)).differentiableAt
    (by simp)).hasFDerivAt
  have hcomp := hdG.comp z hdF
  have hid : HasFDerivAt (fun x : ℂ => x)
      ((fderiv ℝ e.symm (F z)).comp (fderiv ℝ F z)) z := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hzs] with x hx
    rw [← he]
    exact (e.left_inv hx).symm
  have hlin := hid.unique (hasFDerivAt_id z)
  have hval := congrArg (fun A : ℂ →L[ℝ] ℂ => A 1) hlin
  change fderiv ℝ e.symm (F z) (fderiv ℝ F z 1) = (1 : ℂ) at hval
  intro hzero
  rw [hzero, map_zero] at hval
  exact zero_ne_one hval

/-- The rotated genuine inverse remains holomorphic on the original open
physical domain, with its real smoothness already supplied above. -/
theorem localConformalRotatePartialHomeomorph_holomorphicInverse
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) (t : ℝ) :
    DifferentiableOn ℂ (localConformalRotatePartialHomeomorph e t).symm
      (F '' ball (0 : ℂ) 1) := by
  rw [← localConformalRotate_image_ball F t 1]
  exact localConformalInverse_holomorphic (localConformalRotate F t)
    (localConformalRotate_holomorphic hhol t)
    (localConformalRotate_closedDifferential_ne_zero hR F hFs hhol
      (localConformalRotation_closedDifferential_ne_zero_of_inverse hR F hFs
        e he hsource hes) t)
    (localConformalRotatePartialHomeomorph e t)
    (localConformalRotatePartialHomeomorph_coe e he t)
    (localConformalRotatePartialHomeomorph_closedDisk_source e hsource t)

/-- The existing boundary-origin theorem now chooses an actual rotation of
the supplied map. Its genuine monodromy hypothesis remains explicit. -/
theorem exists_localConformalRotate_cut_origin
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {K : NNReal} (hΓLip : LipschitzWith K (physicalCircleTrace F))
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport (physicalCircleTrace F) E (Ws E))
    {E₀ : ℝ} (hE₀ : 0 < E₀) (hU : monodromy (Ws E₀) ≠ 1) :
    ∃ t ∈ Icc 0 (2 * Real.pi), ∃ ε > 0, ε ≤ E₀ ∧
      ∀ E ∈ Ioo (E₀ - ε) (E₀ + ε), ∀ W' : ℝ → Ell2 →L[ℂ] Ell2,
        IsTransport (physicalCircleTrace (localConformalRotate F t)) E W' →
          cutC (W' (2 * Real.pi)) (basisVec 0) ≠ 0 := by
  have hnz := localConformalRotation_closedDifferential_ne_zero_of_inverse
    hR F hFs e he hsource hes
  have hΓnz : ∀ θ, deriv (physicalCircleTrace F) θ ≠ 0 :=
    localConformal_circleTrace_deriv_ne_zero hR F hFs hhol
      (fun z hz => hnz z (sphere_subset_closedBall hz))
  obtain ⟨t, ht, ε, hε, hεE, hc⟩ := exists_boundary_origin hΓLip
    (physicalCircleTrace_periodic F) (Eventually.of_forall hΓnz) hWs hE₀ hU
  refine ⟨t, ht, ε, hε, hεE, fun E hE W' hW' => ?_⟩
  rw [physicalCircleTrace_localConformalRotate_eq] at hW'
  exact hc E hE W' hW'

/-- Rebase the genuine parameter lift at the selected conformal origin. -/
def localConformalRotateTraceReparam (τ : ℝ → ℝ) (t : ℝ) (θ : ℝ) : ℝ :=
  τ (θ + t) - τ t

@[simp] theorem localConformalRotateTraceReparam_zero (τ : ℝ → ℝ) (t : ℝ) :
    localConformalRotateTraceReparam τ t 0 = 0 := by
  simp [localConformalRotateTraceReparam]

theorem localConformalRotateTraceReparam_hasDerivAt {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (t θ : ℝ) :
    HasDerivAt (localConformalRotateTraceReparam τ t) (deriv τ (θ + t)) θ := by
  show HasDerivAt (fun θ => τ (θ + t) - τ t) _ θ
  simpa only [mul_one, Function.comp_def, id] using
    (((hτ.contDiff.differentiable_one (θ + t)).hasDerivAt.comp θ
      ((hasDerivAt_id θ).add_const t)).sub_const (τ t))

theorem localConformalRotateTraceReparam_deriv {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (t θ : ℝ) :
    deriv (localConformalRotateTraceReparam τ t) θ = deriv τ (θ + t) :=
  (localConformalRotateTraceReparam_hasDerivAt hτ t θ).deriv

/-- C¹ continuity upgrades the original AE lower bound on its closed cut
interval to a true pointwise bound on that interval. -/
theorem IsC1TraceReparam.lower_pointwise {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) :
    ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), c ≤ deriv τ θ := by
  have heq : EqOn (fun θ => max c (deriv τ θ)) (deriv τ)
      (Icc (0 : ℝ) (2 * Real.pi)) := by
    apply Measure.eqOn_of_ae_eq
      (hτ.lower_ae.mono (fun θ hθ => max_eq_right hθ))
      (continuous_const.max hτ.contDiff.continuous_deriv_one).continuousOn
      hτ.contDiff.continuous_deriv_one.continuousOn
    simpa only [closure_interior_Icc (ne_of_lt Real.two_pi_pos)] using
      (subset_rfl : Icc (0 : ℝ) (2 * Real.pi) ⊆ Icc (0 : ℝ) (2 * Real.pi))
  intro θ hθ
  rw [← heq hθ]
  exact le_max_left _ _

theorem IsC1TraceReparam.deriv_periodic_of_add_period {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) :
    Function.Periodic (deriv τ) (2 * Real.pi) := by
  intro θ
  have hd : HasDerivAt (fun x => τ (x + 2 * Real.pi))
      (deriv τ (θ + 2 * Real.pi)) θ := by
    simpa only [mul_one, Function.comp_def, id] using
      (hτ.contDiff.differentiable_one (θ + 2 * Real.pi)).hasDerivAt.comp θ
        ((hasDerivAt_id θ).add_const (2 * Real.pi))
  have heq : (fun x => τ (x + 2 * Real.pi)) = fun x => τ x + 2 * Real.pi :=
    funext hper
  rw [heq] at hd
  exact hd.unique ((hτ.contDiff.differentiable_one θ).hasDerivAt.add_const (2 * Real.pi))

/-- The period increment transports the original lower bound to the whole
real line, rather than introducing a new global Jacobian premise. -/
theorem IsC1TraceReparam.lower_global_of_add_period {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) (θ : ℝ) :
    c ≤ deriv τ θ := by
  let θ' := toIcoMod Real.two_pi_pos 0 θ
  have hθ' : θ' ∈ Ico 0 (2 * Real.pi) := by
    simpa only [zero_add, θ'] using toIcoMod_mem_Ico Real.two_pi_pos 0 θ
  have heq : deriv τ θ' = deriv τ θ := by
    dsimp only [θ']
    rw [toIcoMod, (hτ.deriv_periodic_of_add_period hper).sub_zsmul_eq]
  rw [← heq]
  exact hτ.lower_pointwise θ' (Ico_subset_Icc_self hθ')

theorem localConformalRotateTraceReparam_isC1 {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) (t : ℝ) :
    IsC1TraceReparam (localConformalRotateTraceReparam τ t) c := by
  obtain ⟨K, hK⟩ := hτ.lipschitz
  refine ⟨?_, ⟨K, ?_⟩, ?_, localConformalRotateTraceReparam_zero τ t, ?_,
    hτ.lower_pos, ?_⟩
  · intro x y hxy
    change τ (x + t) - τ t ≤ τ (y + t) - τ t
    exact sub_le_sub_right (hτ.monotone (add_le_add hxy (le_refl t))) (τ t)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [localConformalRotateTraceReparam, Real.dist_eq] using
      hK.dist_le_mul (x + t) (y + t)
  · exact (hτ.contDiff.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  · dsimp only [localConformalRotateTraceReparam]
    rw [add_comm (2 * Real.pi) t, hper]
    ring
  · apply Eventually.of_forall
    intro θ
    rw [localConformalRotateTraceReparam_deriv hτ]
    exact hτ.lower_global_of_add_period hper (θ + t)

theorem localConformalRotateTraceReparam_add_period {τ : ℝ → ℝ}
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) (t θ : ℝ) :
    localConformalRotateTraceReparam τ t (θ + 2 * Real.pi) =
      localConformalRotateTraceReparam τ t θ + 2 * Real.pi := by
  dsimp only [localConformalRotateTraceReparam]
  rw [show θ + 2 * Real.pi + t = (θ + t) + 2 * Real.pi by ring, hper]
  ring

/-- The rotated circle is synchronized with the actual rebased physical
boundary, at the old physical parameter `τ t`. -/
theorem localConformalRotate_traceReparam_coordinate {F : ℂ → ℂ}
    {γ : ℝ → ℂ} {τ : ℝ → ℝ}
    (hcoord : ∀ θ, physicalCircleTrace F θ = γ (τ θ)) (t θ : ℝ) :
    physicalCircleTrace (localConformalRotate F t) θ =
      (fun s => γ (s + τ t)) (localConformalRotateTraceReparam τ t θ) := by
  rw [physicalCircleTrace_localConformalRotate, hcoord]
  simp only [localConformalRotateTraceReparam, sub_add_cancel]

theorem localConformalRotate_boundaryParam {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (τ : ℝ → ℝ) (t : ℝ) :
    IsBoundaryParam Ω (fun θ => γ (θ + τ t)) := hγ.shift (τ t)

/-- The physical domain and its genuine constant-speed boundary predicate
are transported by the exact image identity. -/
theorem localConformalRotate_boundaryParam_image {F : ℂ → ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ) (τ : ℝ → ℝ) (t : ℝ) :
    IsBoundaryParam (localConformalRotate F t '' ball (0 : ℂ) 1)
      (fun θ => γ (θ + τ t)) := by
  rw [localConformalRotate_image_ball]
  exact hγ.shift (τ t)

/-- The genuine arclength lift constructed in the existing coordinate
interface can be shifted at every conformal origin without a new premise. -/
theorem exists_localConformalRotate_normalizedArcReparam
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) (t : ℝ) :
    ∃ c : ℝ,
      IsC1TraceReparam
        (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) t) c ∧
      (∀ θ, c ≤ deriv
        (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) t) θ) ∧
      (∀ θ,
        localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) t
          (θ + 2 * Real.pi) =
        localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) t θ +
          2 * Real.pi) := by
  obtain ⟨c, hτ, _, hper⟩ := exists_localConformalArcReparam hR F hFs hhol hnz
  refine ⟨c, localConformalRotateTraceReparam_isC1 hτ hper t, ?_,
    localConformalRotateTraceReparam_add_period hper t⟩
  intro θ
  rw [localConformalRotateTraceReparam_deriv hτ]
  exact hτ.lower_global_of_add_period hper (θ + t)

end PolyaNeumann
end
