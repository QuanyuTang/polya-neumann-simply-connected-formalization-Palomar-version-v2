module

public import RequestProject.LocalConformalMass
public import RequestProject.LocalConformalTests
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The actual H¹ equivalence for supplied conformal coordinates

The pullback is the existing bounded map between the genuine weak-gradient H¹
spaces. Its inverse is constructed here: the mass change-of-variables identity
and the conformal gradient identity give a reverse norm bound, hence closed
range; physical inverse-coordinate tests put every smooth disk restriction in
that range, hence density and surjectivity.

All coordinate and inverse data are supplied explicitly. This file does not
construct an initial conformal map or assume surjectivity of the pullback.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

section NormBound

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)

include hb hhol hinj hC hK in
/-- The physical H¹ norm is bounded by the norm of the actual disk pullback.
The multiplier constant is the genuine bound on the conformal Jacobian root. -/
theorem localConformalH1Pullback_reverse_norm_sq
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖u‖ ^ 2 ≤ max (K ^ 2) 1 * ‖localConformalH1Pullback hR F hFs hL u‖ ^ 2 := by
  let v := localConformalH1Pullback hR F hFs hL u
  have hK0 : 0 ≤ K := (norm_nonneg _).trans
    (hK 0 (by norm_num [Metric.mem_ball]))
  have hm := norm_sq_localConformalMassPullback hR F hFs hb hL hhol hinj hC hK u
  have hg := localConformalH1Pullback_gradient_energy hR F hFs hb hL hhol hinj hC u
  have hmul : ‖localConformalMassPullback hR F hFs hL hK u‖ ≤
      K * ‖h1Value (ball (0 : ℂ) 1) v‖ := by
    change ‖lpBoundedMulLin (localConformalMassDensity F)
      (localConformalMassDensity_aemeasurable hR F hFs)
      (localConformalMassDensity_ae_bound F hK)
      (h1Value (ball (0 : ℂ) 1) v)‖ ≤ _
    exact norm_lpBoundedMulLin_le _ _ _ _
  have hmulSq : ‖localConformalMassPullback hR F hFs hL hK u‖ ^ 2 ≤
      K ^ 2 * ‖h1Value (ball (0 : ℂ) 1) v‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))).2 hmul
  have hgrad0 : 0 ≤ ∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i v‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    ‖u‖ ^ 2 = ‖localConformalMassPullback hR F hFs hL hK u‖ ^ 2 +
        ∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i v‖ ^ 2 := by
      rw [h1_norm_sq, hm]
      exact congrArg (fun t => ‖h1Value (F '' ball (0 : ℂ) 1) u‖ ^ 2 + t) hg.symm
    _ ≤ K ^ 2 * ‖h1Value (ball (0 : ℂ) 1) v‖ ^ 2 +
        ∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i v‖ ^ 2 :=
      add_le_add hmulSq le_rfl
    _ ≤ max (K ^ 2) 1 * ‖h1Value (ball (0 : ℂ) 1) v‖ ^ 2 +
        max (K ^ 2) 1 * (∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i v‖ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      · simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_right (K ^ 2) 1) hgrad0
    _ = max (K ^ 2) 1 * ‖v‖ ^ 2 := by
      rw [h1_norm_sq]
      ring

include hb hhol hinj hC hK in
/-- A concrete bounded-below estimate for the actual pullback. -/
theorem localConformalH1Pullback_reverse_norm
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖u‖ ≤ Real.sqrt (max (K ^ 2) 1) * ‖localConformalH1Pullback hR F hFs hL u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (le_trans zero_le_one (le_max_right (K ^ 2) 1))]
  exact localConformalH1Pullback_reverse_norm_sq hR F hFs hb hL hhol hinj hC hK u

include hb hhol hinj hC hK in
theorem localConformalH1Pullback_antilipschitz :
    AntilipschitzWith (Real.toNNReal (Real.sqrt (max (K ^ 2) 1)))
      (localConformalH1Pullback hR F hFs hL) := by
  apply (localConformalH1Pullback hR F hFs hL).antilipschitz_of_bound
  intro u
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  exact localConformalH1Pullback_reverse_norm hR F hFs hb hL hhol hinj hC hK u

include hb hhol hinj hC hK in
theorem localConformalH1Pullback_injective :
    Function.Injective (localConformalH1Pullback hR F hFs hL) :=
  (localConformalH1Pullback_antilipschitz hR F hFs hb hL hhol hinj hC hK).injective

include hb hhol hinj hC hK in
theorem localConformalH1Pullback_isClosed_range :
    IsClosed (Set.range (localConformalH1Pullback hR F hFs hL)) :=
  (localConformalH1Pullback_antilipschitz hR F hFs hb hL hhol hinj hC hK).isClosed_range
    (localConformalH1Pullback hR F hFs hL).uniformContinuous

end NormBound

section DenseRange

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

include hb hhol hinj hC e he hsource hes in
/-- Every genuine smooth disk restriction is the pullback of a physical test. -/
theorem smoothTraceH1_mem_localConformalH1Pullback_range (φ : smoothTraceTests) :
    smoothTraceH1 (ball (0 : ℂ) 1) φ ∈
      Set.range (localConformalH1Pullback hR F hFs hL) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test hR F hFs hb hL hhol hinj hC
    e he hsource hes φ.property.1
  refine ⟨smoothTraceH1 (F '' ball (0 : ℂ) 1) f, hp.trans ?_⟩
  apply smoothTraceH1_eq_of_eqOn isOpen_ball
  intro z hz
  exact diskHarmonicCutoff_eq_closedDisk (φ : ℂ → ℂ) (ball_subset_closedBall hz)

include hb hhol hinj hC e he hsource hes in
/-- Density follows from exact physical inverse-coordinate tests, rather than
from an assumed surjectivity statement. -/
theorem localConformalH1Pullback_denseRange :
    DenseRange (localConformalH1Pullback hR F hFs hL) := by
  have hsub : Set.range (smoothTraceH1Lin isOpen_ball) ⊆
      Set.range (localConformalH1Pullback hR F hFs hL) := by
    rintro _ ⟨φ, rfl⟩
    exact smoothTraceH1_mem_localConformalH1Pullback_range hR F hFs hb hL hhol hinj hC
      e he hsource hes φ
  intro v
  exact closure_mono hsub
    ((denseRange_smoothTraceH1Lin unitDisk_bounded isLipschitzDomain_unitDisk) v)

end DenseRange

section Equivalence

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

include hb hhol hinj hC hK e he hsource hes in
theorem localConformalH1Pullback_surjective :
    Function.Surjective (localConformalH1Pullback hR F hFs hL) := by
  intro v
  have hv := localConformalH1Pullback_denseRange hR F hFs hb hL hhol hinj hC
    e he hsource hes v
  rw [(localConformalH1Pullback_isClosed_range hR F hFs hb hL hhol hinj hC hK).closure_eq]
    at hv
  exact hv

include hb hhol hinj hC hK e he hsource hes in
theorem localConformalH1Pullback_bijective :
    Function.Bijective (localConformalH1Pullback hR F hFs hL) :=
  ⟨localConformalH1Pullback_injective hR F hFs hb hL hhol hinj hC hK,
    localConformalH1Pullback_surjective hR F hFs hb hL hhol hinj hC hK e he hsource hes⟩

/-- The supplied-map H¹ equivalence; its forward map is the actual pullback. -/
def localConformalH1Equiv :
    NeumannH1 (F '' ball (0 : ℂ) 1) ≃L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  ContinuousLinearEquiv.ofBijective (localConformalH1Pullback hR F hFs hL)
    (LinearMap.ker_eq_bot.mpr
      (localConformalH1Pullback_injective hR F hFs hb hL hhol hinj hC hK))
    (LinearMap.range_eq_top.mpr
      (localConformalH1Pullback_surjective hR F hFs hb hL hhol hinj hC hK e he hsource hes))

@[simp] theorem localConformalH1Equiv_apply
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    localConformalH1Equiv hR F hFs hb hL hhol hinj hC hK e he hsource hes u =
      localConformalH1Pullback hR F hFs hL u := rfl

/-- The actual continuous inverse, taking a disk H¹ vector to its physical vector. -/
def localConformalH1Pushforward :
    NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  (localConformalH1Equiv hR F hFs hb hL hhol hinj hC hK e he hsource hes).symm.toContinuousLinearMap

@[simp] theorem localConformalH1Pullback_pushforward
    (v : NeumannH1 (ball (0 : ℂ) 1)) :
    localConformalH1Pullback hR F hFs hL
      (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes v) = v :=
  (localConformalH1Equiv hR F hFs hb hL hhol hinj hC hK e he hsource hes).apply_symm_apply v

@[simp] theorem localConformalH1Pushforward_pullback
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes
      (localConformalH1Pullback hR F hFs hL u) = u :=
  (localConformalH1Equiv hR F hFs hb hL hhol hinj hC hK e he hsource hes).symm_apply_apply u

theorem norm_localConformalH1Pushforward_apply_le
    (v : NeumannH1 (ball (0 : ℂ) 1)) :
    ‖localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes v‖ ≤
      Real.sqrt (max (K ^ 2) 1) * ‖v‖ := by
  have h := localConformalH1Pullback_reverse_norm hR F hFs hb hL hhol hinj hC hK
    (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes v)
  simpa only [localConformalH1Pullback_pushforward] using h

theorem norm_localConformalH1Pushforward_le :
    ‖localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes‖ ≤
      Real.sqrt (max (K ^ 2) 1) :=
  (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes).opNorm_le_bound
    (Real.sqrt_nonneg _)
    (norm_localConformalH1Pushforward_apply_le hR F hFs hb hL hhol hinj hC hK e he hsource hes)

end Equivalence

end PolyaNeumann

end
