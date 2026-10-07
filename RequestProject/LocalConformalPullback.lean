module

public import RequestProject.LocalConformalH1
public import Mathlib.Topology.Order.Compact

/-!
# Dense extension of the actual local conformal H¹ pullback

The norm bound is proved from the geometric Jacobian lower bound, rather
than assumed for an H¹ composition operator. Agreement on every smooth
restriction determines the resulting continuous linear map uniquely.
Gradient energy invariance extends to all genuine H¹ vectors.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Real ContDiff Topology ENNReal

/-- Nonvanishing of the differential on the compact closed disk supplies
the Jacobian lower bound needed for composition. -/
theorem exists_localConformal_jacobian_bound {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2 := by
  have hcont : ContinuousOn (fun z => ‖fderiv ℝ F z 1‖) (closedBall (0 : ℂ) 1) :=
    (((hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
      continuousOn_const).norm).mono (closedBall_subset_ball hR)
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMinOn
    ⟨0, by simp⟩ hcont
  have hp : 0 < ‖fderiv ℝ F z₀ 1‖ := norm_pos_iff.mpr (hnz z₀ hz₀)
  refine ⟨(‖fderiv ℝ F z₀ 1‖ ^ 2)⁻¹, by positivity, ?_⟩
  intro z hz
  have hfd : fderiv ℝ F z 1 = deriv F z := by
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    change fderiv ℂ F z 1 = _
    rw [fderiv_eq_deriv_mul, mul_one]
  have hle := hmin (ball_subset_closedBall hz)
  change ‖fderiv ℝ F z₀ 1‖ ≤ ‖fderiv ℝ F z 1‖ at hle
  rw [hfd] at hle
  calc
    1 = (‖fderiv ℝ F z₀ 1‖ ^ 2)⁻¹ * ‖fderiv ℝ F z₀ 1‖ ^ 2 :=
      (inv_mul_cancel₀ (by positivity)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hle 2)
      (inv_nonneg.mpr (sq_nonneg _))

def smoothDiskPullbackH1Lin {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    smoothTraceTests →ₗ[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  (smoothTraceH1Lin isOpen_ball).comp (smoothDiskCompositionLin hR F hFs)

def localConformalH1Pullback {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  (smoothDiskPullbackH1Lin hR F hFs).extendOfNorm (smoothTraceH1Lin hL.1.1)

theorem localConformalH1Pullback_smooth {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (f : smoothTraceTests) :
    localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
      smoothTraceH1 (ball (0 : ℂ) 1) (smoothDiskCompositionLin hR F hFs f) := by
  exact LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin hb hL)
    ⟨Real.sqrt (max C 1), norm_smoothDiskCompositionH1_le hR F hFs hhol hinj hC⟩ f

theorem norm_localConformalH1Pullback_apply_le {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖localConformalH1Pullback hR F hFs hL u‖ ≤ Real.sqrt (max C 1) * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_smoothTraceH1Lin hb hL)
    (Real.sqrt (max C 1)) (norm_smoothDiskCompositionH1_le hR F hFs hhol hinj hC) u

theorem norm_localConformalH1Pullback_le {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2) :
    ‖localConformalH1Pullback hR F hFs hL‖ ≤ Real.sqrt (max C 1) :=
  (localConformalH1Pullback hR F hFs hL).opNorm_le_bound (Real.sqrt_nonneg _)
    (norm_localConformalH1Pullback_apply_le hR F hFs hb hL hhol hinj hC)

theorem localConformalH1Pullback_unique {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (T : NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] NeumannH1 (ball (0 : ℂ) 1))
    (hT : ∀ f : smoothTraceTests, T (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
      smoothTraceH1 (ball (0 : ℂ) 1) (smoothDiskCompositionLin hR F hFs f)) :
    localConformalH1Pullback hR F hFs hL = T := by
  have heq : (fun u => localConformalH1Pullback hR F hFs hL u) = (fun u => T u) := by
    apply (denseRange_smoothTraceH1Lin hb hL).equalizer
      (localConformalH1Pullback hR F hFs hL).continuous T.continuous
    funext f
    change localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
      T (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)
    rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f]
    exact (hT f).symm
  exact ContinuousLinearMap.ext (fun u => congrFun heq u)

theorem gradient_energy_smoothTraceH1 (U : Set ℂ) (f : smoothTraceTests) :
    (∑ i : Fin 2, ‖h1Gradient U i (smoothTraceH1 U f)‖ ^ 2) =
      ∫ z in U, gradSq (f : ℂ → ℂ) z := by
  rw [Fin.sum_univ_two]
  simp only [h1Gradient_smoothTraceH1, norm_sq_toLp_eq_integral]
  have h0 := (smoothTraceTests_memLp_deriv U f 0).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  have h1 := (smoothTraceTests_memLp_deriv U f 1).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  rw [← integral_add h0 h1]
  rfl

theorem localConformalH1Pullback_gradient_energy {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i (localConformalH1Pullback hR F hFs hL u)‖ ^ 2) =
      ∑ i : Fin 2, ‖h1Gradient (F '' ball (0 : ℂ) 1) i u‖ ^ 2 := by
  have heq : (fun u => ∑ i : Fin 2,
      ‖h1Gradient (ball (0 : ℂ) 1) i (localConformalH1Pullback hR F hFs hL u)‖ ^ 2) =
      (fun u => ∑ i : Fin 2, ‖h1Gradient (F '' ball (0 : ℂ) 1) i u‖ ^ 2) := by
    apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    · exact continuous_finset_sum _ (fun i _ =>
        (((h1Gradient (ball (0 : ℂ) 1) i).continuous.comp
          (localConformalH1Pullback hR F hFs hL).continuous).norm.pow 2))
    · exact continuous_finset_sum _ (fun i _ =>
        ((h1Gradient (F '' ball (0 : ℂ) 1) i).continuous.norm.pow 2))
    · funext f
      change (∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i
        (localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f))‖ ^ 2) =
        ∑ i : Fin 2, ‖h1Gradient (F '' ball (0 : ℂ) 1) i
          (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)‖ ^ 2
      rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f,
        gradient_energy_smoothTraceH1, gradient_energy_smoothTraceH1]
      exact integral_gradSq_smoothDiskComposition hR F hFs hhol hinj f
  exact congrFun heq u

end PolyaNeumann

end
