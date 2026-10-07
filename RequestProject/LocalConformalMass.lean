module

public import RequestProject.LpBoundedMultiplier
public import RequestProject.LocalConformalPullback

/-!
# The physical mass form in given conformal coordinates

The Jacobian square root multiplies the genuine H¹ pullback in disk L².
Change of variables proves its mass norm identity on smooth restrictions;
density and complex polarization prove the full weak mass pairing.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace

private theorem mass_inner_eq_of_linear_norm_sq
    {V E G : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (A : V →ₗ[ℂ] E) (B : V →ₗ[ℂ] G)
    (h : ∀ u, ‖A u‖ ^ 2 = ‖B u‖ ^ 2) (u v : V) :
    ⟪A u, A v⟫_ℂ = ⟪B u, B v⟫_ℂ := by
  apply Complex.ext
  · change RCLike.re ⟪A u, A v⟫_ℂ = RCLike.re ⟪B u, B v⟫_ℂ
    simp only [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
      ← map_add, ← map_sub, ← sq, h]
  · change RCLike.im ⟪A u, A v⟫_ℂ = RCLike.im ⟪B u, B v⟫_ℂ
    simp only [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four,
      ← map_smul, ← map_add, ← map_sub, ← sq, h]

def localConformalMassDensity (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (‖fderiv ℝ F z 1‖ : ℝ)

theorem localConformalMassDensity_continuousOn {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    ContinuousOn (localConformalMassDensity F) (closedBall (0 : ℂ) 1) := by
  exact Complex.ofRealCLM.continuous.comp_continuousOn
    ((((hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
      continuousOn_const).norm).mono (closedBall_subset_ball hR))

theorem exists_localConformalMassDensity_bound {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (localConformalMassDensity_continuousOn hR F hFs)
  refine ⟨max B 0, le_max_right _ _, fun z hz => ?_⟩
  have h := hB z (ball_subset_closedBall hz)
  simpa only [localConformalMassDensity, Complex.norm_of_nonneg (norm_nonneg _)] using
    h.trans (le_max_left B 0)

theorem localConformalMassDensity_aemeasurable {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    AEStronglyMeasurable (localConformalMassDensity F)
      (volume.restrict (ball (0 : ℂ) 1)) :=
  ((localConformalMassDensity_continuousOn hR F hFs).mono
    ball_subset_closedBall).aestronglyMeasurable measurableSet_ball

theorem localConformalMassDensity_ae_bound (F : ℂ → ℂ) {K : ℝ}
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K) :
    ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1), ‖localConformalMassDensity F z‖ ≤ K := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  simpa only [localConformalMassDensity, Complex.norm_of_nonneg (norm_nonneg _)] using hK z hz

def localConformalMassPullback {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) {K : ℝ}
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K) :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  (lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)).comp
      ((h1Value (ball (0 : ℂ) 1)).comp (localConformalH1Pullback hR F hFs hL))

theorem localConformalMassPullback_apply {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) {K : ℝ}
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    localConformalMassPullback hR F hFs hL hK u =
      lpBoundedMultiplier (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK)
        (h1Value (ball (0 : ℂ) 1)
          (localConformalH1Pullback hR F hFs hL u)) := rfl

theorem norm_sq_L2_eq_integral {U : Set ℂ} (v : L2 U) :
    ‖v‖ ^ 2 = ∫ z in U, ‖(v : ℂ → ℂ) z‖ ^ 2 := by
  simpa only [Lp.toLp_coeFn] using norm_sq_toLp_eq_integral (Lp.memLp v)

private theorem norm_sq_L2_eq_of_ae {U : Set ℂ} (v : L2 U)
    (g : ℂ → ℂ) (h : (v : ℂ → ℂ) =ᵐ[volume.restrict U] g) :
    ‖v‖ ^ 2 = ∫ z in U, ‖g z‖ ^ 2 := by
  exact (norm_sq_L2_eq_integral v).trans
    (integral_congr_ae (h.fun_comp (fun w : ℂ => ‖w‖ ^ 2)))

private theorem norm_sq_lpBoundedMultiplier_toLp {U : Set ℂ}
    (a : ℂ → ℂ) (ha : AEStronglyMeasurable a (volume.restrict U))
    {K : ℝ} (hK : ∀ᵐ z ∂volume.restrict U, ‖a z‖ ≤ K)
    {g : ℂ → ℂ} (hg : MemLp g 2 (volume.restrict U)) :
    ‖lpBoundedMultiplier a ha hK (hg.toLp g)‖ ^ 2 =
      ∫ z in U, ‖a z * g z‖ ^ 2 := by
  apply norm_sq_L2_eq_of_ae
  filter_upwards [lpBoundedMultiplier_ae a ha hK (hg.toLp g),
    hg.coeFn_toLp] with z hmul hval
  rw [hmul, hval]

private theorem localConformalMassDensity_norm_mul
    (F : ℂ → ℂ) {z : ℂ} (hF : DifferentiableAt ℂ F z) (w : ℂ) :
    ‖localConformalMassDensity F z * w‖ ^ 2 =
      ‖deriv F z‖ ^ 2 * ‖w‖ ^ 2 := by
  have hfd : fderiv ℝ F z 1 = deriv F z := by
    rw [hF.fderiv_restrictScalars ℝ]
    change fderiv ℂ F z 1 = _
    rw [fderiv_eq_deriv_mul, mul_one]
  rw [norm_mul, mul_pow, localConformalMassDensity,
    Complex.norm_of_nonneg (norm_nonneg _), hfd]

theorem localConformalMassPullback_smooth_eq {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K) (f : smoothTraceTests) :
    localConformalMassPullback hR F hFs hL hK
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
      lpBoundedMultiplier (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK)
        ((smoothTraceTests_memLp (ball (0 : ℂ) 1)
          (smoothDiskCompositionLin hR F hFs f)).toLp _) := by
  let M := lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)
  calc
    _ = M (h1Value (ball (0 : ℂ) 1) (localConformalH1Pullback hR F hFs hL
        (smoothTraceH1 (F '' ball (0 : ℂ) 1) f))) :=
      localConformalMassPullback_apply hR F hFs hL hK _
    _ = M (h1Value (ball (0 : ℂ) 1) (smoothTraceH1 (ball (0 : ℂ) 1)
        (smoothDiskCompositionLin hR F hFs f))) :=
      congrArg (fun v => M (h1Value (ball (0 : ℂ) 1) v))
        (localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f)
    _ = _ := congrArg M (h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
      (smoothDiskCompositionLin hR F hFs f))

theorem norm_sq_localConformalMass_smooth_L2 {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {K : ℝ}
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K) (f : smoothTraceTests) :
    ‖lpBoundedMultiplier (localConformalMassDensity F)
      (localConformalMassDensity_aemeasurable hR F hFs)
      (localConformalMassDensity_ae_bound F hK)
      ((smoothTraceTests_memLp (ball (0 : ℂ) 1)
        (smoothDiskCompositionLin hR F hFs f)).toLp _)‖ ^ 2 =
      ∫ z in F '' ball (0 : ℂ) 1, ‖f z‖ ^ 2 := by
  calc
    _ = ∫ z in ball (0 : ℂ) 1,
        ‖localConformalMassDensity F z * smoothDiskCompositionLin hR F hFs f z‖ ^ 2 :=
      norm_sq_lpBoundedMultiplier_toLp (localConformalMassDensity F)
      (localConformalMassDensity_aemeasurable hR F hFs)
      (localConformalMassDensity_ae_bound F hK)
      (smoothTraceTests_memLp (ball (0 : ℂ) 1)
        (smoothDiskCompositionLin hR F hFs f))
    _ = ∫ z in ball (0 : ℂ) 1, ‖deriv F z‖ ^ 2 * ‖f (F z)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change ‖localConformalMassDensity F z * smoothDiskCompositionLin hR F hFs f z‖ ^ 2 =
        ‖deriv F z‖ ^ 2 * ‖f (F z)‖ ^ 2
      rw [smoothDiskCompositionLin_eq_closedDisk hR F hFs f
        (ball_subset_closedBall hz)]
      exact localConformalMassDensity_norm_mul F
        (hhol.differentiableAt (isOpen_ball.mem_nhds hz)) (f (F z))
    _ = ∫ z in F '' ball (0 : ℂ) 1, ‖f z‖ ^ 2 :=
      (localConformal_integral_image isOpen_ball hhol hinj (fun z => ‖f z‖ ^ 2)).symm

theorem norm_sq_h1Value_smooth (U : Set ℂ) (f : smoothTraceTests) :
    ‖h1Value U (smoothTraceH1 U f)‖ ^ 2 = ∫ z in U, ‖f z‖ ^ 2 := by
  rw [h1Value_smoothTraceH1, norm_sq_toLp_eq_integral]

theorem norm_sq_localConformalMassPullback_smooth {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K) (f : smoothTraceTests) :
    ‖localConformalMassPullback hR F hFs hL hK
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)‖ ^ 2 =
      ‖h1Value (F '' ball (0 : ℂ) 1) (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)‖ ^ 2 := by
  calc
    _ = ‖lpBoundedMultiplier (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK)
        ((smoothTraceTests_memLp (ball (0 : ℂ) 1)
          (smoothDiskCompositionLin hR F hFs f)).toLp _)‖ ^ 2 :=
      congrArg (fun v : L2 (ball (0 : ℂ) 1) => ‖v‖ ^ 2)
        (localConformalMassPullback_smooth_eq hR F hFs hb hL hhol hinj hC hK f)
    _ = ∫ z in F '' ball (0 : ℂ) 1, ‖f z‖ ^ 2 :=
      norm_sq_localConformalMass_smooth_L2 hR F hFs hhol hinj hK f
    _ = _ := (norm_sq_h1Value_smooth _ f).symm

theorem norm_sq_localConformalMassPullback {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖localConformalMassPullback hR F hFs hL hK u‖ ^ 2 =
      ‖h1Value (F '' ball (0 : ℂ) 1) u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => ‖localConformalMassPullback hR F hFs hL hK v‖ ^ 2 =
      ‖h1Value (F '' ball (0 : ℂ) 1) v‖ ^ 2) u ?_ ?_
  · exact isClosed_eq ((localConformalMassPullback hR F hFs hL hK).continuous.norm.pow 2)
      ((h1Value (F '' ball (0 : ℂ) 1)).continuous.norm.pow 2)
  · exact norm_sq_localConformalMassPullback_smooth hR F hFs hb hL hhol hinj hC hK

theorem localConformalMassPullback_inner {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (u v : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ⟪localConformalMassPullback hR F hFs hL hK u,
      localConformalMassPullback hR F hFs hL hK v⟫_ℂ =
      ⟪h1Value (F '' ball (0 : ℂ) 1) u, h1Value (F '' ball (0 : ℂ) 1) v⟫_ℂ := by
  exact mass_inner_eq_of_linear_norm_sq
    (localConformalMassPullback hR F hFs hL hK).toLinearMap
    (h1Value (F '' ball (0 : ℂ) 1)).toLinearMap
    (norm_sq_localConformalMassPullback hR F hFs hb hL hhol hinj hC hK) u v

end PolyaNeumann

end
