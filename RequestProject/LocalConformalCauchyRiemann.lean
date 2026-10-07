module

public import RequestProject.LocalConformalMass
public import Mathlib.Tactic

/-!
# Conformal invariance of the actual weak antiholomorphic defect

The defect is the genuine L² vector `dx u - i • dy u`, constructed from the
weak-gradient components of the actual H¹ space. For smooth restrictions the
composition differential multiplies this defect by `deriv F`. The actual
conformal Jacobian change of variables proves equality of its squared L² norms.
Density in the genuine H¹ norm extends this equality to every H¹ vector.

The coordinate map is supplied and holomorphic only on the open disk. No weak
derivative transfer formula, Hardy hypothesis, or PDE regularity is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

/-- The actual weak antiholomorphic defect, without the irrelevant factor 1/2. -/
def h1AntiholomorphicDefect (Ω : Set ℂ) : NeumannH1 Ω →L[ℂ] L2 Ω :=
  h1Gradient Ω 0 - Complex.I • h1Gradient Ω 1

@[simp] theorem h1AntiholomorphicDefect_apply (Ω : Set ℂ) (u : NeumannH1 Ω) :
    h1AntiholomorphicDefect Ω u = h1Gradient Ω 0 u - Complex.I • h1Gradient Ω 1 u := rfl

/-- The corresponding actual smooth differential. -/
def antiholomorphicDifferential (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I

private theorem cr_realCLM_apply_complex (A : ℂ →L[ℝ] ℂ) (w : ℂ) :
    A w = (w.re : ℂ) * A 1 + (w.im : ℂ) * A Complex.I := by
  calc
    A w = A (w.re • (1 : ℂ) + w.im • Complex.I) := by
      congr 1
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im w).symm
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

/-- The real-linear computation behind conformal invariance of this defect. -/
theorem realCLM_antiholomorphic_factor (A : ℂ →L[ℝ] ℂ) (c : ℂ) :
    A c - Complex.I * A (c * Complex.I) =
      c * (A 1 - Complex.I * A Complex.I) := by
  rw [cr_realCLM_apply_complex A c, cr_realCLM_apply_complex A (c * Complex.I)]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;> ring

/-- The smooth H¹ defect has its genuine almost-everywhere representative. -/
theorem h1AntiholomorphicDefect_smooth_ae (Ω : Set ℂ) (f : smoothTraceTests) :
    (h1AntiholomorphicDefect Ω (smoothTraceH1 Ω f) : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      antiholomorphicDifferential (f : ℂ → ℂ) := by
  let u := smoothTraceH1 Ω f
  have h0 : (h1Gradient Ω 0 u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (f : ℂ → ℂ) z (coordDir 0) :=
    (smoothTraceTests_memLp_deriv Ω f 0).coeFn_toLp
  have h1 : (h1Gradient Ω 1 u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (f : ℂ → ℂ) z (coordDir 1) :=
    (smoothTraceTests_memLp_deriv Ω f 1).coeFn_toLp
  change ((h1Gradient Ω 0 u - Complex.I • h1Gradient Ω 1 u : L2 Ω) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω]
    antiholomorphicDifferential (f : ℂ → ℂ)
  filter_upwards [Lp.coeFn_sub (h1Gradient Ω 0 u) (Complex.I • h1Gradient Ω 1 u),
    Lp.coeFn_smul Complex.I (h1Gradient Ω 1 u), h0, h1] with z hsub hsmul hx hy
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hx, hy]
  rfl

theorem norm_sq_h1AntiholomorphicDefect_smooth (Ω : Set ℂ) (f : smoothTraceTests) :
    ‖h1AntiholomorphicDefect Ω (smoothTraceH1 Ω f)‖ ^ 2 =
      ∫ z in Ω, ‖antiholomorphicDifferential (f : ℂ → ℂ) z‖ ^ 2 := by
  rw [norm_sq_L2_eq_integral]
  exact integral_congr_ae
    ((h1AntiholomorphicDefect_smooth_ae Ω f).fun_comp (fun w : ℂ => ‖w‖ ^ 2))

/-- The actual chain differential of a smooth pullback, before integration. -/
theorem antiholomorphicDifferential_smoothDiskComposition {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (f : smoothTraceTests)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    antiholomorphicDifferential (smoothDiskCompositionLin hR F hFs f : ℂ → ℂ) z =
      deriv F z * antiholomorphicDifferential (f : ℂ → ℂ) (F z) := by
  have hfd : ∀ v : ℂ, fderiv ℝ F z v = deriv F z * v := by
    intro v
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    change fderiv ℂ F z v = _
    exact fderiv_eq_deriv_mul
  unfold antiholomorphicDifferential
  rw [fderiv_smoothDiskCompositionLin hR F hFs f (ball_subset_closedBall hz)]
  simp only [ContinuousLinearMap.comp_apply, hfd, mul_one]
  exact realCLM_antiholomorphic_factor _ _

theorem norm_sq_antiholomorphicDifferential_smoothDiskComposition {R : ℝ}
    (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (f : smoothTraceTests)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖antiholomorphicDifferential (smoothDiskCompositionLin hR F hFs f : ℂ → ℂ) z‖ ^ 2 =
      ‖deriv F z‖ ^ 2 * ‖antiholomorphicDifferential (f : ℂ → ℂ) (F z)‖ ^ 2 := by
  rw [antiholomorphicDifferential_smoothDiskComposition hR F hFs hhol f hz,
    norm_mul, mul_pow]

/-- The exact Jacobian cancels the conformal differential weight. -/
theorem integral_antiholomorphicDifferential_smoothDiskComposition {R : ℝ}
    (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (f : smoothTraceTests) :
    (∫ z in ball (0 : ℂ) 1,
      ‖antiholomorphicDifferential (smoothDiskCompositionLin hR F hFs f : ℂ → ℂ) z‖ ^ 2) =
      ∫ w in F '' ball (0 : ℂ) 1, ‖antiholomorphicDifferential (f : ℂ → ℂ) w‖ ^ 2 := by
  rw [localConformal_integral_image isOpen_ball hhol hinj]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  exact norm_sq_antiholomorphicDifferential_smoothDiskComposition hR F hFs hhol f hz

section SuppliedCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)

include hb hhol hinj hC in
/-- Conformal invariance for every vector of the actual weak-gradient H¹ space. -/
theorem localConformalH1Pullback_antiholomorphicDefect_norm_sq
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖h1AntiholomorphicDefect (ball (0 : ℂ) 1)
      (localConformalH1Pullback hR F hFs hL u)‖ ^ 2 =
      ‖h1AntiholomorphicDefect (F '' ball (0 : ℂ) 1) u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => ‖h1AntiholomorphicDefect (ball (0 : ℂ) 1)
      (localConformalH1Pullback hR F hFs hL v)‖ ^ 2 =
      ‖h1AntiholomorphicDefect (F '' ball (0 : ℂ) 1) v‖ ^ 2) u ?_ ?_
  · exact isClosed_eq
      (((h1AntiholomorphicDefect (ball (0 : ℂ) 1)).continuous.comp
        (localConformalH1Pullback hR F hFs hL).continuous).norm.pow 2)
      ((h1AntiholomorphicDefect (F '' ball (0 : ℂ) 1)).continuous.norm.pow 2)
  · intro f
    change ‖h1AntiholomorphicDefect (ball (0 : ℂ) 1)
      (localConformalH1Pullback hR F hFs hL
        (smoothTraceH1 (F '' ball (0 : ℂ) 1) f))‖ ^ 2 =
      ‖h1AntiholomorphicDefect (F '' ball (0 : ℂ) 1)
        (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)‖ ^ 2
    rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC,
      norm_sq_h1AntiholomorphicDefect_smooth, norm_sq_h1AntiholomorphicDefect_smooth]
    exact integral_antiholomorphicDifferential_smoothDiskComposition hR F hFs hhol hinj f

include hb hhol hinj hC in
theorem localConformalH1Pullback_antiholomorphicDefect_norm
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖h1AntiholomorphicDefect (ball (0 : ℂ) 1)
      (localConformalH1Pullback hR F hFs hL u)‖ =
      ‖h1AntiholomorphicDefect (F '' ball (0 : ℂ) 1) u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (localConformalH1Pullback_antiholomorphicDefect_norm_sq hR F hFs hb hL hhol hinj hC u)

include hb hhol hinj hC in
/-- The stable zero-equivalence used to transport an actual disk weak CR equation. -/
theorem localConformalH1Pullback_antiholomorphicDefect_eq_zero_iff
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    h1AntiholomorphicDefect (ball (0 : ℂ) 1) (localConformalH1Pullback hR F hFs hL u) = 0 ↔
      h1AntiholomorphicDefect (F '' ball (0 : ℂ) 1) u = 0 := by
  have hn := localConformalH1Pullback_antiholomorphicDefect_norm hR F hFs hb hL hhol hinj hC u
  constructor
  · intro hd
    apply norm_eq_zero.mp
    rw [← hn, hd, norm_zero]
  · intro hp
    apply norm_eq_zero.mp
    rw [hn, hp, norm_zero]

include hb hhol hinj hC in
theorem localConformalH1Pullback_antiholomorphic_iff
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    h1Gradient (ball (0 : ℂ) 1) 0 (localConformalH1Pullback hR F hFs hL u) =
        Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (localConformalH1Pullback hR F hFs hL u) ↔
      h1Gradient (F '' ball (0 : ℂ) 1) 0 u =
        Complex.I • h1Gradient (F '' ball (0 : ℂ) 1) 1 u := by
  simpa only [h1AntiholomorphicDefect_apply, sub_eq_zero] using
    localConformalH1Pullback_antiholomorphicDefect_eq_zero_iff hR F hFs hb hL hhol hinj hC u

end SuppliedCoordinates

end PolyaNeumann

end
