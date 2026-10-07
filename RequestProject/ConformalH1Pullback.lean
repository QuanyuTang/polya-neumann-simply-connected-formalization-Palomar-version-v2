module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Complex
public import Mathlib.Tactic
public import RequestProject.ChainRule
public import RequestProject.DiskHalfTrace
public import RequestProject.ConformalSmoothTests

/-!
# Actual H¹ pullback in boundary coordinates

The existing weak-gradient chain rule and Jacobian change of variables
construct a pullback of genuine H¹ vectors. Its continuity follows from
the closed graph theorem and the bounded actual L² pullback. No bound for
the H¹ pullback or for a fractional trace is supplied as an input.

For a holomorphic map the physical gradient energy is preserved exactly.
Pulling a general image domain back to the disk then gives a bounded
half-order Fourier trace. Smoothness of the coordinate map near the closed
disk gives its actual boundary values on the dense smooth restrictions.

The geometric inputs in this auxiliary module describe a given plane
homeomorphism that is bi-Lipschitz on the two domains. Existence of such
an extension for the interior Riemann map of a smooth domain is a separate
boundary-regularity theorem; this module does not assume that theorem or
assert that it has been established.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Real ComplexConjugate InnerProductSpace Topology ENNReal

section Bilipschitz

variable {U : Set ℂ} (hU : IsOpen U) {F : ℂ ≃ₜ ℂ} {K : NNReal}
  (hK : 0 < K) (hF : LipschitzOnWith K F U)
  (hG : LipschitzOnWith K F.symm (F '' U))

theorem norm_bilipPull_le (v : L2 (F '' U)) :
    ‖bilipPull hU hK hF hG v‖ ≤ (K : ℝ) * ‖v‖ := by
  change ‖(memLp_comp_bilip hU hK hF hG v).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  have hb := eLpNorm_comp_bilip_le hU hK hF hG (v : ℂ → ℂ)
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.memLp v).eLpNorm_ne_top) hb
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hr

/-- The actual L² composition map, with its bound proved by Jacobian change of variables. -/
def bilipL2Pullback : L2 (F '' U) →L[ℂ] L2 U :=
  (bilipPull hU hK hF hG).toLinearMap.mkContinuous K
    (norm_bilipPull_le hU hK hF hG)

@[simp] theorem bilipL2Pullback_apply (v : L2 (F '' U)) :
    bilipL2Pullback hU hK hF hG v = bilipPull hU hK hF hG v := rfl

/-- The H¹ vector consists of the actual composed value and the actual weak chain gradient. -/
def bilipH1PullbackLin : NeumannH1 (F '' U) →ₗ[ℂ] NeumannH1 U where
  toFun u := h1Vector (isWeakGradient_comp_bilip hU hK hF hG
    (h1Value_weakGradient (F '' U) u)
    (bilipPull_ae hU hK hF hG (h1Value (F '' U) u)))
  map_add' u v := by
    apply h1Value_injective hU
    change bilipPull hU hK hF hG (h1Value (F '' U) (u + v)) =
      h1Value U (h1Vector _) + h1Value U (h1Vector _)
    simp only [map_add, h1Value_h1Vector]
  map_smul' c u := by
    apply h1Value_injective hU
    change bilipPull hU hK hF hG (h1Value (F '' U) (c • u)) =
      c • h1Value U (h1Vector _)
    simp only [map_smul, h1Value_h1Vector]

@[simp] theorem h1Value_bilipH1PullbackLin (u : NeumannH1 (F '' U)) :
    h1Value U (bilipH1PullbackLin hU hK hF hG u) =
      bilipL2Pullback hU hK hF hG (h1Value (F '' U) u) := rfl

theorem bilipH1Pullback_closed_graph (u : ℕ → NeumannH1 (F '' U))
    (x : NeumannH1 (F '' U)) (y : NeumannH1 U)
    (hu : Tendsto u atTop (𝓝 x))
    (hy : Tendsto (bilipH1PullbackLin hU hK hF hG ∘ u) atTop (𝓝 y)) :
    y = bilipH1PullbackLin hU hK hF hG x := by
  apply h1Value_injective hU
  have ht₁ := ((h1Value U).continuous.tendsto y).comp hy
  have ht₂ := (((bilipL2Pullback hU hK hF hG).comp
    (h1Value (F '' U))).continuous.tendsto x).comp hu
  simp only [Function.comp_def, h1Value_bilipH1PullbackLin] at ht₁
  change Tendsto (fun n => bilipL2Pullback hU hK hF hG (h1Value (F '' U) (u n)))
    atTop (𝓝 (bilipL2Pullback hU hK hF hG (h1Value (F '' U) x))) at ht₂
  exact tendsto_nhds_unique ht₁ ht₂

/-- The closed graph theorem proves boundedness for the genuine weak-gradient pullback. -/
def bilipH1Pullback : NeumannH1 (F '' U) →L[ℂ] NeumannH1 U :=
  ContinuousLinearMap.ofSeqClosedGraph
    (bilipH1Pullback_closed_graph hU hK hF hG)

@[simp] theorem bilipH1Pullback_apply (u : NeumannH1 (F '' U)) :
    bilipH1Pullback hU hK hF hG u = bilipH1PullbackLin hU hK hF hG u := rfl

@[simp] theorem h1Value_bilipH1Pullback (u : NeumannH1 (F '' U)) :
    h1Value U (bilipH1Pullback hU hK hF hG u) =
      bilipL2Pullback hU hK hF hG (h1Value (F '' U) u) := rfl

theorem h1Value_bilipH1Pullback_ae (u : NeumannH1 (F '' U)) :
    (h1Value U (bilipH1Pullback hU hK hF hG u) : ℂ → ℂ) =ᵐ[volume.restrict U]
      fun z => h1Value (F '' U) u (F z) :=
  bilipPull_ae hU hK hF hG _

theorem h1Gradient_bilipH1Pullback_ae (u : NeumannH1 (F '' U)) (i : Fin 2) :
    (h1Gradient U i (bilipH1Pullback hU hK hF hG u) : ℂ → ℂ) =ᵐ[volume.restrict U]
      chainGrad F (fun j => (h1Gradient (F '' U) j u : ℂ → ℂ)) i :=
  (memLp_chainGrad hU hK hF hG (fun j => h1Gradient (F '' U) j u) i).coeFn_toLp

end Bilipschitz

/-- The actual conformal Jacobian formula for Bochner integrals. -/
theorem integral_image_conformal {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U) (a : ℂ → ℝ) :
    (∫ w in F '' U, a w) = ∫ z in U, ‖deriv F z‖ ^ 2 * a (F z) := by
  have hfd : ∀ z ∈ U, HasFDerivWithinAt F
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv F z)).restrictScalars ℝ) U z :=
    fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hfd hinj a]
  apply setIntegral_congr_fun hU.measurableSet
  intro z _
  simp only [smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars]
  simp [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

private lemma conformal_chainGrad_sq {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (G : Fin 2 → ℂ → ℂ) :
    ‖chainGrad F G 0 z‖ ^ 2 + ‖chainGrad F G 1 z‖ ^ 2 =
      ‖deriv F z‖ ^ 2 * (‖G 0 (F z)‖ ^ 2 + ‖G 1 (F z)‖ ^ 2) := by
  have hfd (i : Fin 2) : fderiv ℝ F z (coordDir i) = deriv F z * coordDir i := by
    rw [hF.fderiv_restrictScalars ℝ]
    change fderiv ℂ F z (coordDir i) = _
    rw [fderiv_eq_deriv_mul]
  simp only [chainGrad, Fin.sum_univ_two, hfd, coordDir, coordRe,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one,
    Complex.mul_I_re, Complex.mul_I_im]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The true physical gradient energy is conformally invariant, for every H¹ vector. -/
theorem bilipH1Pullback_conformal_energy {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ ≃ₜ ℂ} {K : NNReal} (hK : 0 < K)
    (hF : LipschitzOnWith K F U) (hG : LipschitzOnWith K F.symm (F '' U))
    (hhol : DifferentiableOn ℂ F U) (u : NeumannH1 (F '' U)) :
    (∑ i : Fin 2, ‖h1Gradient U i (bilipH1Pullback hU hK hF hG u)‖ ^ 2) =
      ∑ i : Fin 2, ‖h1Gradient (F '' U) i u‖ ^ 2 := by
  let G : Fin 2 → L2 (F '' U) := fun i => h1Gradient (F '' U) i u
  let g : Fin 2 → L2 U := fun i => h1Gradient U i (bilipH1Pullback hU hK hF hG u)
  have hintg (i : Fin 2) : IntegrableOn (fun z => ‖g i z‖ ^ 2) U :=
    (Lp.memLp (g i)).integrable_norm_pow (by decide : (2 : ℝ≥0∞) ≠ 0)
  have hintG (i : Fin 2) : IntegrableOn (fun w => ‖G i w‖ ^ 2) (F '' U) :=
    (Lp.memLp (G i)).integrable_norm_pow (by decide : (2 : ℝ≥0∞) ≠ 0)
  calc
    _ = ∫ z in U, ‖g 0 z‖ ^ 2 + ‖g 1 z‖ ^ 2 := by
      rw [Fin.sum_univ_two, integral_add (hintg 0) (hintg 1),
        integral_norm_sq_toLp, integral_norm_sq_toLp]
    _ = ∫ z in U, ‖deriv F z‖ ^ 2 *
        (‖G 0 (F z)‖ ^ 2 + ‖G 1 (F z)‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [h1Gradient_bilipH1Pullback_ae hU hK hF hG u 0,
        h1Gradient_bilipH1Pullback_ae hU hK hF hG u 1,
        ae_restrict_mem hU.measurableSet] with z hz₀ hz₁ hzU
      change ‖g 0 z‖ ^ 2 + ‖g 1 z‖ ^ 2 = _
      rw [hz₀, hz₁]
      exact conformal_chainGrad_sq (hhol.differentiableAt (hU.mem_nhds hzU))
        (fun i => (G i : ℂ → ℂ))
    _ = ∫ w in F '' U, ‖G 0 w‖ ^ 2 + ‖G 1 w‖ ^ 2 :=
      (integral_image_conformal hU hhol F.injective.injOn _).symm
    _ = _ := by
      rw [integral_add (hintG 0) (hintG 1), integral_norm_sq_toLp,
        integral_norm_sq_toLp, Fin.sum_univ_two]

section DiskCoordinates

variable {F : ℂ ≃ₜ ℂ} {K : NNReal} (hK : 0 < K)
  (hF : LipschitzOnWith K F (ball (0 : ℂ) 1))
  (hG : LipschitzOnWith K F.symm (F '' ball (0 : ℂ) 1))

/-- Ordinary `dθ` trace in the given disk coordinates, on the genuine image-domain H¹ space. -/
def diskCoordinateH1Trace : NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] BoundaryL2 :=
  diskH1Trace.comp (bilipH1Pullback isOpen_ball hK hF hG)

/-- Half-order physical trace of the general image-domain H¹ vectors. -/
def diskCoordinateHalfTrace : NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  diskHalfTrace.comp (bilipH1Pullback isOpen_ball hK hF hG)

@[simp] theorem diskCoordinateHalfTrace_apply
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) (n : ℤ) :
    diskCoordinateHalfTrace hK hF hG u n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
        boundaryFourier (diskCoordinateH1Trace hK hF hG u) n :=
  diskHalfTrace_apply _ n

theorem diskCoordinateHalfTrace_norm_le (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖diskCoordinateHalfTrace hK hF hG u‖ ≤
      Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) *
        ‖bilipH1Pullback isOpen_ball hK hF hG‖ * ‖u‖ := by
  calc
    _ ≤ Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) *
        ‖bilipH1Pullback isOpen_ball hK hF hG u‖ := norm_diskHalfTrace_le _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        ((bilipH1Pullback isOpen_ball hK hF hG).le_opNorm u) (Real.sqrt_nonneg _)

private def diskCoordinateSmoothTest {R : ℝ} (hR : 1 < R)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (f : smoothTraceTests) : smoothTraceTests :=
  smoothDiskCompositionLin hR F hFs f

private theorem bilipH1Pullback_smooth {R : ℝ} (hR : 1 < R)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (f : smoothTraceTests) :
    bilipH1Pullback isOpen_ball hK hF hG
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
        smoothTraceH1 (ball (0 : ℂ) 1) (diskCoordinateSmoothTest hR hFs f) := by
  apply h1Value_injective isOpen_ball
  apply Lp.ext
  have hfval : (h1Value (F '' ball (0 : ℂ) 1)
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) : ℂ → ℂ) =ᵐ[
        volume.restrict (F '' ball (0 : ℂ) 1)] (f : ℂ → ℂ) := by
    rw [h1Value_smoothTraceH1]
    exact (f.property.memLp' 2).coeFn_toLp
  have htest : (h1Value (ball (0 : ℂ) 1)
      (smoothTraceH1 (ball (0 : ℂ) 1) (diskCoordinateSmoothTest hR hFs f)) : ℂ → ℂ)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
        (diskCoordinateSmoothTest hR hFs f : ℂ → ℂ) := by
    rw [h1Value_smoothTraceH1]
    exact ((diskCoordinateSmoothTest hR hFs f).property.memLp' 2).coeFn_toLp
  filter_upwards [h1Value_bilipH1Pullback_ae isOpen_ball hK hF hG
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f),
    (quasiMeasurePreserving_restrict hG).ae_eq hfval, htest,
    ae_restrict_mem measurableSet_ball] with z hz₁ hz₂ hz₃ hzD
  rw [hz₁, hz₂, hz₃]
  exact (smoothDiskCompositionLin_eq_closedDisk hR F hFs f
    (ball_subset_closedBall hzD)).symm

/-- On dense smooth source vectors the constructed trace is the actual value `f(F(e^{iθ}))`. -/
theorem diskCoordinateH1Trace_smooth_ae {R : ℝ} (hR : 1 < R)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (f : smoothTraceTests) :
    (diskCoordinateH1Trace hK hF hG
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) : ℝ → ℂ) =ᵐ[
        volume.restrict (Ioc (0 : ℝ) (2 * π))]
      fun θ => f (F (circleMap 0 1 θ)) := by
  change (diskH1Trace (bilipH1Pullback isOpen_ball hK hF hG
    (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)) : ℝ → ℂ) =ᵐ[_] _
  rw [bilipH1Pullback_smooth hK hF hG hR hFs f]
  have h := h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam (diskCoordinateSmoothTest hR hFs f)
  filter_upwards [h] with θ hθ
  rw [hθ]
  exact smoothDiskCompositionLin_eq_closedDisk hR F hFs f
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))

end DiskCoordinates

end PolyaNeumann

end
