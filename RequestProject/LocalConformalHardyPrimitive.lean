module

public import RequestProject.ConormalNormalization
public import RequestProject.PhysicalHardyWeights
public import RequestProject.HardyPrimitiveTrace
public import RequestProject.DiskHardyDerivative
public import RequestProject.LocalConformalHardyExtension
public import RequestProject.NeumannH1SmoothMultiplier
public import RequestProject.LocalConformalArcReparam
public import RequestProject.BoundaryFourierMultiplier
public import RequestProject.NeumannHardyTraceInjective
public import RequestProject.LocalConformalGradientComponents

/-!
# Actual Hardy multiplication and the normalized primitive

The primitive on normalized half-trace data is constructed from the proved
half-order sequence bound. Its gain of one order factors through the genuine
circle smoothing operator, so its disk extension has an actual L² derivative.

Multiplication of the actual disk Hardy extension by a compact smooth
coefficient has the proved weak product rule and the actual boundary trace
product rule. The coefficient conjugate to the conformal derivative is an
explicit derivative of a genuine smooth cutoff; its antiholomorphic CR
identity follows from interior holomorphicity of the supplied map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

local instance hardyPrimitiveCircleTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Averaged coefficients of an actual half-trace vector. -/
def normalizedHardyAverage (b : L2Z) (n : ℤ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * fromL2 (1 / 2 : ℝ) b n

private theorem hardy_toCLM_apply {s t C : ℝ}
    {Φ : (ℤ → ℂ) → (ℤ → ℂ)} (H : SeqOpBound s t C Φ) (b : L2Z) (n : ℤ) :
    H.toCLM b n = ((sobWeight n ^ t : ℝ) : ℂ) * Φ (fromL2 s b) n := rfl

/-- Bounded multiplication on normalized half-order Fourier coordinates.
The multiplier coefficients use the averaged convention. -/
def normalizedHardyMultiplier (c : ℤ → ℂ) (hc : IsWL1 (1 / 2 : ℝ) c) :
    L2Z →L[ℂ] L2Z :=
  (seqOpBound_seqConv (by norm_num : (0 : ℝ) ≤ 1 / 2) hc).toCLM

theorem normalizedHardyMultiplier_apply (c : ℤ → ℂ)
    (hc : IsWL1 (1 / 2 : ℝ) c) (b : L2Z) (n : ℤ) :
    normalizedHardyMultiplier c hc b n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * seqConv c (fromL2 (1 / 2 : ℝ) b) n :=
  hardy_toCLM_apply _ b n

/-- The primitive in the stronger normalized coordinates of order 3/2. -/
def normalizedHardyPrimitiveGain (a : ℤ → ℂ) (ha : IsWL1 (1 / 2 : ℝ) a) :
    L2Z →L[ℂ] L2Z :=
  (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).toCLM

theorem normalizedHardyPrimitiveGain_apply (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) (n : ℤ) :
    normalizedHardyPrimitiveGain a ha b n =
      ((sobWeight n ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) *
        antiPrim a (fromL2 (1 / 2 : ℝ) b) n :=
  hardy_toCLM_apply _ b n

theorem norm_normalizedHardyPrimitiveGain_le (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) :
    ‖normalizedHardyPrimitiveGain a ha‖ ≤ Real.sqrt (primConst (1 / 2 : ℝ) a) :=
  SeqOpBound.norm_toCLM_le _

/-- The actual normalized primitive at order 1/2, retaining the constant
chosen by `antiPrim` at the same boundary origin. -/
def normalizedHardyPrimitive (a : ℤ → ℂ) (ha : IsWL1 (1 / 2 : ℝ) a) :
    L2Z →L[ℂ] L2Z :=
  (sobolevSmoothing 1 (by norm_num)).comp (normalizedHardyPrimitiveGain a ha)

theorem normalizedHardyPrimitive_factor (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) :
    normalizedHardyPrimitive a ha =
      (sobolevSmoothing 1 (by norm_num)).comp (normalizedHardyPrimitiveGain a ha) := rfl

theorem norm_normalizedHardyPrimitive_le (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) :
    ‖normalizedHardyPrimitive a ha‖ ≤ Real.sqrt (primConst (1 / 2 : ℝ) a) := by
  have hs : ‖sobolevSmoothing 1 (by norm_num)‖ ≤ 1 :=
    norm_diagOp_le _ _ _
  calc
    _ ≤ ‖sobolevSmoothing 1 (by norm_num)‖ * ‖normalizedHardyPrimitiveGain a ha‖ :=
      (sobolevSmoothing 1 (by norm_num)).opNorm_comp_le (normalizedHardyPrimitiveGain a ha)
    _ ≤ 1 * Real.sqrt (primConst (1 / 2 : ℝ) a) :=
      mul_le_mul hs (norm_normalizedHardyPrimitiveGain_le a ha) (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem normalizedHardyPrimitive_apply (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) (n : ℤ) :
    normalizedHardyPrimitive a ha b n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * antiPrim a (fromL2 (1 / 2 : ℝ) b) n := by
  change sobolevSmoothing 1 (by norm_num) (normalizedHardyPrimitiveGain a ha b) n = _
  simp only [sobolevSmoothing, diagOp_apply, normalizedHardyPrimitiveGain_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
  have he : -(1 : ℝ) + ((1 / 2 : ℝ) + 1) = 1 / 2 := by ring
  rw [he]

/-- The factors sqrt(2pi) converting ordinary averaged coefficients to
actual boundary L² coefficients cancel in the normalized primitive. -/
theorem normalizedHardyPrimitive_apply_average (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) (n : ℤ) :
    normalizedHardyPrimitive a ha b n =
      (Real.sqrt (2 * Real.pi) : ℂ) * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        antiPrim a (normalizedHardyAverage b) n := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  have he : normalizedHardyAverage b =
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ • fromL2 (1 / 2 : ℝ) b := rfl
  rw [normalizedHardyPrimitive_apply, he,
    (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).map_smul _ _
      (isSobolevSeq_fromL2 (1 / 2 : ℝ) b)]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hs]

theorem normalizedHardyPrimitive_nonpositive (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (han : IsStrictNegativeFourierSupport a)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (normalizedHardyPrimitive a ha b) := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    intro n hn
    simp only [fromL2, hbn n hn, mul_zero]
  intro n hn
  rw [normalizedHardyPrimitive_apply, antiPrim_nonpositive han hb n hn, mul_zero]

/-- Actual L² derivative of the completed disk primitive. This identifies
the derivative with the completed derivative data, before a product is
identified using the genuine Hardy trace uniqueness theorem. -/
theorem diskHardyExtension_normalizedPrimitive_gradient (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskHardyExtension (normalizedHardyPrimitive a ha b)) =
      h1Value (ball (0 : ℂ) 1)
        (diskHardyExtension (diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b))) :=
  diskHardyExtension_smoothing_gradient (normalizedHardyPrimitiveGain a ha b)

theorem diskHardyExtension_normalizedPrimitive_gradient_y (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 1 (diskHardyExtension (normalizedHardyPrimitive a ha b)) =
      (-Complex.I) • h1Value (ball (0 : ℂ) 1)
        (diskHardyExtension (diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b))) :=
  diskHardyExtension_smoothing_gradient_y (normalizedHardyPrimitiveGain a ha b)

/-- Genuine disk H¹ multiplication of the actual completed Hardy extension. -/
def diskHardySmoothProduct (a : SmoothH1Coefficient) :
    L2Z →L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  (neumannH1SmoothMultiplier (ball (0 : ℂ) 1) a).comp diskHardyExtension

theorem h1Value_diskHardySmoothProduct (a : SmoothH1Coefficient) (b : L2Z) :
    h1Value (ball (0 : ℂ) 1) (diskHardySmoothProduct a b) =
      h1SmoothCoefficientL2 (ball (0 : ℂ) 1) a
        (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)) :=
  h1Value_neumannH1SmoothMultiplier _ a _

theorem h1Gradient_diskHardySmoothProduct (a : SmoothH1Coefficient) (b : L2Z) (i : Fin 2) :
    h1Gradient (ball (0 : ℂ) 1) i (diskHardySmoothProduct a b) =
      h1SmoothCoefficientL2 (ball (0 : ℂ) 1) a
          (h1Gradient (ball (0 : ℂ) 1) i (diskHardyExtension b)) +
        h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a i
          (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)) :=
  h1Gradient_neumannH1SmoothMultiplier _ a _ i

theorem h1Gradient_diskHardySmoothProduct_operator (a : SmoothH1Coefficient) (i : Fin 2) :
    (h1Gradient (ball (0 : ℂ) 1) i).comp (diskHardySmoothProduct a) =
      (h1SmoothCoefficientL2 (ball (0 : ℂ) 1) a).comp
          ((h1Gradient (ball (0 : ℂ) 1) i).comp diskHardyExtension) +
        (h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a i).comp
          ((h1Value (ball (0 : ℂ) 1)).comp diskHardyExtension) := by
  apply ContinuousLinearMap.ext
  intro b
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] using
    h1Gradient_diskHardySmoothProduct a b i

theorem h1Gradient_diskHardySmoothProduct_smoothing (a : SmoothH1Coefficient) (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardySmoothProduct a (sobolevSmoothing 1 (by norm_num) b)) =
      h1SmoothCoefficientL2 (ball (0 : ℂ) 1) a
          (h1Value (ball (0 : ℂ) 1) (diskHardyExtension (diskHardyDerivativeData b))) +
        h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a 0
          (h1Value (ball (0 : ℂ) 1)
            (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b))) := by
  rw [h1Gradient_diskHardySmoothProduct, diskHardyExtension_smoothing_gradient]

private theorem hardy_coefficient_derivative_CR (a : SmoothH1Coefficient)
    (hCR : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ (a : ℂ → ℂ) z 1 = Complex.I * fderiv ℝ (a : ℂ → ℂ) z Complex.I)
    (u : L2 (ball (0 : ℂ) 1)) :
    h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a 0 u =
      Complex.I • h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a 1 u := by
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientDerivativeL2_ae (ball (0 : ℂ) 1) a 0 u,
    h1SmoothCoefficientDerivativeL2_ae (ball (0 : ℂ) 1) a 1 u,
    Lp.coeFn_smul Complex.I (h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a 1 u),
    ae_restrict_mem measurableSet_ball] with z hx hy hs hz
  rw [hx, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hy]
  change fderiv ℝ (a : ℂ → ℂ) z 1 * u z =
    Complex.I * (fderiv ℝ (a : ℂ → ℂ) z Complex.I * u z)
  rw [hCR z hz]
  ring

/-- An actual smooth antiholomorphic coefficient preserves the genuine
weak CR equation of the completed disk Hardy extension. -/
theorem diskHardySmoothProduct_cauchyRiemann (a : SmoothH1Coefficient)
    (hCR : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ (a : ℂ → ℂ) z 1 = Complex.I * fderiv ℝ (a : ℂ → ℂ) z Complex.I)
    (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskHardySmoothProduct a b) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (diskHardySmoothProduct a b) := by
  rw [h1Gradient_diskHardySmoothProduct, h1Gradient_diskHardySmoothProduct,
    diskHardyExtension_cauchyRiemann, map_smul,
    hardy_coefficient_derivative_CR a hCR, smul_add]

/-- The product has the genuine all-H¹ trace product, with ordinary dtheta. -/
theorem diskH1Trace_diskHardySmoothProduct (a : SmoothH1Coefficient) (b : L2Z) :
    diskH1Trace (diskHardySmoothProduct a b) =
      h1SmoothBoundaryMultiplier unitCircle_isBoundaryParam a
        (diskH1Trace (diskHardyExtension b)) := by
  exact h1BoundaryTrace_neumannH1SmoothMultiplier
    unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam a
      (diskHardyExtension b)

theorem diskH1Trace_diskHardySmoothProduct_ae (a : SmoothH1Coefficient) (b : L2Z) :
    (diskH1Trace (diskHardySmoothProduct a b) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
        fun θ => a (circleMap 0 1 θ) * diskH1Trace (diskHardyExtension b) θ := by
  rw [diskH1Trace_diskHardySmoothProduct]
  exact h1SmoothBoundaryMultiplier_ae unitCircle_isBoundaryParam a _

theorem diskHalfTrace_diskHardySmoothProduct_apply (a : SmoothH1Coefficient) (b : L2Z) (n : ℤ) :
    diskHalfTrace (diskHardySmoothProduct a b) n =
      (Real.sqrt (sobWeight n) : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) *
        fourierCoeffOn Real.two_pi_pos
          (fun θ => a (circleMap 0 1 θ) * diskH1Trace (diskHardyExtension b) θ) n := by
  rw [diskHalfTrace_apply, boundaryFourier_apply,
    congrFun (fourierCoeffOn_congr_ae Real.two_pi_pos
      (diskH1Trace_diskHardySmoothProduct_ae a b)) n]
  simp only [sobWeight, mul_assoc]

/-- The actual compact coefficient conjugate to the supplied conformal
derivative. It is smooth globally because the actual F is cut off first. -/
def localConformalHardyDerivativeTest {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) : smoothTraceTests :=
  ⟨fun z => conj (dirD (smoothDiskCutoff R hR F) 1 z),
    ((smoothDiskCutoff_testFunction hR hFs).dirD 1).conj⟩

def localConformalHardyDerivativeCoefficient {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) : SmoothH1Coefficient :=
  smoothTraceTestsH1Coefficient (localConformalHardyDerivativeTest hR F hFs)

theorem localConformalHardyDerivativeCoefficient_closedDisk {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    localConformalHardyDerivativeCoefficient hR F hFs z = conj (fderiv ℝ F z 1) := by
  change conj (fderiv ℝ (smoothDiskCutoff R hR F) z 1) = _
  rw [fderiv_smoothDiskCutoff_eq hR F hz]

private theorem hardy_real_derivative_of_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ F z v = deriv F z * v := by
  rw [(hF.differentiableAt (hU.mem_nhds hz)).fderiv_restrictScalars ℝ]
  change fderiv ℂ F z v = _
  exact fderiv_eq_deriv_mul

/-- The actual cutoff coefficient has the derivative of conj(F′) in the
interior, derived from holomorphic F′ and its real chain rule. -/
theorem localConformalHardyDerivativeCoefficient_fderiv {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (v : ℂ) :
    fderiv ℝ (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z v =
      conj (deriv (deriv F) z * v) := by
  have he : (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ)
      =ᶠ[𝓝 z] fun w => conj (deriv F w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    rw [localConformalHardyDerivativeCoefficient_closedDisk hR F hFs (ball_subset_closedBall hw),
      hardy_real_derivative_of_holomorphic isOpen_ball hhol hw 1, mul_one]
  rw [he.fderiv_eq (𝕜 := ℝ)]
  have hd := (hhol.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)
  have h := (Complex.conjCLE.hasFDerivAt.comp z (hd.restrictScalars ℝ).hasFDerivAt).fderiv
  rw [show (fun w => conj (deriv F w)) = Complex.conjCLE ∘ deriv F from rfl, h]
  change conj (fderiv ℝ (deriv F) z v) = _
  rw [hardy_real_derivative_of_holomorphic isOpen_ball (hhol.deriv isOpen_ball) hz v]

theorem localConformalHardyDerivativeCoefficient_cauchyRiemann {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    fderiv ℝ (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z 1 =
      Complex.I * fderiv ℝ
        (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z Complex.I := by
  rw [localConformalHardyDerivativeCoefficient_fderiv hR F hFs hhol hz 1,
    localConformalHardyDerivativeCoefficient_fderiv hR F hFs hhol hz Complex.I]
  simp only [mul_one, map_mul, Complex.conj_I]
  calc
    conj (deriv (deriv F) z) = -(Complex.I * Complex.I) * conj (deriv (deriv F) z) := by
      rw [Complex.I_mul_I]
      simp
    _ = _ := by ring

/-- The genuine disk product needed for the interior physical primitive. -/
def localConformalHardyDerivativeProduct {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    L2Z →L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  diskHardySmoothProduct (localConformalHardyDerivativeCoefficient hR F hFs)

theorem localConformalHardyDerivativeProduct_cauchyRiemann {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0 (localConformalHardyDerivativeProduct hR F hFs b) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1
        (localConformalHardyDerivativeProduct hR F hFs b) :=
  diskHardySmoothProduct_cauchyRiemann _
    (fun _ hz => localConformalHardyDerivativeCoefficient_cauchyRiemann hR F hFs hhol hz) b

/-- Actual angular-velocity multiplier data for the primitive. -/
def localConformalHardyPrimitiveMultiplier (F : ℂ → ℂ) : ℤ → ℂ :=
  fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv (physicalCircleTrace F) θ))

theorem localConformalHardyPrimitiveMultiplier_isWL1 {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    IsWL1 (1 / 2 : ℝ) (localConformalHardyPrimitiveMultiplier F) := by
  have h1 := (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  refine h1.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

theorem localConformalHardyPrimitiveMultiplier_strictNegative {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    IsStrictNegativeFourierSupport (localConformalHardyPrimitiveMultiplier F) :=
  physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood hR F
    (hFs.of_le (by simp)) hhol

/-- The actual supplied-coordinate primitive on normalized half-trace data. -/
def localConformalHardyPrimitive {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) : L2Z →L[ℂ] L2Z :=
  normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
    (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs)

private theorem hardy_fourier_one_circle (θ : ℝ) :
    fourier (T := 2 * Real.pi) 1 (θ : AddCircle (2 * Real.pi)) = circleMap 0 1 θ := by
  rw [fourier_coe_two_pi, circleMap_zero]
  simp only [Int.cast_one, one_mul, Complex.ofReal_one]

/-- The actual boundary coefficient as a continuous circle function. -/
def diskSmoothCoefficientCircle (a : SmoothH1Coefficient) :
    C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨fun q => a (fourier (T := 2 * Real.pi) 1 q),
    a.smooth.continuous.comp (fourier (T := 2 * Real.pi) 1).continuous⟩

theorem diskSmoothCoefficientCircle_apply (a : SmoothH1Coefficient) (θ : ℝ) :
    diskSmoothCoefficientCircle a (θ : AddCircle (2 * Real.pi)) = a (circleMap 0 1 θ) := by
  change a (fourier (T := 2 * Real.pi) 1 (θ : AddCircle (2 * Real.pi))) = _
  rw [hardy_fourier_one_circle]

private theorem hardy_fourierCoeffOn_circle (A : C(AddCircle (2 * Real.pi), ℂ)) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) n =
      fourierCoeff A n := by
  have he : AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) = (A : AddCircle (2 * Real.pi) → ℂ) := by
    funext q
    change A ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) : AddCircle (2 * Real.pi)) = A q
    have hrep : ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) :
        AddCircle (2 * Real.pi)) = q :=
      (AddCircle.equivIoc (2 * Real.pi) 0).symm_apply_apply q
    rw [hrep]
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) n
  rw [he] at h
  simpa only [zero_add] using h.symm

theorem diskSmoothCoefficientCircle_coeff (a : SmoothH1Coefficient) (n : ℤ) :
    fourierCoeff (diskSmoothCoefficientCircle a) n =
      fourierCoeffOn Real.two_pi_pos (fun θ => a (circleMap 0 1 θ)) n := by
  rw [← hardy_fourierCoeffOn_circle]
  congr 1
  funext θ
  exact diskSmoothCoefficientCircle_apply a θ

theorem diskSmoothCoefficientCircle_isWL1 (a : SmoothH1Coefficient) :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (diskSmoothCoefficientCircle a)) := by
  have hf : ContDiff ℝ 4 (fun θ : ℝ => a (circleMap 0 1 θ)) :=
    (a.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_circleMap 0 1)
  have hp : Function.Periodic (fun θ : ℝ => a (circleMap 0 1 θ)) (2 * Real.pi) :=
    (periodic_circleMap 0 1).comp (a : ℂ → ℂ)
  have h2 := (periodic_contDiff_four_fourier_weights hf hp).2
  change Summable (fun n => sobWeight n ^ (1 / 2 : ℝ) *
    ‖fourierCoeff (diskSmoothCoefficientCircle a) n‖)
  simp_rw [diskSmoothCoefficientCircle_coeff]
  refine h2.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

/-- Exact half trace of the completed product, expressed in normalized
convolution coordinates with averaged multiplier coefficients. -/
theorem diskHalfTrace_diskHardySmoothProduct (a : SmoothH1Coefficient) (b : L2Z) :
    diskHalfTrace (diskHardySmoothProduct a b) =
      normalizedHardyMultiplier (fourierCoeff (diskSmoothCoefficientCircle a))
        (diskSmoothCoefficientCircle_isWL1 a) ((1 - posProj) b) := by
  have h := diskHalfTrace_smoothMultiplier a (diskSmoothCoefficientCircle a)
    (diskSmoothCoefficientCircle_apply a) (diskSmoothCoefficientCircle_isWL1 a)
      (diskHardyExtension b)
  rw [diskHalfTrace_diskHardyExtension] at h
  exact h

private theorem hardy_fourierCoeff_shift (C : C(AddCircle (2 * Real.pi), ℂ)) (n : ℤ) :
    fourierCoeff (fun q => fourier (T := 2 * Real.pi) (-1) q * C q) n =
      fourierCoeff C (n + 1) := by
  simp only [fourierCoeff, smul_eq_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by
    change fourier (T := 2 * Real.pi) (-n) q *
      (fourier (T := 2 * Real.pi) (-1) q * C q) =
        fourier (T := 2 * Real.pi) (-(n + 1)) q * C q
    rw [← mul_assoc, ← fourier_add]
    have hi : -n + (-1 : ℤ) = -(n + 1) := by omega
    rw [hi])

/-- The conjugated angular velocity has precisely the shifted coefficient
of conj(F′), including its phase -i. -/
theorem localConformalHardyPrimitiveMultiplier_shift {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (n : ℤ) :
    localConformalHardyPrimitiveMultiplier F n = (-Complex.I) *
      fourierCoeff (diskSmoothCoefficientCircle
        (localConformalHardyDerivativeCoefficient hR F hFs)) (n + 1) := by
  let C := diskSmoothCoefficientCircle (localConformalHardyDerivativeCoefficient hR F hFs)
  let B : C(AddCircle (2 * Real.pi), ℂ) := (-Complex.I) •
    ((fourier (T := 2 * Real.pi) (-1)) * C)
  have he (θ : ℝ) : conj (deriv (physicalCircleTrace F) θ) =
      B (θ : AddCircle (2 * Real.pi)) := by
    rw [localConformal_circleTrace_deriv hR F hFs hhol]
    simp only [map_mul, Complex.conj_I]
    simp only [B, ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul]
    rw [fourier_neg, hardy_fourier_one_circle, diskSmoothCoefficientCircle_apply,
      localConformalHardyDerivativeCoefficient_closedDisk hR F hFs
        (circleMap_mem_closedBall 0 (by norm_num) θ)]
    ring
  change fourierCoeffOn Real.two_pi_pos
    (fun θ => conj (deriv (physicalCircleTrace F) θ)) n = _
  rw [show (fun θ => conj (deriv (physicalCircleTrace F) θ)) =
      (fun θ : ℝ => B (θ : AddCircle (2 * Real.pi))) from funext he,
    hardy_fourierCoeffOn_circle]
  change fourierCoeff ((-Complex.I) •
    (fun q => fourier (T := 2 * Real.pi) (-1) q * C q)) n = _
  rw [fourierCoeff.const_smul]
  simp only [smul_eq_mul]
  rw [hardy_fourierCoeff_shift]

theorem localConformalHardyDerivativeCoefficient_nonpositive {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle
      (localConformalHardyDerivativeCoefficient hR F hFs))) := by
  intro n hn
  have ha := localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol
    (n - 1) (by omega)
  rw [localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol,
    sub_add_cancel] at ha
  exact (mul_eq_zero.mp ha).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)

private theorem hardy_seqConv_nonpositive {c h : ℤ → ℂ}
    (hc : IsNonpositiveFourierSupport c) (hh : IsNonpositiveFourierSupport h) :
    IsNonpositiveFourierSupport (seqConv c h) := by
  intro n hn
  unfold seqConv
  have he : (fun k => c k * h (n - k)) = (fun _ : ℤ => (0 : ℂ)) := by
    funext k
    by_cases hk : 0 < k
    · rw [hc k hk, zero_mul]
    · rw [hh (n - k) (by omega), mul_zero]
  rw [he, tsum_zero]

private theorem hardy_seqConv_shift {a c : ℤ → ℂ}
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1)) (h : ℤ → ℂ) (n : ℤ) :
    seqConv a h (n - 1) = (-Complex.I) * seqConv c h n := by
  unfold seqConv
  calc
    _ = (-Complex.I) * ∑' k : ℤ, c (k + 1) * h (n - (k + 1)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [hshift k]
      have hi : n - 1 - k = n - (k + 1) := by omega
      rw [hi]
      ring
    _ = _ := congrArg (fun x : ℂ => (-Complex.I) * x)
      ((Equiv.addRight (1 : ℤ)).tsum_eq (fun k => c k * h (n - k)))

private theorem hardy_sobWeight_neg_nat (k : ℕ) :
    sobWeight (-(k : ℤ)) = ((k + 1 : ℕ) : ℝ) := by
  simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
    abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k),
    Nat.cast_add, Nat.cast_one]
  ring

private theorem hardy_primitive_derivative_scalar (x y sx sy : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hsy : sy ≠ 0) :
    (x / y * (sx / sy)) * ((sy * y) / (Complex.I * (-x))) * (-Complex.I) = sx := by
  field_simp [hx, hy, hsy, Complex.I_ne_zero]

private theorem hardy_primitive_derivative_scale (k : ℕ) :
    (diskHardyDerivativeWeight k : ℂ) *
        (((sobWeight (-((k + 1 : ℕ) : ℤ)) ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) /
          (Complex.I * (-((k + 1 : ℕ) : ℂ)))) * (-Complex.I) =
      ((sobWeight (-(k : ℤ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [hardy_sobWeight_neg_nat, hardy_sobWeight_neg_nat]
  have hy : (((k + 1 + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + 1)) =
      Real.sqrt ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
    have hi : k + 1 + 1 = k + 2 := by omega
    rw [hi, Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hy, ← Real.sqrt_eq_rpow]
  simp only [diskHardyDerivativeWeight, Real.sqrt_div (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))]
  have hx : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  have hy0 : ((k + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 2 ≠ 0)
  have hsy : (Real.sqrt ((k + 2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ((k + 2 : ℕ) : ℝ))).ne'
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] using
    hardy_primitive_derivative_scalar ((k + 1 : ℕ) : ℂ) ((k + 2 : ℕ) : ℂ)
      (Real.sqrt ((k + 1 : ℕ) : ℝ) : ℂ) (Real.sqrt ((k + 2 : ℕ) : ℝ) : ℂ)
      hx hy0 hsy

/-- The actual derivative-data operator on a normalized primitive is the
actual normalized product data. The input and product retain frequency zero. -/
theorem diskHardyDerivativeData_normalizedPrimitiveGain
    (a c : ℤ → ℂ) (ha : IsWL1 (1 / 2 : ℝ) a) (hc : IsWL1 (1 / 2 : ℝ) c)
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1))
    (hcn : IsNonpositiveFourierSupport c) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b) =
      normalizedHardyMultiplier c hc b := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    intro n hn
    simp only [fromL2, hbn n hn, mul_zero]
  ext n
  by_cases hn : 0 < n
  · rw [diskHardyDerivativeData_apply_pos _ hn, normalizedHardyMultiplier_apply,
      hardy_seqConv_nonpositive hcn hb n hn, mul_zero]
  · let k : ℕ := Int.toNat (-n)
    have hnk : n = -(k : ℤ) := by dsimp [k]; omega
    rw [hnk, diskHardyDerivativeData_apply_neg, normalizedHardyPrimitiveGain_apply,
      normalizedHardyMultiplier_apply]
    have hne : -((k + 1 : ℕ) : ℤ) ≠ 0 := by omega
    rw [antiPrim, if_neg hne, primSeq]
    have hi : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
    have hconv := hardy_seqConv_shift hshift (fromL2 (1 / 2 : ℝ) b) (-(k : ℤ))
    rw [hi] at hconv
    rw [hconv]
    simp only [Int.cast_neg, Int.cast_natCast]
    calc
      _ = ((diskHardyDerivativeWeight k : ℂ) *
          (((sobWeight (-((k + 1 : ℕ) : ℤ)) ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) /
            (Complex.I * (-((k + 1 : ℕ) : ℂ)))) * (-Complex.I)) *
              seqConv c (fromL2 (1 / 2 : ℝ) b) (-(k : ℤ)) := by ring
      _ = _ := by rw [hardy_primitive_derivative_scale]

theorem normalizedHardyMultiplier_nonpositive (c : ℤ → ℂ)
    (hc : IsWL1 (1 / 2 : ℝ) c) (hcn : IsNonpositiveFourierSupport c)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (normalizedHardyMultiplier c hc b) := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    intro n hn
    simp only [fromL2, hbn n hn, mul_zero]
  intro n hn
  rw [normalizedHardyMultiplier_apply, hardy_seqConv_nonpositive hcn hb n hn, mul_zero]

private theorem hardy_trace_eq_of_halfTrace_eq
    (u v : NeumannH1 (ball (0 : ℂ) 1)) (h : diskHalfTrace u = diskHalfTrace v) :
    diskH1Trace u = diskH1Trace v := by
  apply boundaryFourier.injective
  apply lp.ext
  rw [← fromL2_half_diskHalfTrace, ← fromL2_half_diskHalfTrace, h]

/-- The actual completed antiholomorphic product is identified with its
completed Fourier extension by the proved weak CR trace uniqueness theorem. -/
theorem diskHardySmoothProduct_eq_extension (a : SmoothH1Coefficient)
    (hCR : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ (a : ℂ → ℂ) z 1 = Complex.I * fderiv ℝ (a : ℂ → ℂ) z Complex.I)
    (hcn : IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle a)))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    diskHardySmoothProduct a b = diskHardyExtension
      (normalizedHardyMultiplier (fourierCoeff (diskSmoothCoefficientCircle a))
        (diskSmoothCoefficientCircle_isWL1 a) b) := by
  apply neumannH1_eq_of_antiholomorphic_same_trace unitDisk_bounded
    isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
  · exact diskHardySmoothProduct_cauchyRiemann a hCR b
  · exact diskHardyExtension_cauchyRiemann _
  · change diskH1Trace (diskHardySmoothProduct a b) =
      diskH1Trace (diskHardyExtension
        (normalizedHardyMultiplier (fourierCoeff (diskSmoothCoefficientCircle a))
          (diskSmoothCoefficientCircle_isWL1 a) b))
    apply hardy_trace_eq_of_halfTrace_eq
    have hp := diskHalfTrace_smoothMultiplier a (diskSmoothCoefficientCircle a)
      (diskSmoothCoefficientCircle_apply a) (diskSmoothCoefficientCircle_isWL1 a)
      (diskHardyExtension b)
    rw [diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hbn] at hp
    rw [diskHalfTrace_diskHardyExtension_eq_of_nonpositive _
      (normalizedHardyMultiplier_nonpositive _ _ hcn b hbn)]
    exact hp

theorem localConformalHardyDerivativeProduct_eq_extension {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    localConformalHardyDerivativeProduct hR F hFs b = diskHardyExtension
      (normalizedHardyMultiplier
        (fourierCoeff (diskSmoothCoefficientCircle
          (localConformalHardyDerivativeCoefficient hR F hFs)))
        (diskSmoothCoefficientCircle_isWL1
          (localConformalHardyDerivativeCoefficient hR F hFs)) b) :=
  diskHardySmoothProduct_eq_extension _
    (fun _ hz => localConformalHardyDerivativeCoefficient_cauchyRiemann hR F hFs hhol hz)
    (localConformalHardyDerivativeCoefficient_nonpositive hR F hFs hhol) b hbn

/-- Actual disk x derivative of the normalized physical primitive. The
derivative multiplier is the compact smooth representative of conj(F′). -/
theorem diskHardyExtension_localConformalPrimitive_gradient {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (localConformalHardyPrimitive hR F hFs b)) =
      h1SmoothCoefficientL2 (ball (0 : ℂ) 1)
        (localConformalHardyDerivativeCoefficient hR F hFs)
          (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)) := by
  change h1Gradient (ball (0 : ℂ) 1) 0 (diskHardyExtension
    (normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
      (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) b)) = _
  rw [diskHardyExtension_normalizedPrimitive_gradient,
    diskHardyDerivativeData_normalizedPrimitiveGain _ _ _
      (diskSmoothCoefficientCircle_isWL1 (localConformalHardyDerivativeCoefficient hR F hFs))
      (localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol)
      (localConformalHardyDerivativeCoefficient_nonpositive hR F hFs hhol) b hbn,
    ← localConformalHardyDerivativeProduct_eq_extension hR F hFs hhol b hbn]
  exact h1Value_diskHardySmoothProduct _ b

/-- Actual disk y derivative, with the antiholomorphic sign -i. -/
theorem diskHardyExtension_localConformalPrimitive_gradient_y {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (ball (0 : ℂ) 1) 1
        (diskHardyExtension (localConformalHardyPrimitive hR F hFs b)) =
      (-Complex.I) • h1SmoothCoefficientL2 (ball (0 : ℂ) 1)
        (localConformalHardyDerivativeCoefficient hR F hFs)
          (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)) := by
  change h1Gradient (ball (0 : ℂ) 1) 1 (diskHardyExtension
    (normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
      (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) b)) = _
  rw [diskHardyExtension_normalizedPrimitive_gradient_y,
    diskHardyDerivativeData_normalizedPrimitiveGain _ _ _
      (diskSmoothCoefficientCircle_isWL1 (localConformalHardyDerivativeCoefficient hR F hFs))
      (localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol)
      (localConformalHardyDerivativeCoefficient_nonpositive hR F hFs hhol) b hbn,
    ← localConformalHardyDerivativeProduct_eq_extension hR F hFs hhol b hbn]
  dsimp only [localConformalHardyDerivativeProduct]
  rw [h1Value_diskHardySmoothProduct]

/-- The actual L² representative of the disk primitive derivative. -/
theorem diskHardyExtension_localConformalPrimitive_gradient_ae {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    (h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (localConformalHardyPrimitive hR F hFs b)) : ℂ → ℂ)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)] fun z =>
        conj (deriv F z) * h1Value (ball (0 : ℂ) 1) (diskHardyExtension b) z := by
  rw [diskHardyExtension_localConformalPrimitive_gradient hR F hFs hhol b hbn]
  filter_upwards [h1SmoothCoefficientL2_ae (ball (0 : ℂ) 1)
    (localConformalHardyDerivativeCoefficient hR F hFs)
    (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)),
    ae_restrict_mem measurableSet_ball] with z hz hzd
  rw [hz, localConformalHardyDerivativeCoefficient_closedDisk hR F hFs
    (ball_subset_closedBall hzd), hardy_real_derivative_of_holomorphic isOpen_ball hhol hzd 1,
    mul_one]

/-- The normalized primitive preserves the entire Hardy subspace. -/
theorem localConformalHardyPrimitive_nonpositive {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (localConformalHardyPrimitive hR F hFs b) :=
  normalizedHardyPrimitive_nonpositive _ _
    (localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol) b hbn

theorem normalizedHardyAverage_isSobolev (b : L2Z) :
    IsSobolevSeq (1 / 2 : ℝ) (normalizedHardyAverage b) :=
  isSobolevSeq_smul _ (isSobolevSeq_fromL2 (1 / 2 : ℝ) b)

/-- The averaged normalization is exactly the Fourier coefficient of the
actual ordinary disk H¹ trace, without an omitted sqrt(2pi) factor. -/
theorem normalizedHardyAverage_diskHalfTrace (u : NeumannH1 (ball (0 : ℂ) 1)) :
    normalizedHardyAverage (diskHalfTrace u) =
      fourierCoeffOn Real.two_pi_pos (diskH1Trace u) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  have hf := fromL2_half_diskHalfTrace u
  funext n
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * fromL2 (1 / 2 : ℝ) (diskHalfTrace u) n = _
  rw [hf, boundaryFourier_apply, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem normalizedHardyAverage_diskHardyExtension (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    normalizedHardyAverage b =
      fourierCoeffOn Real.two_pi_pos (diskH1Trace (diskHardyExtension b)) := by
  calc
    _ = normalizedHardyAverage (diskHalfTrace (diskHardyExtension b)) :=
      congrArg normalizedHardyAverage
        (diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hbn).symm
    _ = _ := normalizedHardyAverage_diskHalfTrace _

theorem fromL2_normalizedHardyPrimitive (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    fromL2 (1 / 2 : ℝ) (normalizedHardyPrimitive a ha b) =
      antiPrim a (fromL2 (1 / 2 : ℝ) b) := by
  funext n
  rw [fromL2, normalizedHardyPrimitive_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-(1 / 2 : ℝ))), sobWeight_rpow_mul_neg, Complex.ofReal_one,
    one_mul]

/-- Averaged coefficients of the normalized primitive are the same `antiPrim`
coefficients, including its prescribed zero coefficient. -/
theorem normalizedHardyAverage_primitive (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    normalizedHardyAverage (normalizedHardyPrimitive a ha b) =
      antiPrim a (normalizedHardyAverage b) := by
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
      fromL2 (1 / 2 : ℝ) (normalizedHardyPrimitive a ha b) =
    antiPrim a ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ • fromL2 (1 / 2 : ℝ) b)
  rw [fromL2_normalizedHardyPrimitive,
    (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).map_smul _ _
      (isSobolevSeq_fromL2 (1 / 2 : ℝ) b)]

theorem normalizedHardyPrimitive_average_summable (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    Summable (fun n => ‖normalizedHardyAverage (normalizedHardyPrimitive a ha b) n‖) := by
  rw [normalizedHardyAverage_primitive]
  exact (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (antiPrim_bound (by norm_num : (0 : ℝ) ≤ 1 / 2) ha
      (normalizedHardyAverage_isSobolev b)).1).1

/-- The extra order of the true primitive makes its boundary reconstruction
continuous, even for arbitrary normalized L² input data. -/
theorem normalizedHardyPrimitive_boundary_continuous (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    Continuous (hardyFourierTrace
      (normalizedHardyAverage (normalizedHardyPrimitive a ha b))) :=
  continuous_hardyFourierTrace (normalizedHardyPrimitive_average_summable a ha b)

/-- The reconstructed primitive vanishes at the same boundary origin as
`antiPrim`; the Fourier scaling is sqrt(2pi) times lambda to the half power. -/
theorem normalizedHardyPrimitive_boundary_origin (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    hardyFourierTrace (normalizedHardyAverage (normalizedHardyPrimitive a ha b)) 0 = 0 := by
  rw [normalizedHardyAverage_primitive]
  simp only [hardyFourierTrace, AddCircle.coe_zero, fourier_eval_zero, mul_one]
  exact tsum_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha
    (normalizedHardyAverage_isSobolev b)

theorem localConformalHardyPrimitive_boundary_origin {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) (b : L2Z) :
    hardyFourierTrace (normalizedHardyAverage (localConformalHardyPrimitive hR F hFs b)) 0 = 0 :=
  normalizedHardyPrimitive_boundary_origin _ _ b

private theorem hardy_phase_mul_massDensity {C : ℝ} (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    localConformalAntiholomorphicPhase F z * localConformalMassDensity F z =
      conj (fderiv ℝ F z 1) := by
  have hd : deriv F z ≠ 0 := by
    intro he
    have h := hC z hz
    rw [he, norm_zero] at h
    norm_num at h
  have hs : (‖fderiv ℝ F z 1‖ : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    rw [hardy_real_derivative_of_holomorphic isOpen_ball hhol hz 1, mul_one]
    exact norm_ne_zero_iff.mpr hd
  change (conj (fderiv ℝ F z 1) / (‖fderiv ℝ F z 1‖ : ℂ)) *
    (‖fderiv ℝ F z 1‖ : ℂ) = _
  exact div_mul_cancel₀ _ hs

/-- Multiplication by actual conj(F′) on pullback values equals the actual
Jacobian phase times the genuine weighted L² pullback of physical values. -/
theorem localConformalHardyDerivativeCoefficient_pullback_value {R C K : ℝ}
    (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    h1SmoothCoefficientL2 (ball (0 : ℂ) 1)
      (localConformalHardyDerivativeCoefficient hR F hFs)
        (h1Value (ball (0 : ℂ) 1) (localConformalH1Pullback hR F hFs hL u)) =
      localConformalAntiholomorphicPhaseMultiplier F
        (localConformalWeightedL2Pullback hR F hFs hL hK
          (h1Value (F '' ball (0 : ℂ) 1) u)) := by
  rw [localConformalWeightedL2Pullback_h1Value hR F hFs hb hL hhol hinj hC hK,
    localConformalMassPullback_apply]
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientL2_ae (ball (0 : ℂ) 1)
    (localConformalHardyDerivativeCoefficient hR F hFs)
    (h1Value (ball (0 : ℂ) 1) (localConformalH1Pullback hR F hFs hL u)),
    localConformalAntiholomorphicPhaseMultiplier_ae F
      (lpBoundedMultiplier (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK)
        (h1Value (ball (0 : ℂ) 1) (localConformalH1Pullback hR F hFs hL u))),
    lpBoundedMultiplier_ae (localConformalMassDensity F)
      (localConformalMassDensity_aemeasurable hR F hFs)
      (localConformalMassDensity_ae_bound F hK)
      (h1Value (ball (0 : ℂ) 1) (localConformalH1Pullback hR F hFs hL u)),
    ae_restrict_mem measurableSet_ball] with z ha hp hm hz
  rw [ha, hp, hm,
    localConformalHardyDerivativeCoefficient_closedDisk hR F hFs (ball_subset_closedBall hz),
    ← mul_assoc, hardy_phase_mul_massDensity F hhol hC hz]

section PhysicalPrimitive

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

/-- The actual physical H¹ primitive of normalized data, constructed by the
bounded Fourier primitive and the genuine supplied-coordinate H¹ extension. -/
def localConformalHardyH1Primitive :
    L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes).comp
    (localConformalHardyPrimitive hR F hFs)

theorem localConformalDiskHalfTrace_hardyPrimitive (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    localConformalDiskHalfTrace hR F hFs hL
      (localConformalHardyH1Primitive hR F hFs hb hL hhol hinj hC hK e he hsource hes b) =
        localConformalHardyPrimitive hR F hFs b :=
  localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL hhol hinj
    hC hK e he hsource hes _ (localConformalHardyPrimitive_nonpositive hR F hFs hhol b hbn)

/-- The primitive has the actual physical x derivative U(b), proved from
the disk derivative identity and cancellation of the genuine Jacobian phase
and the norm-preserving physical L² pullback. -/
theorem localConformalHardyH1Extension_primitive_gradient (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (F '' ball (0 : ℂ) 1) 0
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (localConformalHardyPrimitive hR F hFs b)) =
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) := by
  apply localConformalWeightedL2Pullback_injective hR F hFs hb hL hhol hinj hC hK
  apply localConformalAntiholomorphicPhaseMultiplier_injective F hhol hC
  calc
    _ = h1Gradient (ball (0 : ℂ) 1) 0 (localConformalH1Pullback hR F hFs hL
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (localConformalHardyPrimitive hR F hFs b))) :=
      (localConformalH1Pullback_gradient_antiholomorphic hR F hFs hb hL hhol hinj hC hK _
        (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
          e he hsource hes _)).symm
    _ = h1Gradient (ball (0 : ℂ) 1) 0
      (diskHardyExtension (localConformalHardyPrimitive hR F hFs b)) := by
        rw [localConformalH1Pullback_hardyExtension]
    _ = h1SmoothCoefficientL2 (ball (0 : ℂ) 1)
      (localConformalHardyDerivativeCoefficient hR F hFs)
        (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)) :=
      diskHardyExtension_localConformalPrimitive_gradient hR F hFs hhol b hbn
    _ = _ := by
      have h := localConformalHardyDerivativeCoefficient_pullback_value hR F hFs hb hL
        hhol hinj hC hK
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b)
      rw [localConformalH1Pullback_hardyExtension] at h
      exact h

/-- The physical y derivative has the true antiholomorphic sign. -/
theorem localConformalHardyH1Extension_primitive_gradient_y (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (F '' ball (0 : ℂ) 1) 1
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (localConformalHardyPrimitive hR F hFs b)) =
      (-Complex.I) • h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) := by
  calc
    _ = (-Complex.I) • h1Gradient (F '' ball (0 : ℂ) 1) 0
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (localConformalHardyPrimitive hR F hFs b)) := by
      rw [localConformalHardyH1Extension_cauchyRiemann, smul_smul]
      simp
    _ = _ := by rw [localConformalHardyH1Extension_primitive_gradient hR F hFs hb hL
      hhol hinj hC hK e he hsource hes b hbn]

theorem localConformalHardyH1Primitive_gradient (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (F '' ball (0 : ℂ) 1) 0
      (localConformalHardyH1Primitive hR F hFs hb hL hhol hinj hC hK e he hsource hes b) =
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) :=
  localConformalHardyH1Extension_primitive_gradient hR F hFs hb hL hhol hinj hC hK
    e he hsource hes b hbn

theorem localConformalHardyH1Primitive_gradient_y (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (F '' ball (0 : ℂ) 1) 1
      (localConformalHardyH1Primitive hR F hFs hb hL hhol hinj hC hK e he hsource hes b) =
      (-Complex.I) • h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) :=
  localConformalHardyH1Extension_primitive_gradient_y hR F hFs hb hL hhol hinj hC hK
    e he hsource hes b hbn

end PhysicalPrimitive

end PolyaNeumann

end
