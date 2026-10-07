module

public import RequestProject.TraceH1
public import RequestProject.LpBoundedMultiplier

/-!
# Multiplication in the actual weak-gradient H¹ space

A globally smooth coefficient with bounded value and first derivatives defines
a genuine bounded H¹ multiplication operator. The product rule is proved by
testing the original weak gradient against the compact product aφ. Smooth
compact coefficients supply the bounds, so this applies to actual cutoff
coordinate functions without an assumed weak product rule.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped Topology

/-- Bounds on an actual smooth coefficient and its two real derivatives. -/
structure SmoothH1Coefficient where
  toFun : ℂ → ℂ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  value_bound : ∀ z, ‖toFun z‖ ≤ bound
  derivative_bound : ∀ (i : Fin 2) z, ‖fderiv ℝ toFun z (coordDir i)‖ ≤ bound

instance : CoeFun SmoothH1Coefficient (fun _ => ℂ → ℂ) := ⟨SmoothH1Coefficient.toFun⟩

/-- Smooth compact coefficients have actual global value and derivative bounds. -/
theorem smoothTraceTests_exists_h1Coefficient_bound (a : smoothTraceTests) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ z, ‖a z‖ ≤ B) ∧
      ∀ (i : Fin 2) z, ‖fderiv ℝ (a : ℂ → ℂ) z (coordDir i)‖ ≤ B := by
  obtain ⟨B, hB⟩ := a.property.2.1.exists_bound_of_continuous a.property.1.continuous
  obtain ⟨B₀, hB₀⟩ := (a.property.dirD (coordDir 0)).2.1.exists_bound_of_continuous
    (a.property.dirD (coordDir 0)).1.continuous
  obtain ⟨B₁, hB₁⟩ := (a.property.dirD (coordDir 1)).2.1.exists_bound_of_continuous
    (a.property.dirD (coordDir 1)).1.continuous
  refine ⟨max 0 (max B (max B₀ B₁)), le_max_left _ _, ?_, ?_⟩
  · intro z
    exact (hB z).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro i z
    fin_cases i
    · exact (hB₀ z).trans ((le_max_left _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    · exact (hB₁ z).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))

/-- An actual compact smooth function as a bounded H¹ coefficient. -/
def smoothTraceTestsH1Coefficient (a : smoothTraceTests) : SmoothH1Coefficient where
  toFun := a
  smooth := a.property.1
  bound := Classical.choose (smoothTraceTests_exists_h1Coefficient_bound a)
  bound_nonneg := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).1
  value_bound := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).2.1
  derivative_bound := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).2.2

@[simp] theorem smoothTraceTestsH1Coefficient_apply (a : smoothTraceTests) (z : ℂ) :
    smoothTraceTestsH1Coefficient a z = a z := rfl

theorem coefficient_derivative_continuous (a : SmoothH1Coefficient) (i : Fin 2) :
    Continuous (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i)) :=
  ((a.smooth.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiff_const).continuous

def h1SmoothCoefficientL2 (Ω : Set ℂ) (a : SmoothH1Coefficient) : L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (a : ℂ → ℂ) a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound)

def h1SmoothCoefficientDerivativeL2 (Ω : Set ℂ) (a : SmoothH1Coefficient) (i : Fin 2) :
    L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (Eventually.of_forall (a.derivative_bound i))

theorem h1SmoothCoefficientL2_ae (Ω : Set ℂ) (a : SmoothH1Coefficient) (u : L2 Ω) :
    (h1SmoothCoefficientL2 Ω a u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun z => a z * u z :=
  lpBoundedMultiplier_ae (a : ℂ → ℂ) a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound) u

theorem h1SmoothCoefficientDerivativeL2_ae (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (i : Fin 2) (u : L2 Ω) :
    (h1SmoothCoefficientDerivativeL2 Ω a i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i) * u z :=
  lpBoundedMultiplier_ae (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (Eventually.of_forall (a.derivative_bound i)) u

theorem norm_h1SmoothCoefficientL2_apply_le (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : L2 Ω) : ‖h1SmoothCoefficientL2 Ω a u‖ ≤ a.bound * ‖u‖ :=
  norm_lpBoundedMulLin_le (a : ℂ → ℂ) a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound) u

theorem norm_h1SmoothCoefficientDerivativeL2_apply_le (Ω : Set ℂ)
    (a : SmoothH1Coefficient) (i : Fin 2) (u : L2 Ω) :
    ‖h1SmoothCoefficientDerivativeL2 Ω a i u‖ ≤ a.bound * ‖u‖ :=
  norm_lpBoundedMulLin_le (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (Eventually.of_forall (a.derivative_bound i)) u

theorem coefficient_test_mul {Ω : Set ℂ} (a : SmoothH1Coefficient)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) : TestFunction Ω (fun z => a z * φ z) :=
  ⟨a.smooth.mul hφ.1, hφ.2.1.mul_left, tsupport_mul_subset_right.trans hφ.2.2⟩

private theorem coefficient_test_mul_fderiv (a : SmoothH1Coefficient)
    {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) (z : ℂ) (i : Fin 2) :
    fderiv ℝ (fun w => a w * φ w) z (coordDir i) =
      fderiv ℝ (a : ℂ → ℂ) z (coordDir i) * φ z +
        a z * fderiv ℝ φ z (coordDir i) := by
  rw [fderiv_fun_mul (a.smooth.differentiable (by simp) z)
    (hφ.1.differentiable (by simp) z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The genuine weak product rule, with both derivative terms in actual L². -/
theorem isWeakGradient_h1SmoothCoefficientL2 {Ω : Set ℂ} (a : SmoothH1Coefficient)
    {u : L2 Ω} {g : Fin 2 → L2 Ω} (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (h1SmoothCoefficientL2 Ω a u)
      (fun i => h1SmoothCoefficientL2 Ω a (g i) +
        h1SmoothCoefficientDerivativeL2 Ω a i u) := by
  intro φ hφ i
  have hweak := hu (fun z => a z * φ z) (coefficient_test_mul a hφ) i
  have hid : Integrable (fun z => h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z)
      (volume.restrict Ω) :=
    (Lp.memLp (h1SmoothCoefficientDerivativeL2 Ω a i u)).integrable_mul hφ.memLp
  have hif : Integrable (fun z => h1SmoothCoefficientL2 Ω a u z *
      fderiv ℝ φ z (coordDir i)) (volume.restrict Ω) :=
    (Lp.memLp (h1SmoothCoefficientL2 Ω a u)).integrable_mul (hφ.memLp_fderiv (coordDir i))
  have hig : Integrable (fun z => h1SmoothCoefficientL2 Ω a (g i) z * φ z)
      (volume.restrict Ω) :=
    (Lp.memLp (h1SmoothCoefficientL2 Ω a (g i))).integrable_mul hφ.memLp
  have hleft : (∫ z in Ω, u z * fderiv ℝ (fun w => a w * φ w) z (coordDir i)) =
      (∫ z in Ω, h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z) +
        ∫ z in Ω, h1SmoothCoefficientL2 Ω a u z * fderiv ℝ φ z (coordDir i) := by
    calc
      _ = ∫ z in Ω, h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z +
          h1SmoothCoefficientL2 Ω a u z * fderiv ℝ φ z (coordDir i) := by
        apply integral_congr_ae
        filter_upwards [h1SmoothCoefficientL2_ae Ω a u,
          h1SmoothCoefficientDerivativeL2_ae Ω a i u] with z hz hdz
        rw [coefficient_test_mul_fderiv a hφ z i, hz, hdz]
        ring
      _ = _ := integral_add hid hif
  have hright : (∫ z in Ω, (g i) z * (a z * φ z)) =
      ∫ z in Ω, h1SmoothCoefficientL2 Ω a (g i) z * φ z := by
    apply integral_congr_ae
    filter_upwards [h1SmoothCoefficientL2_ae Ω a (g i)] with z hz
    rw [hz]
    ring
  have hout : (∫ z in Ω,
      ((h1SmoothCoefficientL2 Ω a (g i) + h1SmoothCoefficientDerivativeL2 Ω a i u : L2 Ω) :
        ℂ → ℂ) z * φ z) =
      (∫ z in Ω, h1SmoothCoefficientL2 Ω a (g i) z * φ z) +
        ∫ z in Ω, h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z := by
    calc
      _ = ∫ z in Ω, h1SmoothCoefficientL2 Ω a (g i) z * φ z +
          h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (h1SmoothCoefficientL2 Ω a (g i))
          (h1SmoothCoefficientDerivativeL2 Ω a i u)] with z hz
        rw [hz]
        simp only [Pi.add_apply, add_mul]
      _ = _ := integral_add hig hid
  rw [hleft, hright] at hweak
  rw [hout]
  linear_combination hweak

theorem smooth_coefficient_h1_ext {Ω : Set ℂ} {u v : NeumannH1 Ω}
    (hv : h1Value Ω u = h1Value Ω v)
    (hg : ∀ i : Fin 2, h1Gradient Ω i u = h1Gradient Ω i v) : u = v := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

def smoothCoefficientH1Vector (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u))

theorem smoothCoefficientH1Vector_value (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) :
    h1Value Ω (smoothCoefficientH1Vector Ω a u) = h1SmoothCoefficientL2 Ω a (h1Value Ω u) :=
  h1Value_h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u))

theorem smoothCoefficientH1Vector_gradient (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (smoothCoefficientH1Vector Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
        h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  h1Gradient_h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u)) i

def smoothCoefficientH1Lin (Ω : Set ℂ) (a : SmoothH1Coefficient) :
    NeumannH1 Ω →ₗ[ℂ] NeumannH1 Ω where
  toFun := smoothCoefficientH1Vector Ω a
  map_add' u v := by
    apply smooth_coefficient_h1_ext
    · simp only [smoothCoefficientH1Vector_value, map_add]
    · intro i
      simp only [smoothCoefficientH1Vector_gradient, map_add]
      abel
  map_smul' c u := by
    apply smooth_coefficient_h1_ext
    · simp only [smoothCoefficientH1Vector_value, map_smul, RingHom.id_apply]
    · intro i
      simp only [smoothCoefficientH1Vector_gradient, map_smul, smul_add, RingHom.id_apply]

private theorem smoothCoefficientH1Lin_value (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) :
    h1Value Ω (smoothCoefficientH1Lin Ω a u) = h1SmoothCoefficientL2 Ω a (h1Value Ω u) :=
  smoothCoefficientH1Vector_value Ω a u

private theorem smoothCoefficientH1Lin_gradient (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (smoothCoefficientH1Lin Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
        h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  smoothCoefficientH1Vector_gradient Ω a u i

private theorem smooth_real_component_bounds {r a b c : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : r ^ 2 = a ^ 2 + (b ^ 2 + c ^ 2)) :
    a ≤ r ∧ b ≤ r ∧ c ≤ r := by
  constructor
  · apply (sq_le_sq₀ ha hr).mp
    nlinarith [sq_nonneg b, sq_nonneg c]
  constructor
  · apply (sq_le_sq₀ hb hr).mp
    nlinarith [sq_nonneg a, sq_nonneg c]
  · apply (sq_le_sq₀ hc hr).mp
    nlinarith [sq_nonneg a, sq_nonneg b]

private theorem smooth_coefficient_component_norm_le {Ω : Set ℂ} (u : NeumannH1 Ω) :
    ‖h1Value Ω u‖ ≤ ‖u‖ ∧ ∀ i : Fin 2, ‖h1Gradient Ω i u‖ ≤ ‖u‖ := by
  have hs := h1_norm_sq Ω u
  rw [Fin.sum_univ_two] at hs
  have hc := smooth_real_component_bounds (norm_nonneg u) (norm_nonneg (h1Value Ω u))
    (norm_nonneg (h1Gradient Ω 0 u)) (norm_nonneg (h1Gradient Ω 1 u)) hs
  refine ⟨hc.1, ?_⟩
  intro i
  fin_cases i
  · exact hc.2.1
  · exact hc.2.2

private theorem smooth_real_three_component_norm_le {r a b c A : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hs : r ^ 2 = a ^ 2 + (b ^ 2 + c ^ 2))
    (hva : a ≤ A) (hvb : b ≤ A) (hvc : c ≤ A) :
    r ≤ Real.sqrt 3 * A := by
  have hsa : a ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ ha hva 2
  have hsb : b ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hb hvb 2
  have hsc : c ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hc hvc 2
  apply (sq_le_sq₀ hr (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith

private theorem smooth_coefficient_norm_le_of_components {Ω : Set ℂ}
    (u : NeumannH1 Ω) {A : ℝ} (hA : 0 ≤ A)
    (hv : ‖h1Value Ω u‖ ≤ A) (hg : ∀ i : Fin 2, ‖h1Gradient Ω i u‖ ≤ A) :
    ‖u‖ ≤ Real.sqrt 3 * A := by
  have hs := h1_norm_sq Ω u
  rw [Fin.sum_univ_two] at hs
  exact smooth_real_three_component_norm_le (norm_nonneg u) (norm_nonneg (h1Value Ω u))
    (norm_nonneg (h1Gradient Ω 0 u)) (norm_nonneg (h1Gradient Ω 1 u)) hA hs hv (hg 0) (hg 1)

theorem smoothCoefficientH1Lin_norm_le (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) :
    ‖smoothCoefficientH1Lin Ω a u‖ ≤ (2 * Real.sqrt 3 * a.bound) * ‖u‖ := by
  have hc := smooth_coefficient_component_norm_le u
  have hv : ‖h1Value Ω (smoothCoefficientH1Lin Ω a u)‖ ≤ 2 * a.bound * ‖u‖ := by
    rw [smoothCoefficientH1Lin_value]
    exact (norm_h1SmoothCoefficientL2_apply_le Ω a _).trans
      ((mul_le_mul_of_nonneg_left hc.1 a.bound_nonneg).trans
        (by nlinarith [norm_nonneg u, a.bound_nonneg]))
  have hg (i : Fin 2) :
      ‖h1Gradient Ω i (smoothCoefficientH1Lin Ω a u)‖ ≤ 2 * a.bound * ‖u‖ := by
    rw [smoothCoefficientH1Lin_gradient]
    calc
      _ ≤ ‖h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u)‖ +
          ‖h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u)‖ := norm_add_le _ _
      _ ≤ a.bound * ‖h1Gradient Ω i u‖ + a.bound * ‖h1Value Ω u‖ :=
        add_le_add (norm_h1SmoothCoefficientL2_apply_le Ω a _)
          (norm_h1SmoothCoefficientDerivativeL2_apply_le Ω a i _)
      _ ≤ a.bound * ‖u‖ + a.bound * ‖u‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hc.2 i) a.bound_nonneg)
          (mul_le_mul_of_nonneg_left hc.1 a.bound_nonneg)
      _ = _ := by ring
  have hn := smooth_coefficient_norm_le_of_components (smoothCoefficientH1Lin Ω a u)
    (mul_nonneg (mul_nonneg (by norm_num) a.bound_nonneg) (norm_nonneg u)) hv hg
  convert hn using 1; ring

/-- Actual bounded multiplication in H¹, with no regularity premise on the input. -/
def neumannH1SmoothMultiplier (Ω : Set ℂ) (a : SmoothH1Coefficient) :
    NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  (smoothCoefficientH1Lin Ω a).mkContinuous (2 * Real.sqrt 3 * a.bound)
    (smoothCoefficientH1Lin_norm_le Ω a)

theorem h1Value_neumannH1SmoothMultiplier (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) :
    h1Value Ω (neumannH1SmoothMultiplier Ω a u) = h1SmoothCoefficientL2 Ω a (h1Value Ω u) :=
  smoothCoefficientH1Vector_value Ω a u

theorem h1Gradient_neumannH1SmoothMultiplier (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (neumannH1SmoothMultiplier Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
        h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  smoothCoefficientH1Vector_gradient Ω a u i

theorem h1Value_neumannH1SmoothMultiplier_ae (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) :
    (h1Value Ω (neumannH1SmoothMultiplier Ω a u) : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => a z * h1Value Ω u z := by
  rw [h1Value_neumannH1SmoothMultiplier]
  exact h1SmoothCoefficientL2_ae Ω a (h1Value Ω u)

theorem norm_neumannH1SmoothMultiplier_apply_le (Ω : Set ℂ) (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) :
    ‖neumannH1SmoothMultiplier Ω a u‖ ≤ (2 * Real.sqrt 3 * a.bound) * ‖u‖ :=
  smoothCoefficientH1Lin_norm_le Ω a u

theorem norm_neumannH1SmoothMultiplier_le (Ω : Set ℂ) (a : SmoothH1Coefficient) :
    ‖neumannH1SmoothMultiplier Ω a‖ ≤ 2 * Real.sqrt 3 * a.bound :=
  (neumannH1SmoothMultiplier Ω a).opNorm_le_bound
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) a.bound_nonneg)
    (norm_neumannH1SmoothMultiplier_apply_le Ω a)

def smoothCoefficientTestProduct (a : SmoothH1Coefficient) (f : smoothTraceTests) :
    smoothTraceTests :=
  ⟨fun z => a z * f z, coefficient_test_mul a f.property⟩

@[simp] theorem smoothCoefficientTestProduct_apply (a : SmoothH1Coefficient)
    (f : smoothTraceTests) (z : ℂ) : smoothCoefficientTestProduct a f z = a z * f z := rfl

/-- The completed product agrees with the actual compact smooth product. -/
theorem neumannH1SmoothMultiplier_smooth {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (a : SmoothH1Coefficient) (f : smoothTraceTests) :
    neumannH1SmoothMultiplier Ω a (smoothTraceH1 Ω f) =
      smoothTraceH1 Ω (smoothCoefficientTestProduct a f) := by
  apply h1Value_injective hΩ
  simp only [h1Value_neumannH1SmoothMultiplier, h1Value_smoothTraceH1]
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientL2_ae Ω a (h1Value Ω (smoothTraceH1 Ω f)),
    (smoothTraceTests_memLp Ω f).coeFn_toLp,
    (smoothTraceTests_memLp Ω (smoothCoefficientTestProduct a f)).coeFn_toLp]
    with z hm hf hp
  simp only [h1Value_smoothTraceH1] at hm
  rw [hm, hf, hp]
  rfl

/-- Multiplication by the actual boundary values of the same coefficient. -/
def h1SmoothBoundaryMultiplier {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  lpBoundedMultiplier (fun θ => a (γ θ))
    (a.smooth.continuous.comp hγ.lipschitz.choose_spec.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun θ => a.value_bound (γ θ)))

theorem h1SmoothBoundaryMultiplier_ae {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) (g : BoundaryL2) :
    (h1SmoothBoundaryMultiplier hγ a g : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] fun θ => a (γ θ) * g θ :=
  lpBoundedMultiplier_ae (fun θ => a (γ θ))
    (a.smooth.continuous.comp hγ.lipschitz.choose_spec.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun θ => a.value_bound (γ θ))) g

/-- The physical trace product rule for every actual H¹ vector follows from
the dense smooth restrictions and the two already bounded product operators. -/
theorem h1BoundaryTrace_neumannH1SmoothMultiplier {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) (u : NeumannH1 Ω) :
    h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a u) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ u) := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a v) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ v)) u ?_ ?_
  · exact isClosed_eq ((h1BoundaryTrace hb hL hγ).continuous.comp
      (neumannH1SmoothMultiplier Ω a).continuous)
      ((h1SmoothBoundaryMultiplier hγ a).continuous.comp (h1BoundaryTrace hb hL hγ).continuous)
  · intro f
    change h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a (smoothTraceH1 Ω f)) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f))
    rw [neumannH1SmoothMultiplier_smooth hL.1.1]
    apply Lp.ext
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ (smoothCoefficientTestProduct a f),
      h1SmoothBoundaryMultiplier_ae hγ a (h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f)),
      h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hp hm hf
    rw [hp, hm, hf]
    rfl

end PolyaNeumann

end
