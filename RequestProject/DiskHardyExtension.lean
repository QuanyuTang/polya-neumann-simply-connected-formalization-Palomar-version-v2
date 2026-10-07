module

public import RequestProject.DiskWeakModes
public import RequestProject.DiskAreaBessel
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The genuine antiholomorphic H¹ extension on the disk

The construction uses the actual compactly supported harmonic test vectors.
Their H¹ Gram matrix includes both area mass and gradient energy, including
the constant mode. Orthogonal synthesis completes their finite sums in the
physical H¹ space; applying the continuous half trace recovers exactly the
nonpositive Fourier projection. No harmonic extension theorem is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace Topology ENNReal

abbrev DiskHardyCoefficients := lp (fun _ : ℕ => ℂ) 2

/-- The full physical H¹ mass of the mode `conj(z)^m`. -/
def diskAntiholomorphicH1Weight (m : ℕ) : ℝ :=
  π / ((m + 1 : ℕ) : ℝ) + 2 * π * (m : ℝ)

theorem diskAntiholomorphicH1Weight_pos (m : ℕ) :
    0 < diskAntiholomorphicH1Weight m := by
  unfold diskAntiholomorphicH1Weight
  positivity

private theorem hardy_value_antiholomorphicTest (m : ℕ) :
    h1Value (ball (0 : ℂ) 1) (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicArea m :=
  h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

private theorem hardy_gradient_antiholomorphicTest (m n : ℕ) :
    (∑ i : Fin 2,
      ⟪h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m),
        h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test n)⟫_ℂ) =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
  have h := inner_diskAntiholomorphicGradient m n
  rw [← diskH1Gradient_antiholomorphicTest m,
    ← diskH1Gradient_antiholomorphicTest n, PiLp.inner_apply] at h
  exact h

/-- The true H¹ Gram matrix; the zero mode has weight `π`. -/
theorem inner_diskAntiholomorphicH1Test (m n : ℕ) :
    ⟪diskAntiholomorphicH1Test m, diskAntiholomorphicH1Test n⟫_ℂ =
      if m = n then (diskAntiholomorphicH1Weight m : ℂ) else 0 := by
  rw [h1_inner, hardy_value_antiholomorphicTest,
    hardy_value_antiholomorphicTest, inner_diskAntiholomorphicArea,
    hardy_gradient_antiholomorphicTest]
  by_cases hmn : m = n
  · simp only [hmn, ite_true, diskAntiholomorphicH1Weight]
    push_cast
    ring
  · simp [hmn]

private theorem hardy_sqrt_inverse_normalizes {w : ℝ} (hw : 0 < w) :
    conj ((Real.sqrt w : ℂ)⁻¹) *
      ((Real.sqrt w : ℂ)⁻¹ * (w : ℂ)) = 1 := by
  have hs : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  have hr : (Real.sqrt w)⁻¹ * ((Real.sqrt w)⁻¹ * w) = 1 := by
    have hsq : Real.sqrt w * Real.sqrt w = w := by
      simpa only [pow_two] using Real.sq_sqrt hw.le
    calc
      _ = (Real.sqrt w)⁻¹ *
          ((Real.sqrt w)⁻¹ * (Real.sqrt w * Real.sqrt w)) := by rw [hsq]
      _ = 1 := by field_simp [hs]
  simp only [map_inv₀, Complex.conj_ofReal]
  exact_mod_cast hr

private theorem hardy_orthonormal_of_gram
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℕ → H) (w : ℕ → ℝ) (hw : ∀ m, 0 < w m)
    (hgram : ∀ m n, ⟪v m, v n⟫_ℂ =
      if m = n then (w m : ℂ) else 0) :
    Orthonormal ℂ (fun m => (Real.sqrt (w m) : ℂ)⁻¹ • v m) := by
  classical
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst n
    simp only [inner_smul_left, inner_smul_right, hgram, ite_true]
    calc
      _ = conj ((Real.sqrt (w m) : ℂ)⁻¹) *
          ((Real.sqrt (w m) : ℂ)⁻¹ * (w m : ℂ)) := by ring
      _ = 1 := hardy_sqrt_inverse_normalizes (hw m)
  · simp [inner_smul_left, inner_smul_right, hgram, hmn]

/-- Unit vectors in actual disk H¹, with the constant mode retained. -/
def diskUnitAntiholomorphicH1Test (m : ℕ) : NeumannH1 (ball (0 : ℂ) 1) :=
  (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹ •
    diskAntiholomorphicH1Test m

theorem orthonormal_diskUnitAntiholomorphicH1Test :
    Orthonormal ℂ diskUnitAntiholomorphicH1Test :=
  hardy_orthonormal_of_gram diskAntiholomorphicH1Test
    diskAntiholomorphicH1Weight diskAntiholomorphicH1Weight_pos
    inner_diskAntiholomorphicH1Test

/-- The half-trace amplitude of an unscaled antiholomorphic monomial. -/
def diskHardyTraceScale (m : ℕ) : ℝ :=
  Real.sqrt (sobWeight (-(m : ℤ))) * Real.sqrt (2 * π)

theorem diskHardyTraceScale_pos (m : ℕ) : 0 < diskHardyTraceScale m := by
  exact mul_pos (Real.sqrt_pos.mpr (sobWeight_pos _))
    (Real.sqrt_pos.mpr (by positivity))

private theorem hardy_sobWeight_neg_nat (m : ℕ) :
    sobWeight (-(m : ℤ)) = ((m + 1 : ℕ) : ℝ) := by
  simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m), Nat.cast_add, Nat.cast_one]
  ring

theorem diskHardyTraceScale_sq (m : ℕ) :
    diskHardyTraceScale m ^ 2 = 2 * π * ((m + 1 : ℕ) : ℝ) := by
  rw [diskHardyTraceScale, mul_pow, Real.sq_sqrt (sobWeight_pos _).le,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * π), hardy_sobWeight_neg_nat]
  ring

theorem diskAntiholomorphicH1Weight_le_traceScale_sq (m : ℕ) :
    diskAntiholomorphicH1Weight m ≤ diskHardyTraceScale m ^ 2 := by
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hdiv : π / ((m + 1 : ℕ) : ℝ) ≤ π := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  rw [diskAntiholomorphicH1Weight, diskHardyTraceScale_sq]
  push_cast at hm hdiv ⊢
  nlinarith [Real.pi_pos]

/-- The ratio between unit H¹ coordinates and normalized trace coordinates. -/
def diskHardySynthesisWeight (m : ℕ) : ℝ :=
  Real.sqrt (diskAntiholomorphicH1Weight m) / diskHardyTraceScale m

theorem diskHardySynthesisWeight_nonneg (m : ℕ) :
    0 ≤ diskHardySynthesisWeight m := by
  unfold diskHardySynthesisWeight
  exact div_nonneg (Real.sqrt_nonneg _) (diskHardyTraceScale_pos _).le

theorem diskHardySynthesisWeight_le_one (m : ℕ) :
    diskHardySynthesisWeight m ≤ 1 := by
  rw [diskHardySynthesisWeight, div_le_one (diskHardyTraceScale_pos m)]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (diskHardyTraceScale_pos m).le).mp
  rw [Real.sq_sqrt (diskAntiholomorphicH1Weight_pos m).le]
  exact diskAntiholomorphicH1Weight_le_traceScale_sq m

private theorem hardy_nat_memℓp_two_iff_summable {f : ℕ → ℂ} :
    Memℓp f 2 ↔ Summable (fun m => ‖f m‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp

private theorem hardy_negative_index_injective :
    Function.Injective (fun m : ℕ => -(m : ℤ)) := by
  intro m n h
  change -(m : ℤ) = -(n : ℤ) at h
  exact_mod_cast neg_injective h

theorem hardy_weighted_coefficients_memℓp
    (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) (b : L2Z) :
    Memℓp (fun m => w m * b (-(m : ℤ))) 2 := by
  refine hardy_nat_memℓp_two_iff_summable.mpr ?_
  have hs : Summable (fun m : ℕ => ‖b (-(m : ℤ))‖ ^ 2) :=
    (summable_norm_sq_L2Z b).comp_injective hardy_negative_index_injective
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => ?_) hs
  rw [norm_mul, mul_pow]
  calc
    _ ≤ 1 ^ 2 * ‖b (-(m : ℤ))‖ ^ 2 := by gcongr; exact hw m
    _ = _ := by ring

def hardyWeightedCoefficientsLin
    (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) : L2Z →ₗ[ℂ] DiskHardyCoefficients where
  toFun b := ⟨fun m => w m * b (-(m : ℤ)), hardy_weighted_coefficients_memℓp w hw b⟩
  map_add' b c := by
    ext m
    simp [mul_add, Pi.add_apply]
    rfl
  map_smul' a b := by
    ext m
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem hardy_weighted_coefficients_norm_le
    (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) (b : L2Z) :
    ‖hardyWeightedCoefficientsLin w hw b‖ ≤ ‖b‖ := by
  have hsq : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    have hn : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 =
        ∑' m : ℕ, ‖w m * b (-(m : ℤ))‖ ^ 2 := by
      have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
        (hardyWeightedCoefficientsLin w hw b)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
      exact h
    rw [hn, norm_sq_L2Z]
    calc
      _ ≤ ∑' m : ℕ, ‖b (-(m : ℤ))‖ ^ 2 := by
        refine (hardy_nat_memℓp_two_iff_summable.mp
          (lp.memℓp (hardyWeightedCoefficientsLin w hw b))).tsum_le_tsum
          (fun m => ?_) ((summable_norm_sq_L2Z b).comp_injective
            hardy_negative_index_injective)
        change ‖w m * b (-(m : ℤ))‖ ^ 2 ≤ _
        rw [norm_mul, mul_pow]
        calc
          _ ≤ 1 ^ 2 * ‖b (-(m : ℤ))‖ ^ 2 := by gcongr; exact hw m
          _ = _ := by ring
      _ ≤ _ := tsum_comp_le_tsum_of_inj (summable_norm_sq_L2Z b)
        (fun n => sq_nonneg ‖b n‖) hardy_negative_index_injective
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

def hardyWeightedCoefficients
    (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) : L2Z →L[ℂ] DiskHardyCoefficients :=
  (hardyWeightedCoefficientsLin w hw).mkContinuous 1
    (fun b => by simpa using hardy_weighted_coefficients_norm_le w hw b)

theorem hardy_synthesis_weight_bound (m : ℕ) :
    ‖(diskHardySynthesisWeight m : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_of_nonneg (diskHardySynthesisWeight_nonneg m)]
  exact diskHardySynthesisWeight_le_one m

/-- The actual square-summable coordinates used by H¹ orthogonal synthesis. -/
def diskHardyCoefficientMap : L2Z →L[ℂ] DiskHardyCoefficients :=
  hardyWeightedCoefficients (fun m => (diskHardySynthesisWeight m : ℂ))
    hardy_synthesis_weight_bound

theorem diskHardyCoefficientMap_apply (b : L2Z) (m : ℕ) :
    diskHardyCoefficientMap b m =
      (diskHardySynthesisWeight m : ℂ) * b (-(m : ℤ)) := rfl

theorem norm_diskHardyCoefficientMap_apply_le (b : L2Z) :
    ‖diskHardyCoefficientMap b‖ ≤ ‖b‖ :=
  hardy_weighted_coefficients_norm_le
    (fun m => (diskHardySynthesisWeight m : ℂ)) hardy_synthesis_weight_bound b

def hardySynthesisIsometry :
    DiskHardyCoefficients →ₗᵢ[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily.linearIsometry

/-- Harmonic extension of the nonpositive normalized Fourier data, into the
actual weak-gradient H¹ space on the disk. -/
def diskHardyExtension : L2Z →L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  hardySynthesisIsometry.toContinuousLinearMap.comp diskHardyCoefficientMap

theorem norm_diskHardyExtension_apply_le (b : L2Z) :
    ‖diskHardyExtension b‖ ≤ ‖b‖ := by
  change ‖hardySynthesisIsometry (diskHardyCoefficientMap b)‖ ≤ _
  rw [hardySynthesisIsometry.norm_map]
  exact norm_diskHardyCoefficientMap_apply_le b

theorem norm_diskHardyExtension_le_one : ‖diskHardyExtension‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro b
  simpa using norm_diskHardyExtension_apply_le b

private theorem hardy_raw_synthesis_scalar (m : ℕ) (a : ℂ) :
    ((diskHardySynthesisWeight m : ℂ) * a) *
        (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹ =
      a / (diskHardyTraceScale m : ℂ) := by
  have hs : (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (diskAntiholomorphicH1Weight_pos m)).ne'
  rw [diskHardySynthesisWeight, Complex.ofReal_div, div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = ((Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ) *
        (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹) *
        (a * (diskHardyTraceScale m : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hs, one_mul]

/-- Convergence of smooth harmonic partial sums in genuine H¹. The ordinary
boundary coefficient is the normalized coefficient divided by
`sqrt(2π) * sqrt(λ)`, including frequency zero. -/
theorem diskHardyExtension_hasSum (b : L2Z) :
    HasSum (fun m : ℕ => (b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) (diskHardyExtension b) := by
  have hs := (orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily).hasSum_linearIsometry
    (diskHardyCoefficientMap b)
  change HasSum (fun m =>
    (diskHardyCoefficientMap b m) • diskUnitAntiholomorphicH1Test m)
    (diskHardyExtension b) at hs
  convert hs using 1
  funext m
  rw [diskHardyCoefficientMap_apply, diskUnitAntiholomorphicH1Test, smul_smul,
    hardy_raw_synthesis_scalar]

theorem diskHardyExtension_tendsto_partialSum (b : L2Z) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
      (b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
        diskAntiholomorphicH1Test m) atTop (𝓝 (diskHardyExtension b)) :=
  (diskHardyExtension_hasSum b).tendsto_sum_nat

private theorem hardy_trace_term (b : L2Z) (m : ℕ) :
    diskHalfTrace ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) =
        b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)) := by
  have ht : (diskHardyTraceScale m : ℂ) ≠ 0 := by
    exact_mod_cast (diskHardyTraceScale_pos m).ne'
  rw [map_smul, diskHalfTrace_antiholomorphicTest, smul_smul]
  have hc : (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) *
      (Real.sqrt (2 * π) : ℂ) = (diskHardyTraceScale m : ℂ) := by
    simp only [diskHardyTraceScale, Complex.ofReal_mul]
  rw [hc, div_mul_cancel₀ _ ht]

theorem diskHardyExtension_halfTrace_hasSum (b : L2Z) :
    HasSum (fun m : ℕ => b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)))
      (diskHalfTrace (diskHardyExtension b)) := by
  simpa only [hardy_trace_term] using diskHalfTrace.hasSum (diskHardyExtension_hasSum b)

private theorem hardy_inner_stdBasisZ (n : ℤ) (b : L2Z) :
    ⟪stdBasisZ n, b⟫_ℂ = b n := by
  rw [stdBasisZ_apply, lp.inner_single_left]
  simp

private theorem hardy_nonpositive_series_coordinate
    (b x : L2Z)
    (hx : HasSum (fun m : ℕ => b (-(m : ℤ)) • stdBasisZ (-(m : ℤ))) x)
    (n : ℤ) : x n = if 0 < n then 0 else b n := by
  classical
  have hcoord := (innerSL ℂ (stdBasisZ n)).hasSum hx
  have hbasis (m : ℕ) :
      (innerSL ℂ (stdBasisZ n)) (b (-(m : ℤ)) • stdBasisZ (-(m : ℤ))) =
        if n = -(m : ℤ) then b (-(m : ℤ)) else 0 := by
    simp only [innerSL_apply_apply, inner_smul_right,
      orthonormal_iff_ite.mp stdBasisZ.orthonormal]
    split_ifs <;> simp
  simp only [hbasis, innerSL_apply_apply, hardy_inner_stdBasisZ] at hcoord
  rw [← hcoord.tsum_eq]
  by_cases hn : 0 < n
  · simp only [hn, ite_true]
    have hz : (fun m : ℕ => if n = -(m : ℤ) then b (-(m : ℤ)) else 0) =
        (fun _ : ℕ => (0 : ℂ)) := by
      funext m
      have hnm : n ≠ -(m : ℤ) := by omega
      simp [hnm]
    rw [hz]
    simp
  · simp only [hn, ite_false]
    have hn0 : 0 ≤ -n := by omega
    let k : ℕ := Int.toNat (-n)
    have hk : n = -(k : ℤ) := by
      have hc : (k : ℤ) = -n := Int.toNat_of_nonneg hn0
      omega
    rw [tsum_eq_single k]
    · simp [← hk]
    · intro m hm
      have hnm : n ≠ -(m : ℤ) := by omega
      simp [hnm]

/-- The extension has precisely the nonpositive normalized half trace. -/
theorem diskHalfTrace_diskHardyExtension_apply (b : L2Z) (n : ℤ) :
    diskHalfTrace (diskHardyExtension b) n = if 0 < n then 0 else b n :=
  hardy_nonpositive_series_coordinate b _ (diskHardyExtension_halfTrace_hasSum b) n

theorem diskHalfTrace_diskHardyExtension (b : L2Z) :
    diskHalfTrace (diskHardyExtension b) = (1 - posProj) b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    lp.coeFn_sub, Pi.sub_apply, posProj, diagOp_apply]
  split_ifs <;> simp

theorem diskHalfTrace_comp_diskHardyExtension :
    diskHalfTrace.comp diskHardyExtension = 1 - posProj := by
  apply ContinuousLinearMap.ext
  intro b
  exact diskHalfTrace_diskHardyExtension b

theorem diskHalfTrace_diskHardyExtension_zero (b : L2Z) :
    diskHalfTrace (diskHardyExtension b) 0 = b 0 := by
  simp only [diskHalfTrace_diskHardyExtension_apply, lt_self_iff_false, ite_false]

/-- A bounded genuine H¹ right inverse on the nonpositive Fourier subspace. -/
theorem diskHalfTrace_diskHardyExtension_eq_of_nonpositive (b : L2Z)
    (hb : ∀ n : ℤ, 0 < n → b n = 0) :
    diskHalfTrace (diskHardyExtension b) = b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  by_cases hn : 0 < n
  · simp [hn, hb n hn]
  · simp [hn]

private theorem hardy_antiholomorphic_gradient_components (m : ℕ) :
    diskAntiholomorphicGradient m 0 =
      Complex.I • diskAntiholomorphicGradient m 1 := by
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae m 0,
    diskAntiholomorphicGradient_ae m 1,
    Lp.coeFn_smul Complex.I (diskAntiholomorphicGradient m 1)] with z hx hy hsmul
  rw [hx, hsmul]
  change dirD (diskAntiholomorphicMode m) (coordDir 0) z =
    Complex.I * ((diskAntiholomorphicGradient m 1 : ℂ → ℂ) z)
  rw [hy]
  simp only [dirD_diskAntiholomorphicMode,
    show coordDir 0 = (1 : ℂ) from rfl,
    show coordDir 1 = Complex.I from rfl,
    map_one, Complex.conj_I, mul_one]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem hardy_gradient_component_antiholomorphicTest (m : ℕ) (i : Fin 2) :
    h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicGradient m i := by
  have h := congrArg (fun G : DiskGradientSpace => G i)
    (diskH1Gradient_antiholomorphicTest m)
  simpa only [diskH1Gradient, PiLp.toLp_apply] using h

theorem diskAntiholomorphicH1Test_cauchyRiemann (m : ℕ) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test m) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (diskAntiholomorphicH1Test m) := by
  rw [hardy_gradient_component_antiholomorphicTest,
    hardy_gradient_component_antiholomorphicTest]
  exact hardy_antiholomorphic_gradient_components m

/-- The weak antiholomorphic derivative, without an inessential scalar factor. -/
def diskAntiholomorphicDefect :
    NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  h1Gradient (ball (0 : ℂ) 1) 0 -
    Complex.I • h1Gradient (ball (0 : ℂ) 1) 1

private theorem hardy_antiholomorphic_defect_test (m : ℕ) :
    diskAntiholomorphicDefect (diskAntiholomorphicH1Test m) = 0 := by
  simp only [diskAntiholomorphicDefect, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, diskAntiholomorphicH1Test_cauchyRiemann,
    sub_self]

theorem diskAntiholomorphicDefect_diskHardyExtension (b : L2Z) :
    diskAntiholomorphicDefect (diskHardyExtension b) = 0 := by
  have hs := diskAntiholomorphicDefect.hasSum (diskHardyExtension_hasSum b)
  have hs0 : HasSum (fun _ : ℕ => (0 : L2 (ball (0 : ℂ) 1)))
      (diskAntiholomorphicDefect (diskHardyExtension b)) := by
    simpa only [map_smul, hardy_antiholomorphic_defect_test, smul_zero] using hs
  exact hs0.unique hasSum_zero

/-- The completed H¹ vector is genuinely weakly antiholomorphic. -/
theorem diskHardyExtension_cauchyRiemann (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskHardyExtension b) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (diskHardyExtension b) := by
  apply sub_eq_zero.mp
  exact diskAntiholomorphicDefect_diskHardyExtension b

theorem diskHardyExtension_fourierCoeff (b : L2Z) (m : ℕ) :
    fourierCoeffOn two_pi_pos
      (diskH1Trace (diskHardyExtension b) : ℝ → ℂ) (-(m : ℤ)) =
        b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ) := by
  have ht : (diskHardyTraceScale m : ℂ) ≠ 0 := by
    exact_mod_cast (diskHardyTraceScale_pos m).ne'
  have h := diskHalfTrace_diskHardyExtension_apply b (-(m : ℤ))
  rw [diskHalfTrace_apply, boundaryFourier_apply] at h
  have hn : ¬ (0 : ℤ) < -(m : ℤ) := by omega
  simp only [hn, ite_false] at h
  apply (eq_div_iff ht).mpr
  calc
    _ = (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) *
        ((Real.sqrt (2 * π) : ℂ) *
          fourierCoeffOn two_pi_pos
            (diskH1Trace (diskHardyExtension b) : ℝ → ℂ) (-(m : ℤ))) := by
      simp only [diskHardyTraceScale, Complex.ofReal_mul]
      ring
    _ = _ := h

theorem dirD_comm_of_contDiff {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v w z : ℂ) :
    dirD (dirD φ v) w z = dirD (dirD φ w) v z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiable (by simp) z
  have hv : fderiv ℝ (dirD φ v) z w = fderiv ℝ (fderiv ℝ φ) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ φ x v) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hw : fderiv ℝ (dirD φ w) z v = fderiv ℝ (fderiv ℝ φ) z v w := by
    change fderiv ℝ (fun x => fderiv ℝ φ x w) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change fderiv ℝ (dirD φ v) z w = fderiv ℝ (dirD φ w) z v
  rw [hv, hw]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).eq w v

private theorem hardy_harmonic_of_cauchyRiemann {Ω : Set ℂ} (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * lap φ z) = 0 := by
  have hfactor (ψ : ℂ → ℂ) :
      (∫ z in Ω, (h1Gradient Ω 0 u : ℂ → ℂ) z * ψ z) =
        Complex.I * ∫ z in Ω, (h1Gradient Ω 1 u : ℂ → ℂ) z * ψ z := by
    rw [hCR]
    calc
      _ = ∫ z in Ω, Complex.I * ((h1Gradient Ω 1 u : ℂ → ℂ) z * ψ z) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul Complex.I (h1Gradient Ω 1 u)] with z hz
        rw [hz]
        change Complex.I * ((h1Gradient Ω 1 u : ℂ → ℂ) z) * ψ z = _
        ring
      _ = _ := integral_const_mul _ _
  have hxx := (h1Value_weakGradient Ω u) (dirD φ 1) (hφ.dirD 1) 0
  have hxy := (h1Value_weakGradient Ω u) (dirD φ Complex.I) (hφ.dirD Complex.I) 0
  have hyx := (h1Value_weakGradient Ω u) (dirD φ 1) (hφ.dirD 1) 1
  have hyy := (h1Value_weakGradient Ω u) (dirD φ Complex.I) (hφ.dirD Complex.I) 1
  change (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ 1) 1 z) =
    -∫ z in Ω, (h1Gradient Ω 0 u : ℂ → ℂ) z * dirD φ 1 z at hxx
  change (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) 1 z) =
    -∫ z in Ω, (h1Gradient Ω 0 u : ℂ → ℂ) z * dirD φ Complex.I z at hxy
  change (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ 1) Complex.I z) =
    -∫ z in Ω, (h1Gradient Ω 1 u : ℂ → ℂ) z * dirD φ 1 z at hyx
  change (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) Complex.I z) =
    -∫ z in Ω, (h1Gradient Ω 1 u : ℂ → ℂ) z * dirD φ Complex.I z at hyy
  have hx :
      (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ 1) 1 z) =
        Complex.I * ∫ z in Ω,
          (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ 1) Complex.I z := by
    rw [hxx, hfactor, hyx]
    ring
  have hy :
      (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) 1 z) =
        Complex.I * ∫ z in Ω,
          (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) Complex.I z := by
    rw [hxy, hfactor, hyy]
    ring
  have hc :
      (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ 1) Complex.I z) =
        ∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) 1 z := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      change (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ 1) Complex.I z =
        (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) 1 z
      rw [dirD_comm_of_contDiff hφ.1])
  have hix := (Lp.memLp (h1Value Ω u)).integrable_mul
    (((hφ.dirD 1).dirD 1).memLp' 2 (μ := volume.restrict Ω))
  have hiy := (Lp.memLp (h1Value Ω u)).integrable_mul
    (((hφ.dirD Complex.I).dirD Complex.I).memLp' 2 (μ := volume.restrict Ω))
  calc
    _ = (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ 1) 1 z) +
        ∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) Complex.I z := by
      simp only [lap, mul_add]
      exact integral_add hix hiy
    _ = Complex.I * (Complex.I * ∫ z in Ω,
          (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) Complex.I z) +
        ∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * dirD (dirD φ Complex.I) Complex.I z := by
      rw [hx, hc, hy]
    _ = 0 := by rw [← mul_assoc, Complex.I_mul_I]; ring

/-- A genuine weak Cauchy--Riemann equation implies distributional harmonicity
in every physical domain, directly from the weak-gradient identities. -/
theorem h1_weakHarmonic_of_cauchyRiemann {Ω : Set ℂ} (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, (h1Value Ω u : ℂ → ℂ) z * lap φ z) = 0 :=
  hardy_harmonic_of_cauchyRiemann u hCR hφ

/-- Distributional harmonicity of the actual completed H¹ extension. -/
theorem diskHardyExtension_weakHarmonic (b : L2Z) {φ : ℂ → ℂ}
    (hφ : TestFunction (ball (0 : ℂ) 1) φ) :
    (∫ z in ball (0 : ℂ) 1,
      (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b) : ℂ → ℂ) z * lap φ z) = 0 :=
  hardy_harmonic_of_cauchyRiemann (diskHardyExtension b)
    (diskHardyExtension_cauchyRiemann b) hφ

end PolyaNeumann
