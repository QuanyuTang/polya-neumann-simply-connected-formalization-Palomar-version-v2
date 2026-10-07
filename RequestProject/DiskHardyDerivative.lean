module

public import RequestProject.DiskHardyExtension

/-!
# The actual weak derivative of a smoothed disk Hardy extension

One extra order of boundary smoothing turns the weak derivative of the
antiholomorphic H¹ extension into the value of another genuine H¹ extension.
The derivative data are constructed as a bounded weighted Fourier shift.
The proof differentiates the convergent physical H¹ series, removes its
constant term, and reindexes the remaining actual monomial derivatives.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace Topology

/-- The normalized derivative weight at output frequency `-k`. -/
def diskHardyDerivativeWeight (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) *
    Real.sqrt (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))

theorem diskHardyDerivativeWeight_nonneg (k : ℕ) :
    0 ≤ diskHardyDerivativeWeight k := by
  unfold diskHardyDerivativeWeight
  positivity

theorem diskHardyDerivativeWeight_le_one (k : ℕ) :
    diskHardyDerivativeWeight k ≤ 1 := by
  have hr0 : 0 ≤ (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) := by positivity
  have hr1 : (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.le_add_right (k + 1) 1
  have hs : Real.sqrt (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hr1
  unfold diskHardyDerivativeWeight
  calc
    _ ≤ 1 * 1 := mul_le_mul hr1 hs (Real.sqrt_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- Positive output modes are zero. The nonpositive output `n` takes its
input from `n-1`, so output zero comes from input frequency `-1`. -/
def diskHardyDerivativeSymbol (n : ℤ) : ℂ :=
  if 0 < n then 0 else (diskHardyDerivativeWeight (Int.toNat (-n)) : ℂ)

theorem norm_diskHardyDerivativeSymbol_le_one (n : ℤ) :
    ‖diskHardyDerivativeSymbol n‖ ≤ 1 := by
  unfold diskHardyDerivativeSymbol
  split_ifs
  · norm_num
  · rw [Complex.norm_of_nonneg (diskHardyDerivativeWeight_nonneg _)]
    exact diskHardyDerivativeWeight_le_one _

private theorem derivative_shift_injective :
    Function.Injective (fun n : ℤ => n - 1) := by
  intro m n h
  change m - 1 = n - 1 at h
  omega

theorem derivative_shift_memℓp (b : L2Z) :
    Memℓp (fun n : ℤ => b (n - 1)) 2 := by
  exact memℓp_two_iff_summable.mpr
    ((summable_norm_sq_L2Z b).comp_injective derivative_shift_injective)

def derivativeShiftLin : L2Z →ₗ[ℂ] L2Z where
  toFun b := ⟨fun n => b (n - 1), derivative_shift_memℓp b⟩
  map_add' b c := by ext n; simp [Pi.add_apply]; rfl
  map_smul' a b := by ext n; simp

private theorem derivative_shift_norm_le (b : L2Z) :
    ‖derivativeShiftLin b‖ ≤ ‖b‖ := by
  have hs : ‖derivativeShiftLin b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [norm_sq_L2Z, norm_sq_L2Z]
    exact tsum_comp_le_tsum_of_inj (summable_norm_sq_L2Z b)
      (fun n => sq_nonneg ‖b n‖) derivative_shift_injective
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def derivativeShift : L2Z →L[ℂ] L2Z :=
  derivativeShiftLin.mkContinuous 1 (fun b => by simpa using derivative_shift_norm_le b)

/-- The genuine bounded derivative-data operator. -/
def diskHardyDerivativeData : L2Z →L[ℂ] L2Z :=
  (diagOp diskHardyDerivativeSymbol 1 norm_diskHardyDerivativeSymbol_le_one).comp
    derivativeShift

theorem diskHardyDerivativeData_apply (b : L2Z) (n : ℤ) :
    diskHardyDerivativeData b n = diskHardyDerivativeSymbol n * b (n - 1) := rfl

theorem diskHardyDerivativeData_apply_pos (b : L2Z) {n : ℤ} (hn : 0 < n) :
    diskHardyDerivativeData b n = 0 := by
  simp only [diskHardyDerivativeData_apply, diskHardyDerivativeSymbol, hn,
    ite_true, zero_mul]

theorem diskHardyDerivativeData_apply_neg (b : L2Z) (k : ℕ) :
    diskHardyDerivativeData b (-(k : ℤ)) =
      (diskHardyDerivativeWeight k : ℂ) * b (-((k + 1 : ℕ) : ℤ)) := by
  have hn : ¬ (0 : ℤ) < -(k : ℤ) := by omega
  have hi : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
  simp only [diskHardyDerivativeData_apply, diskHardyDerivativeSymbol, hn,
    ite_false, neg_neg, Int.toNat_natCast, hi]

theorem diskHardyDerivativeData_apply_neg_formula (b : L2Z) (k : ℕ) :
    diskHardyDerivativeData b (-(k : ℤ)) =
      ((((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
        Real.sqrt (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) : ℝ) : ℂ) *
          b (-((k + 1 : ℕ) : ℤ)) := by
  simpa only [diskHardyDerivativeWeight] using diskHardyDerivativeData_apply_neg b k

theorem norm_diskHardyDerivativeData_apply_le (b : L2Z) :
    ‖diskHardyDerivativeData b‖ ≤ ‖b‖ := by
  change ‖diagOp diskHardyDerivativeSymbol 1
    norm_diskHardyDerivativeSymbol_le_one (derivativeShift b)‖ ≤ _
  have hd : ‖diagOp diskHardyDerivativeSymbol 1
      norm_diskHardyDerivativeSymbol_le_one (derivativeShift b)‖ ≤ ‖derivativeShift b‖ := by
    have h := norm_diagLin_le diskHardyDerivativeSymbol 1
      norm_diskHardyDerivativeSymbol_le_one (derivativeShift b)
    simp only [one_mul] at h
    exact h
  exact hd.trans (derivative_shift_norm_le b)

theorem norm_diskHardyDerivativeData_le_one : ‖diskHardyDerivativeData‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro b
  simpa using norm_diskHardyDerivativeData_apply_le b

private theorem derivative_sobWeight_neg_nat (m : ℕ) :
    sobWeight (-(m : ℤ)) = ((m + 1 : ℕ) : ℝ) := by
  simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m), Nat.cast_add, Nat.cast_one]
  ring

private theorem derivative_smoothing_one_apply (b : L2Z) (n : ℤ) :
    sobolevSmoothing 1 (by norm_num) b n = (sobWeight n : ℂ)⁻¹ * b n := by
  simp only [sobolevSmoothing, diagOp_apply, Real.rpow_neg_one, Complex.ofReal_inv]

private theorem derivative_sqrt_ratio_scale {a c : ℝ} (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (a / b * Real.sqrt (a / b)) / (Real.sqrt a * c) =
      (a / b) / (Real.sqrt b * c) := by
  rw [Real.sqrt_div ha.le]
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp [hsa, hsb, hb.ne', hc.ne']

private theorem derivative_weight_over_traceScale (k : ℕ) :
    diskHardyDerivativeWeight k / diskHardyTraceScale k =
      (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) /
        diskHardyTraceScale (k + 1) := by
  simpa only [diskHardyDerivativeWeight, diskHardyTraceScale,
    derivative_sobWeight_neg_nat, Nat.add_assoc, Nat.reduceAdd] using
      derivative_sqrt_ratio_scale (by positivity : 0 < ((k + 1 : ℕ) : ℝ))
        ((k + 2 : ℕ) : ℝ) (by positivity) (Real.sqrt_pos.mpr (by positivity : 0 < 2 * π))

private theorem derivative_series_scalar (b : L2Z) (k : ℕ) :
    (sobolevSmoothing 1 (by norm_num) b (-((k + 1 : ℕ) : ℤ)) /
      (diskHardyTraceScale (k + 1) : ℂ)) * ((k + 1 : ℕ) : ℂ) =
        diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k : ℂ) := by
  have hc : (diskHardyDerivativeWeight k : ℂ) / (diskHardyTraceScale k : ℂ) =
      (((k + 1 : ℕ) : ℂ) / ((k + 2 : ℕ) : ℂ)) /
        (diskHardyTraceScale (k + 1) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
      congrArg (fun r : ℝ => (r : ℂ)) (derivative_weight_over_traceScale k)
  rw [derivative_smoothing_one_apply, derivative_sobWeight_neg_nat,
    diskHardyDerivativeData_apply_neg]
  simp only [Nat.add_assoc, Nat.reduceAdd, Complex.ofReal_natCast]
  calc
    _ = ((((k + 1 : ℕ) : ℂ) / ((k + 2 : ℕ) : ℂ)) /
        (diskHardyTraceScale (k + 1) : ℂ)) * b (-((k + 1 : ℕ) : ℤ)) := by
      simp only [div_eq_mul_inv]
      ring
    _ = ((diskHardyDerivativeWeight k : ℂ) / (diskHardyTraceScale k : ℂ)) *
        b (-((k + 1 : ℕ) : ℤ)) := by rw [hc]
    _ = _ := by simp only [div_eq_mul_inv]; ring

private theorem derivative_mode_value (m : ℕ) :
    h1Value (ball (0 : ℂ) 1) (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicArea m :=
  h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

private theorem derivative_mode_gradient_component (m : ℕ) (i : Fin 2) :
    h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicGradient m i := by
  have h := congrArg (fun G : DiskGradientSpace => G i)
    (diskH1Gradient_antiholomorphicTest m)
  simpa only [diskH1Gradient, PiLp.toLp_apply] using h

/-- Actual weak `x` derivative of the constant disk mode. -/
theorem diskAntiholomorphicH1Test_gradient_zero :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test 0) = 0 := by
  rw [derivative_mode_gradient_component]
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae 0 0,
    Lp.coeFn_zero ℂ 2 (volume.restrict (ball (0 : ℂ) 1))] with z hz hzero
  rw [hz, hzero]
  simp only [dirD_diskAntiholomorphicMode, Nat.cast_zero, zero_mul,
    Pi.zero_apply]

/-- Actual weak `x` derivative of a nonconstant disk mode. -/
theorem diskAntiholomorphicH1Test_gradient_succ (k : ℕ) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test (k + 1)) =
      ((k + 1 : ℕ) : ℂ) • diskAntiholomorphicArea k := by
  rw [derivative_mode_gradient_component]
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae (k + 1) 0,
    diskAntiholomorphicArea_ae k,
    Lp.coeFn_smul ((k + 1 : ℕ) : ℂ) (diskAntiholomorphicArea k)] with z hg ha hsmul
  rw [hg, hsmul]
  change dirD (diskAntiholomorphicMode (k + 1)) (coordDir 0) z =
    ((k + 1 : ℕ) : ℂ) * ((diskAntiholomorphicArea k : ℂ → ℂ) z)
  rw [ha]
  simp only [dirD_diskAntiholomorphicMode,
    show coordDir 0 = (1 : ℂ) from rfl,
    Nat.add_sub_cancel, map_one, mul_one]

private theorem derivative_hasSum_tail
    {H : Type*} [NormedAddCommGroup H] (f : ℕ → H) (x : H)
    (hzero : f 0 = 0) (hs : HasSum f x) : HasSum (fun k => f (k + 1)) x := by
  apply (hasSum_nat_add_iff 1).mpr
  simpa only [Finset.sum_range_one, hzero, add_zero] using hs

/-- The smoothed Hardy extension has a weak derivative which is itself
the value of an actual H¹ Hardy extension. -/
theorem diskHardyExtension_smoothing_gradient (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b)) =
      h1Value (ball (0 : ℂ) 1) (diskHardyExtension (diskHardyDerivativeData b)) := by
  let f : ℕ → L2 (ball (0 : ℂ) 1) := fun m =>
    (sobolevSmoothing 1 (by norm_num) b (-(m : ℤ)) /
      (diskHardyTraceScale m : ℂ)) •
        h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test m)
  have hs : HasSum f
      (h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b))) := by
    simpa only [map_smul] using
      (h1Gradient (ball (0 : ℂ) 1) 0).hasSum
        (diskHardyExtension_hasSum (sobolevSmoothing 1 (by norm_num) b))
  have hz : f 0 = 0 := by
    simp only [f, diskAntiholomorphicH1Test_gradient_zero, smul_zero]
  have ht := derivative_hasSum_tail f _ hz hs
  have hv := (h1Value (ball (0 : ℂ) 1)).hasSum
    (diskHardyExtension_hasSum (diskHardyDerivativeData b))
  have ht' : HasSum (fun k : ℕ =>
      (diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k : ℂ)) •
        diskAntiholomorphicArea k)
      (h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b))) := by
    convert ht using 1
    funext k
    simp only [f, diskAntiholomorphicH1Test_gradient_succ, smul_smul,
      derivative_series_scalar]
  have hv' : HasSum (fun k : ℕ =>
      (diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k : ℂ)) •
        diskAntiholomorphicArea k)
      (h1Value (ball (0 : ℂ) 1) (diskHardyExtension (diskHardyDerivativeData b))) := by
    simpa only [map_smul, derivative_mode_value] using hv
  exact ht'.unique hv'

theorem diskHardyExtension_smoothing_gradient_y (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 1
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b)) =
      (-Complex.I) • h1Value (ball (0 : ℂ) 1)
        (diskHardyExtension (diskHardyDerivativeData b)) := by
  have h := congrArg (fun v : L2 (ball (0 : ℂ) 1) => (-Complex.I) • v)
    (diskHardyExtension_cauchyRiemann (sobolevSmoothing 1 (by norm_num) b))
  simp only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at h
  rw [diskHardyExtension_smoothing_gradient] at h
  exact h.symm

theorem diskHardyExtension_smoothing_gradient_operator :
    (h1Gradient (ball (0 : ℂ) 1) 0).comp
        (diskHardyExtension.comp (sobolevSmoothing 1 (by norm_num))) =
      (h1Value (ball (0 : ℂ) 1)).comp
        (diskHardyExtension.comp diskHardyDerivativeData) := by
  apply ContinuousLinearMap.ext
  intro b
  exact diskHardyExtension_smoothing_gradient b

end PolyaNeumann
