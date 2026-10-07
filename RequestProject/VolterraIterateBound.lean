module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-!
# Factorial estimates for iterated boundary primitives

The iterates in this file are actual complex interval integrals, starting from an
arbitrary continuous function.  Bounds on the coefficient and the initial function
are required only on the interval in the estimate.

This supplies the factorial estimate for a Volterra primitive.  Identifying the
Fourier-defined boundary `antiPrim` with this interval primitive (including the
choice of integration constant and any zero-mode correction) is a separate bridge;
no such identification is assumed or proved here.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace PolyaNeumann

/-- Iteration of the genuine primitive `f ↦ (t ↦ ∫ s in 0..t, a s * f s)`. -/
def volterraPrimitiveIterate (a h : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => h
  | n + 1 => fun t => ∫ s in (0 : ℝ)..t, a s * volterraPrimitiveIterate a h n s

variable {a h : ℝ → ℂ}

/-- Continuity of every genuine primitive iterate. -/
theorem continuous_volterraPrimitiveIterate (ha : Continuous a) (hh : Continuous h) :
    ∀ n, Continuous (volterraPrimitiveIterate a h n)
  | 0 => hh
  | n + 1 => intervalIntegral.continuous_primitive
      (fun x y =>
        (ha.mul (continuous_volterraPrimitiveIterate ha hh n)).intervalIntegrable x y) 0

/-- The continuous integrand defining the next iterate is interval integrable. -/
theorem intervalIntegrable_volterraPrimitiveIntegrand
    (ha : Continuous a) (hh : Continuous h) (n : ℕ) (x y : ℝ) :
    IntervalIntegrable (fun s => a s * volterraPrimitiveIterate a h n s) volume x y :=
  (ha.mul (continuous_volterraPrimitiveIterate ha hh n)).intervalIntegrable x y

/-- A compact form of the factorial estimate, retaining `(M * t) ^ n`. -/
theorem volterraPrimitiveIterate_bound_mul
    (ha : Continuous a) (hh : Continuous h)
    {T M H : ℝ} (_hT : 0 ≤ T) (hM0 : 0 ≤ M) (_hH0 : 0 ≤ H)
    (hM : ∀ t ∈ Set.Icc 0 T, ‖a t‖ ≤ M)
    (hH : ∀ t ∈ Set.Icc 0 T, ‖h t‖ ≤ H) :
    ∀ n t, t ∈ Set.Icc 0 T →
      ‖volterraPrimitiveIterate a h n t‖ ≤ H * (M * t) ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      simpa [volterraPrimitiveIterate] using hH t ht
  | succ n ih =>
      intro t ht
      simp only [volterraPrimitiveIterate]
      refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      have hint1 :
          IntervalIntegrable (fun s => ‖a s * volterraPrimitiveIterate a h n s‖)
            volume 0 t :=
        (intervalIntegrable_volterraPrimitiveIntegrand ha hh n 0 t).norm
      have hint2 : IntervalIntegrable
          (fun s => M * (H * (M * s) ^ n / (n.factorial : ℝ))) volume 0 t := by
        apply Continuous.intervalIntegrable
        fun_prop
      refine (intervalIntegral.integral_mono_on ht.1 hint1 hint2
        fun s hs => ?_).trans_eq ?_
      · have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
        exact (norm_mul_le _ _).trans
          (mul_le_mul (hM s hsT) (ih s hsT) (norm_nonneg _) hM0)
      · have heq :
            (fun s : ℝ => M * (H * (M * s) ^ n / (n.factorial : ℝ))) =
              fun s => (M * H * M ^ n / (n.factorial : ℝ)) * s ^ n := by
          funext s
          rw [mul_pow]
          ring
        rw [heq, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
        push_cast
        field_simp
        ring

/-- The factorial estimate in separated powers of `M` and `t`. -/
theorem volterraPrimitiveIterate_bound
    (ha : Continuous a) (hh : Continuous h)
    {T M H : ℝ} (hT : 0 ≤ T) (hM0 : 0 ≤ M) (hH0 : 0 ≤ H)
    (hM : ∀ t ∈ Set.Icc 0 T, ‖a t‖ ≤ M)
    (hH : ∀ t ∈ Set.Icc 0 T, ‖h t‖ ≤ H)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖volterraPrimitiveIterate a h n t‖ ≤ H * M ^ n * t ^ n / (n.factorial : ℝ) := by
  simpa only [mul_pow, mul_assoc] using
    volterraPrimitiveIterate_bound_mul ha hh hT hM0 hH0 hM hH n t ht

/-- A bound independent of the evaluation point in `[0,T]`. -/
theorem volterraPrimitiveIterate_bound_uniform
    (ha : Continuous a) (hh : Continuous h)
    {T M H : ℝ} (hT : 0 ≤ T) (hM0 : 0 ≤ M) (hH0 : 0 ≤ H)
    (hM : ∀ t ∈ Set.Icc 0 T, ‖a t‖ ≤ M)
    (hH : ∀ t ∈ Set.Icc 0 T, ‖h t‖ ≤ H)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖volterraPrimitiveIterate a h n t‖ ≤ H * (M * T) ^ n / (n.factorial : ℝ) := by
  refine (volterraPrimitiveIterate_bound_mul ha hh hT hM0 hH0 hM hH n t ht).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hM0 ht.1)
        (mul_le_mul_of_nonneg_left ht.2 hM0) n) hH0)
    (Nat.cast_nonneg n.factorial)

/-- The scalar factorial majorant is summable for every real multiplier. -/
theorem summable_volterraPrimitive_majorant (H c : ℝ) :
    Summable (fun n : ℕ => H * c ^ n / (n.factorial : ℝ)) := by
  simpa only [mul_div_assoc] using (Real.summable_pow_div_factorial c).mul_left H

/-- The actual primitive iterates form a summable series at every point in `[0,T]`. -/
theorem summable_volterraPrimitiveIterate
    (ha : Continuous a) (hh : Continuous h)
    {T M H : ℝ} (hT : 0 ≤ T) (hM0 : 0 ≤ M) (hH0 : 0 ≤ H)
    (hM : ∀ t ∈ Set.Icc 0 T, ‖a t‖ ≤ M)
    (hH : ∀ t ∈ Set.Icc 0 T, ‖h t‖ ≤ H)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    Summable (fun n => volterraPrimitiveIterate a h n t) :=
  Summable.of_norm_bounded (summable_volterraPrimitive_majorant H (M * T))
    (fun n => volterraPrimitiveIterate_bound_uniform ha hh hT hM0 hH0 hM hH n t ht)

/-- Arbitrary complex exponential weights preserve summability of the primitive series. -/
theorem summable_weighted_volterraPrimitiveIterate
    (ha : Continuous a) (hh : Continuous h)
    {T M H : ℝ} (hT : 0 ≤ T) (hM0 : 0 ≤ M) (hH0 : 0 ≤ H)
    (hM : ∀ t ∈ Set.Icc 0 T, ‖a t‖ ≤ M)
    (hH : ∀ t ∈ Set.Icc 0 T, ‖h t‖ ≤ H)
    (c : ℂ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    Summable (fun n => c ^ n * volterraPrimitiveIterate a h n t) := by
  refine Summable.of_norm_bounded
    (summable_volterraPrimitive_majorant H (‖c‖ * (M * T))) ?_
  intro n
  calc
    ‖c ^ n * volterraPrimitiveIterate a h n t‖ =
        ‖c‖ ^ n * ‖volterraPrimitiveIterate a h n t‖ := by rw [norm_mul, norm_pow]
    _ ≤ ‖c‖ ^ n * (H * (M * T) ^ n / (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (volterraPrimitiveIterate_bound_uniform ha hh hT hM0 hH0 hM hH n t ht)
        (pow_nonneg (norm_nonneg c) n)
    _ = H * (‖c‖ * (M * T)) ^ n / (n.factorial : ℝ) := by
      rw [mul_pow]
      ring

/-- The next iterate has the genuine derivative prescribed by its continuous integrand. -/
theorem hasDerivAt_volterraPrimitiveIterate_succ
    (ha : Continuous a) (hh : Continuous h) (n : ℕ) (t : ℝ) :
    HasDerivAt (volterraPrimitiveIterate a h (n + 1))
      (a t * volterraPrimitiveIterate a h n t) t := by
  have hc := ha.mul (continuous_volterraPrimitiveIterate ha hh n)
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_volterraPrimitiveIntegrand ha hh n 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

end PolyaNeumann

end
