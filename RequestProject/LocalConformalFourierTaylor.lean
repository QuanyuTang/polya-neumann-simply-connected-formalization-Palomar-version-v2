module

public import RequestProject.LocalConformalFourierCollar
public import RequestProject.PhysicalHardySupport
public import RequestProject.CutFourier
public import RequestProject.ArcLength
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Averaged circle coefficients, genuine Taylor data, and a smooth Fourier collar

The coefficients below are the averaged Haar Fourier coefficients of the actual
circle trace.  There is no orthonormal `sqrt (2 * pi)` factor.  Disk holomorphicity
and closure continuity identify them with the Cauchy coefficients; all orders of
real smoothness of the circle trace imply the summability required by the actual
collar construction.  No complex holomorphicity outside the disk is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology ComplexConjugate

local instance fourierTaylorTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The actual averaged, rather than orthonormal, nonnegative circle coefficients. -/
def localConformalFourierTaylorCoefficients (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos (physicalCircleTrace F) (n : ℤ)

theorem periodic_iteratedDeriv_two_pi {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) (2 * Real.pi) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hp
  | succ k ih =>
      simpa only [iteratedDeriv_succ] using deriv_periodic ih

theorem contDiff_infty_iteratedDeriv_real {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv k hf

theorem contDiff_infty_hasDerivAt_iteratedDeriv_real {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (θ : ℝ) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f θ) θ := by
  have hk : ContDiff ℝ 1 (iteratedDeriv k f) :=
    (contDiff_infty_iteratedDeriv_real hf k).of_le
      (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)
  simpa only [iteratedDeriv_succ] using (hk.differentiable_one θ).hasDerivAt

/-- Genuine repeated periodic integration by parts, including frequency zero. -/
theorem periodic_contDiff_infty_fourierCoeffOn_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n =
      (Complex.I * (n : ℂ)) ^ k * fourierCoeffOn Real.two_pi_pos f n := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ k ih =>
      have hend : iteratedDeriv k f 0 = iteratedDeriv k f (2 * Real.pi) := by
        simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp k 0).symm
      rw [fourierCoeffOn_deriv
        (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
        (contDiff_infty_iteratedDeriv_real hf (k + 1)).continuous hend, ih,
        pow_succ']
      ring

theorem periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) (n : ℤ) :
    ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n‖ =
      |(n : ℝ)| ^ k * ‖fourierCoeffOn Real.two_pi_pos f n‖ := by
  rw [periodic_contDiff_infty_fourierCoeffOn_iteratedDeriv hf hp k n,
    norm_mul, norm_pow, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]

/-- Absolute summability is obtained from three actual derivatives, applied
at every derivative order, rather than from a Fourier decay premise. -/
theorem periodic_contDiff_infty_summable_derivative_coefficients {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) :
    Summable (fun n : ℤ =>
      ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f) n‖) := by
  apply summable_norm_fourierCoeffOn_deriv
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf k)
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1))
    (contDiff_infty_hasDerivAt_iteratedDeriv_real hf (k + 1 + 1))
    (contDiff_infty_iteratedDeriv_real hf (k + 1 + 1 + 1)).continuous
  · simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp k 0).symm
  · simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp (k + 1) 0).symm
  · simpa only [zero_add] using (periodic_iteratedDeriv_two_pi hp (k + 1 + 1) 0).symm

/-- Every polynomially weighted positive tail of the genuine averaged
Fourier coefficients is summable.  The zeroth mode is not discarded. -/
theorem periodic_contDiff_infty_hasRapidFourierDecay {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * Real.pi)) :
    HasRapidFourierDecay (fun n : ℕ => fourierCoeffOn Real.two_pi_pos f (n : ℤ)) := by
  intro k
  have hi : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := by
    intro m n h
    exact Nat.add_right_cancel (Int.ofNat_injective h)
  have hs := (periodic_contDiff_infty_summable_derivative_coefficients hf hp k).comp_injective hi
  have hs' : Summable (fun n : ℕ =>
      ‖fourierCoeffOn Real.two_pi_pos f ((n + 1 : ℕ) : ℤ)‖ *
        ((n + 1 : ℕ) : ℝ) ^ (k + 1)) := by
    refine hs.congr fun n => ?_
    change ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f)
      ((n + 1 : ℕ) : ℤ)‖ = _
    rw [periodic_contDiff_infty_norm_fourierCoeffOn_iteratedDeriv hf hp (k + 1)]
    simp only [Int.cast_natCast, abs_of_nonneg
      (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
    ring
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
    (pow_nonneg (Nat.cast_nonneg _) _)) (fun n => ?_) hs'
  have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hnonneg : (0 : ℝ) ≤
      ‖fourierCoeffOn Real.two_pi_pos f ((n + 1 : ℕ) : ℤ)‖ *
        ((n + 1 : ℕ) : ℝ) ^ k :=
    mul_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  simpa only [mul_one, pow_succ, mul_assoc] using
    mul_le_mul_of_nonneg_left hbase hnonneg

theorem localConformalFourierTaylorCoefficients_hasRapidFourierDecay
    (F : ℂ → ℂ) (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F)) :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) :=
  periodic_contDiff_infty_hasRapidFourierDecay hΓ (physicalCircleTrace_periodic F)

private theorem fourierTaylor_fourier_natCast (n : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (n : ℤ) (θ : AddCircle (2 * Real.pi)) =
      (circleMap 0 1 θ) ^ n := by
  rw [fourier_coe_apply, circleMap_zero_pow]
  simp only [one_pow, circleMap_zero, Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem fourierTaylor_fourier_neg_natCast (n : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (-(n : ℤ)) (θ : AddCircle (2 * Real.pi)) =
      (circleMap 0 1 θ)⁻¹ ^ n := by
  rw [fourier_neg, fourierTaylor_fourier_natCast, map_pow,
    ← Complex.inv_eq_conj (z := circleMap 0 1 θ)
      (by simp only [norm_circleMap_zero, abs_one])]

/-- The Cauchy coefficient is exactly the averaged angular coefficient.
This calculation does not require any holomorphicity hypothesis. -/
theorem cauchyPowerSeries_unitDisk_coefficient_eq_fourier
    (F : ℂ → ℂ) (n : ℕ) :
    cauchyPowerSeries F 0 1 n (fun _ => (1 : ℂ)) =
      localConformalFourierTaylorCoefficients F n := by
  have hcircle : circleIntegral (fun z : ℂ => z⁻¹ ^ n * (z⁻¹ * F z)) 0 1 =
      Complex.I * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        fourier (T := 2 * Real.pi) (-(n : ℤ))
          (θ : AddCircle (2 * Real.pi)) * physicalCircleTrace F θ) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    have hz : circleMap 0 1 θ ≠ 0 := by
      intro h
      have hh := norm_circleMap_zero 1 θ
      simp only [h, norm_zero, abs_one] at hh
      exact zero_ne_one hh
    change deriv (circleMap 0 1) θ •
      ((circleMap 0 1 θ)⁻¹ ^ n * ((circleMap 0 1 θ)⁻¹ * F (circleMap 0 1 θ))) =
      Complex.I * (fourier (T := 2 * Real.pi) (-(n : ℤ))
        (θ : AddCircle (2 * Real.pi)) * physicalCircleTrace F θ)
    rw [fourierTaylor_fourier_neg_natCast]
    simp only [deriv_circleMap, smul_eq_mul, physicalCircleTrace]
    field_simp [hz]
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, one_pow, sub_zero, smul_eq_mul]
  rw [hcircle, localConformalFourierTaylorCoefficients, fourierCoeffOn_eq_integral]
  simp only [sub_zero, smul_eq_mul, Complex.real_smul]
  rw [sub_zero]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hπ, Complex.I_ne_zero]

theorem cauchyPowerSeries_unitDisk_apply_eq_fourier
    (F : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    cauchyPowerSeries F 0 1 n (fun _ => z) =
      localConformalFourierTaylorCoefficients F n * z ^ n := by
  have hcoef := cauchyPowerSeries_unitDisk_coefficient_eq_fourier F n
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, one_pow, one_smul] at hcoef ⊢
  rw [hcoef]
  exact mul_comm (z ^ n) (localConformalFourierTaylorCoefficients F n)

/-- Interior Taylor matching follows from the actual Cauchy representation
on the open disk, with the coefficients already identified above. -/
theorem localConformalFourierTaylor_hasSum_on_openDisk
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n : ℕ => localConformalFourierTaylorCoefficients F n * z ^ n) (F z) := by
  have hp := hF.hasFPowerSeriesOnBall (R := (1 : NNReal)) (by norm_num)
  have hz' : z ∈ eball (0 : ℂ) ((1 : NNReal) : ENNReal) := by
    simpa only [Metric.eball_coe, NNReal.coe_one] using hz
  have hs := hp.hasSum_sub hz'
  simpa only [sub_zero, NNReal.coe_one, cauchyPowerSeries_unitDisk_apply_eq_fourier] using hs

/-- Closure matching uses continuity of the genuinely constructed collar
and the original map, so no boundary power-series identity is a premise. -/
theorem localConformalFourierTaylor_eq_on_closedDisk
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    F z = localConformalFourierTaylorCoefficients F 0 +
      ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) := by
  let a := localConformalFourierTaylorCoefficients F
  have ha : HasRapidFourierDecay a :=
    localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ
  have hEq : EqOn (fourierCollarExtension a) F (ball (0 : ℂ) 1) := by
    intro w hw
    have hs := localConformalFourierTaylor_hasSum_on_openDisk F hF hw
    calc
      fourierCollarExtension a w = a 0 + ∑' n : ℕ, a (n + 1) * w ^ (n + 1) :=
        fourierCollarExtension_eq_taylor_on_closedDisk a (ball_subset_closedBall hw)
      _ = ∑' n : ℕ, a n * w ^ n := by
        simpa only [pow_zero, mul_one] using hs.summable.tsum_eq_zero_add.symm
      _ = F w := hs.tsum_eq
  have hEqCl : EqOn (fourierCollarExtension a) F (closedBall (0 : ℂ) 1) :=
    hEq.of_subset_closure (fourierCollarExtension_contDiff ha).continuous.continuousOn
      hF.continuousOn_ball ball_subset_closedBall (by
        simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
          (Subset.rfl : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1))
  exact (hEqCl hz).symm.trans (fourierCollarExtension_eq_taylor_on_closedDisk a hz)

/-- Rapid decay gives genuine absolute convergence at every closed-disk
point, not only a value assigned by `tsum`. -/
theorem fourierTaylor_summable_tail_on_closedDisk {a : ℕ → ℂ}
    (ha : HasRapidFourierDecay a) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    Summable (fun n : ℕ => a (n + 1) * z ^ (n + 1)) := by
  have hs : Summable (fun n : ℕ => ‖a (n + 1)‖) := by
    simpa only [pow_zero, mul_one] using ha 0
  have hzNorm : ‖z‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  apply hs.of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hzNorm)
    (norm_nonneg _)).trans_eq (mul_one _)

theorem localConformalFourierTaylor_hasSum_on_closedDisk
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    HasSum (fun n : ℕ => localConformalFourierTaylorCoefficients F n * z ^ n) (F z) := by
  have hs := fourierTaylor_summable_tail_on_closedDisk
    (localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ) hz
  rw [localConformalFourierTaylor_eq_on_closedDisk F hF hΓ hz]
  simpa only [pow_zero, mul_one] using
    (HasSum.zero_add (f := fun n : ℕ =>
      localConformalFourierTaylorCoefficients F n * z ^ n) hs.hasSum)

/-- Actual smooth circle data now supplies both genuine rapid decay and
the closed-disk Taylor identity needed by the Fourier collar construction. -/
theorem localConformalFourierTaylor_data
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F)) :
    HasRapidFourierDecay (localConformalFourierTaylorCoefficients F) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1,
        F z = localConformalFourierTaylorCoefficients F 0 +
          ∑' n : ℕ, localConformalFourierTaylorCoefficients F (n + 1) * z ^ (n + 1) :=
  ⟨localConformalFourierTaylorCoefficients_hasRapidFourierDecay F hΓ,
    fun _ hz => localConformalFourierTaylor_eq_on_closedDisk F hF hΓ hz⟩

/-- A real-smooth global extension from the actual smooth circle trace.
It agrees on the whole closed disk and remains complex holomorphic inside. -/
theorem exists_smooth_holomorphic_fourier_collar_of_circleTrace
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      EqOn G F (closedBall (0 : ℂ) 1) ∧ DifferentiableOn ℂ G (ball (0 : ℂ) 1) := by
  obtain ⟨ha, hTaylor⟩ := localConformalFourierTaylor_data F hF hΓ
  exact exists_smooth_holomorphic_fourier_collar_of_taylor ha hF.differentiableOn hTaylor

end PolyaNeumann
