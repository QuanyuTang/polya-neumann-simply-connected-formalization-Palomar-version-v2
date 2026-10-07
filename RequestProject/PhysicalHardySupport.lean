module

public import RequestProject.HardyAntiderivative
public import RequestProject.Driven
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

/-!
# Hardy support of an actual disk boundary trace

For a given map holomorphic in the open unit disk and continuous on its closure,
Cauchy--Goursat proves that its actual circle trace has no negative Fourier
coefficients.  With real C¹ regularity of that trace, integration by parts proves
the derivative coefficient identity and its zero mean.  Conjugation therefore
gives strictly negative support for the actual conjugated boundary derivative.

All Fourier coefficients use the averaged convention on `[0,2π]`.  Real smoothness
near the closed disk is sufficient for the C¹ corollary; holomorphicity outside the
open disk is never required.  This file does not construct the initial conformal
map, an arc-length reparametrization, or an `IsBoundaryParam` instance for the circle
trace.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate

local instance physicalHardyTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The actual given map restricted to the unit circle in its usual angular parameter. -/
def physicalCircleTrace (F : ℂ → ℂ) (θ : ℝ) : ℂ := F (circleMap 0 1 θ)

theorem physicalCircleTrace_periodic (F : ℂ → ℂ) :
    Function.Periodic (physicalCircleTrace F) (2 * Real.pi) := by
  intro θ
  exact congrArg F ((periodic_circleMap 0 1) θ)

private theorem physicalHardy_fourier_natCast (m : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (m : ℤ) (θ : AddCircle (2 * Real.pi)) =
      (circleMap 0 1 θ) ^ m := by
  rw [fourier_coe_apply, circleMap_zero_pow]
  simp only [one_pow, circleMap_zero, Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- A Cauchy--Goursat integral is the ordinary angular integral selecting a
negative Fourier coefficient, with its genuine circle differential. -/
theorem physicalCircleTrace_negative_moment_eq_zero
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1)) (m : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      fourier (T := 2 * Real.pi) ((m + 1 : ℕ) : ℤ)
        (θ : AddCircle (2 * Real.pi)) * physicalCircleTrace F θ) = 0 := by
  have hpoly : DiffContOnCl ℂ (fun z => F z * z ^ m) (ball (0 : ℂ) 1) :=
    ⟨hF.differentiableOn.mul (differentiableOn_id.pow m),
      hF.continuousOn.mul (continuousOn_id.pow m)⟩
  have hzero : circleIntegral (fun z => F z * z ^ m) 0 1 = 0 :=
    DiffContOnCl.circleIntegral_eq_zero (by norm_num) hpoly
  have heq : circleIntegral (fun z => F z * z ^ m) 0 1 =
      Complex.I * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        fourier (T := 2 * Real.pi) ((m + 1 : ℕ) : ℤ)
          (θ : AddCircle (2 * Real.pi)) * physicalCircleTrace F θ) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, smul_eq_mul, physicalCircleTrace]
    rw [physicalHardy_fourier_natCast, pow_succ]
    ring
  rw [heq] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left Complex.I_ne_zero

/-- Every strictly negative averaged Fourier coefficient of the actual circle
trace vanishes, derived solely from disk holomorphicity and closure continuity. -/
theorem physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    {n : ℤ} (hn : n < 0) :
    fourierCoeffOn Real.two_pi_pos (physicalCircleTrace F) n = 0 := by
  cases n with
  | ofNat m =>
      exact (not_lt_of_ge (show (0 : ℤ) ≤ Int.ofNat m from
        Int.natCast_nonneg m) hn).elim
  | negSucc m =>
      have hi : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by
        simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one]
      have hmoment := physicalCircleTrace_negative_moment_eq_zero F hF m
      simp only [fourier_coe_apply] at hmoment
      rw [hi, fourierCoeffOn_eq_integral]
      simp only [fourier_coe_apply, sub_zero, neg_neg, smul_eq_mul]
      rw [hmoment, smul_zero]

private theorem physicalHardy_fourierCoeffOn_derivative
    {γ b : ℝ → ℂ} (hd : ∀ θ, HasDerivAt γ (b θ) θ) (hb : Continuous b)
    (hper : γ 0 = γ (2 * Real.pi)) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos b n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos γ n := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, Int.cast_zero, mul_zero, zero_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
      (hb.intervalIntegrable _ _), ← hper, sub_self, smul_zero]
  · rw [fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn (fun θ _ => hd θ)
      (hb.intervalIntegrable _ _), ← hper, sub_self, mul_zero, zero_sub]
    have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp [hnC, hpi]
    ring

/-- Integration by parts for the actual derivative of a C¹ circle trace. -/
theorem physicalCircleTrace_deriv_fourierCoeffOn
    (F : ℂ → ℂ) (hγ : ContDiff ℝ 1 (physicalCircleTrace F)) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (deriv (physicalCircleTrace F)) n =
      (Complex.I * (n : ℂ)) *
        fourierCoeffOn Real.two_pi_pos (physicalCircleTrace F) n := by
  apply physicalHardy_fourierCoeffOn_derivative
    (fun θ => (hγ.differentiable_one θ).hasDerivAt) hγ.continuous_deriv_one
  simpa only [zero_add] using ((physicalCircleTrace_periodic F) 0).symm

/-- The actual periodic boundary derivative has zero averaged coefficient. -/
@[simp] theorem physicalCircleTrace_deriv_fourierCoeffOn_zero
    (F : ℂ → ℂ) (hγ : ContDiff ℝ 1 (physicalCircleTrace F)) :
    fourierCoeffOn Real.two_pi_pos (deriv (physicalCircleTrace F)) 0 = 0 := by
  rw [physicalCircleTrace_deriv_fourierCoeffOn F hγ]
  simp only [Int.cast_zero, mul_zero, zero_mul]

private theorem physicalHardy_fourierCoeffOn_conj (g : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ => conj (g θ)) n =
      conj (fourierCoeffOn Real.two_pi_pos g (-n)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [smul_eq_mul, map_mul, neg_neg]
  congr 1
  exact fourier_neg

/-- The actual conjugated boundary derivative has strictly negative Fourier support. -/
theorem physicalCircleTrace_conj_deriv_strictNegative
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    (hγ : ContDiff ℝ 1 (physicalCircleTrace F)) :
    IsStrictNegativeFourierSupport
      (fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv (physicalCircleTrace F) θ))) := by
  intro n hn
  rw [physicalHardy_fourierCoeffOn_conj, physicalCircleTrace_deriv_fourierCoeffOn F hγ]
  by_cases hn0 : n = 0
  · subst n
    simp only [neg_zero, Int.cast_zero, mul_zero, zero_mul, map_zero]
  · have hneg : -n < 0 := by omega
    rw [physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg F hF hneg, mul_zero, map_zero]

/-- Real C¹ regularity on a neighborhood of the closed disk gives C¹ regularity
of the actual angular circle trace.  This assertion uses no exterior holomorphicity. -/
theorem contDiff_physicalCircleTrace_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 1 F (ball (0 : ℂ) R)) :
    ContDiff ℝ 1 (physicalCircleTrace F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hz : circleMap 0 1 θ ∈ ball (0 : ℂ) R :=
    closedBall_subset_ball hR (circleMap_mem_closedBall 0 (by norm_num) θ)
  exact (hFs.contDiffAt (isOpen_ball.mem_nhds hz)).comp θ
    (contDiff_circleMap 0 1).contDiffAt

/-- Strict negative support follows from the standard supplied coordinate data:
real C¹ smoothness near the closure and holomorphicity only in the open disk. -/
theorem physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 1 F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    IsStrictNegativeFourierSupport
      (fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv (physicalCircleTrace F) θ))) := by
  apply physicalCircleTrace_conj_deriv_strictNegative F
    (DiffContOnCl.mk_ball hhol (hFs.continuousOn.mono (closedBall_subset_ball hR)))
    (contDiff_physicalCircleTrace_of_neighborhood hR F hFs)

end PolyaNeumann

end
