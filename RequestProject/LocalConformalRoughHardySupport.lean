module

public import RequestProject.PhysicalMomentHardyCriterion
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.BoundaryFourierMultiplier
public import RequestProject.LocalConformalArcReparam
public import RequestProject.ObservationDual

/-!
# Actual Hardy support from L² physical moments

The density is only an actual L² function on the angular interval. Its first
weighted primitive is genuinely absolutely continuous, has an L² derivative,
and has zero endpoints by the zeroth physical moment. Integration by parts
transfers every physical moment to its continuous periodic representative.
The existing continuous physical moment criterion applies to that first
primitive, using its own second primitive. No continuity of the original
density, or point evaluation of an H^{1/2} function, is required.

The derivative of the first primitive has strictly negative Fourier support,
including a genuinely zero average. The original density is recovered by
multiplication by i z conjugate(1/F'). The actual boundary Fourier multiplier
identity and its convergent convolution give nonpositive support, retaining
the original density's full zero mode. Variable speed of the conformal circle
is preserved throughout.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate

local instance roughHardyTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem rough_c1_absolutelyContinuous {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    AbsolutelyContinuousOnInterval f 0 (2 * Real.pi) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le Real.two_pi_pos.le] using hK

private theorem rough_continuousOn_memLp_two {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 (2 * Real.pi))) :
    MemLp f 2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    C ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
    hC x (Ioc_subset_Icc_self hx)

private theorem rough_memLp_continuous_mul {a H : ℝ → ℂ}
    (ha : Continuous a) (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    MemLp (fun θ => a θ * H θ) 2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (ha.continuousOn : ContinuousOn a (Icc 0 (2 * Real.pi)))
  apply hH.of_le_mul (c := C) (ha.aestronglyMeasurable.restrict.mul hH.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change ‖a θ * H θ‖ ≤ C * ‖H θ‖
  simpa only [Pi.mul_apply, norm_mul] using
    (mul_le_mul_of_nonneg_right (hC θ ⟨hθ.1.le, hθ.2⟩) (norm_nonneg _))

/-- The true weighted derivative density is in L². -/
theorem physicalMomentDensity_memLp (γ H : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    MemLp (fun θ => conj (deriv γ θ) * H θ) 2
      (volume.restrict (Ioc 0 (2 * Real.pi))) :=
  rough_memLp_continuous_mul
    (Complex.continuous_conj.comp hγ.continuous_deriv_one) hH

private theorem rough_memLp_intervalIntegrable {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    IntervalIntegrable f volume 0 (2 * Real.pi) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
    (hf.integrable (by norm_num : (1 : ENNReal) ≤ 2))

/-- The first physical primitive is actual AC, rather than an assumed trace. -/
theorem physicalMomentPrimitive_absolutelyContinuous (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    AbsolutelyContinuousOnInterval (physicalMomentPrimitive γ H) 0 (2 * Real.pi) := by
  exact absolutelyContinuousOnInterval_intervalIntegral_banach
    (rough_memLp_intervalIntegrable (physicalMomentDensity_memLp γ H hγ hH))
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)

/-- The genuine almost-everywhere first derivative, without a continuous load. -/
theorem physicalMomentPrimitive_ae_hasDerivAt (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalMomentPrimitive γ H) (conj (deriv γ θ) * H θ) θ :=
  ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (rough_memLp_intervalIntegrable (physicalMomentDensity_memLp γ H hγ hH))

/-- Equal endpoints imply genuine Fourier H¹ regularity of the first primitive. -/
theorem physicalMomentPrimitive_isSobolevSeq_one (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (physicalMomentPrimitive γ H)) := by
  apply isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalMomentPrimitive_absolutelyContinuous γ H hγ hH)
    (physicalMomentDensity_memLp γ H hγ hH)
    (physicalMomentPrimitive_ae_hasDerivAt γ H hγ hH)
  rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0]

/-- Periodization of the actual continuous first primitive, with no density
value at the chosen boundary origin. -/
def physicalMomentPeriodicPrimitive (γ H : ℝ → ℂ) (θ : ℝ) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) 0 (physicalMomentPrimitive γ H)
    (θ : AddCircle (2 * Real.pi))

theorem physicalMomentPeriodicPrimitive_periodic (γ H : ℝ → ℂ) :
    Function.Periodic (physicalMomentPeriodicPrimitive γ H) (2 * Real.pi) := by
  intro θ
  unfold physicalMomentPeriodicPrimitive
  rw [AddCircle.coe_add_period]

theorem physicalMomentPeriodicPrimitive_eqOn (γ H : ℝ → ℂ)
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    EqOn (physicalMomentPeriodicPrimitive γ H) (physicalMomentPrimitive γ H)
      (Icc 0 (2 * Real.pi)) := by
  intro θ hθ
  by_cases hθL : θ = 2 * Real.pi
  · subst θ
    have hlift : AddCircle.liftIco (2 * Real.pi) 0 (physicalMomentPrimitive γ H)
        (0 : AddCircle (2 * Real.pi)) = physicalMomentPrimitive γ H 0 :=
      AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
    unfold physicalMomentPeriodicPrimitive
    rw [AddCircle.coe_period, hlift, physicalMomentPrimitive_zero,
      physicalMomentPrimitive_endpoint γ H hmom0]
  · exact AddCircle.liftIco_zero_coe_apply ⟨hθ.1, lt_of_le_of_ne hθ.2 hθL⟩

theorem physicalMomentPeriodicPrimitive_continuous (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    Continuous (physicalMomentPeriodicPrimitive γ H) := by
  have hc : ContinuousOn (physicalMomentPrimitive γ H) (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using
      (physicalMomentPrimitive_absolutelyContinuous γ H hγ hH).continuousOn
  exact (AddCircle.liftIco_zero_continuous
    (by rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0])
    hc).comp (AddCircle.continuous_mk' _)

/-- AC integration by parts transfers the original (m+1)-st moment to the
m-th moment of the first primitive. The original density remains only L². -/
theorem physicalMomentPrimitive_moments_of_memLp (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0) (m : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * physicalMomentPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) = 0 := by
  let a : ℝ → ℂ := fun θ => conj (deriv γ θ)
  let z : ℝ → ℂ := fun θ => conj (γ θ) - conj (γ 0)
  let K := physicalMomentPrimitive γ H
  let ν : ℝ → ℂ := fun θ => a θ * H θ
  let c : ℂ := (m + 1 : ℕ)
  have ha : Continuous a := Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hγconj : ContDiff ℝ 1 (fun θ => conj (γ θ)) := by
    simpa only [Function.comp_def, Complex.conjCLE_apply] using Complex.conjCLE.contDiff.comp hγ
  have hz : ContDiff ℝ 1 z := by
    exact hγconj.sub (contDiff_const (c := conj (γ 0)))
  have dz (θ : ℝ) : HasDerivAt z (a θ) θ := by
    simpa only [Complex.star_def] using
      ((hγ.differentiable_one θ).hasDerivAt.star).sub_const (conj (γ 0))
  have dv (θ : ℝ) : HasDerivAt (fun s => z s ^ (m + 1))
      (c * z θ ^ m * a θ) θ := by
    exact (dz θ).pow (m + 1)
  have hKAC : AbsolutelyContinuousOnInterval K 0 (2 * Real.pi) :=
    physicalMomentPrimitive_absolutelyContinuous γ H hγ hH
  have hKC : ContinuousOn K (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hKAC.continuousOn
  have hνI : IntegrableOn ν (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (physicalMomentDensity_memLp γ H hγ hH).integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
  have hfirst : IntegrableOn (fun θ => ν θ * z θ ^ (m + 1)) (Icc 0 (2 * Real.pi)) :=
    hνI.mul_continuousOn (hz.continuous.pow (m + 1)).continuousOn isCompact_Icc
  have hsecond : IntegrableOn (fun θ => (a θ * K θ) * z θ ^ m)
      (Icc 0 (2 * Real.pi)) :=
    ((ha.continuousOn.mul hKC).mul (hz.continuous.pow m).continuousOn).integrableOn_Icc
  have hprodAC : AbsolutelyContinuousOnInterval (fun θ => K θ * z θ ^ (m + 1))
      0 (2 * Real.pi) := by
    exact hKAC.smul (rough_c1_absolutelyContinuous (hz.pow (m + 1)))
  have hprodD : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (fun θ => K θ * z θ ^ (m + 1))
        (ν θ * z θ ^ (m + 1) + c * ((a θ * K θ) * z θ ^ m)) θ := by
    filter_upwards [physicalMomentPrimitive_ae_hasDerivAt γ H hγ hH] with θ hθ hmem
    convert (hθ hmem).mul (dv θ) using 1
    all_goals
      dsimp [ν, a, K]
      ring
  have hprodI := hfirst.add (hsecond.const_mul c)
  have hFTC := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    hprodAC hprodI hprodD (2 * Real.pi) ⟨Real.two_pi_pos.le, le_rfl⟩
  have hK0 : K 0 = 0 := physicalMomentPrimitive_zero γ H
  have hKL : K (2 * Real.pi) = 0 := physicalMomentPrimitive_endpoint γ H
    (by simpa only [pow_zero, mul_one] using hmom 0)
  rw [hK0, hKL, zero_mul, zero_mul, zero_add] at hFTC
  simp only [Pi.add_apply] at hFTC
  have hi₁ : IntervalIntegrable (fun θ => ν θ * z θ ^ (m + 1)) volume 0 (2 * Real.pi) :=
    IntegrableOn.intervalIntegrable
      (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hfirst)
  have hi₂ : IntervalIntegrable (fun θ => (a θ * K θ) * z θ ^ m) volume 0 (2 * Real.pi) :=
    IntegrableOn.intervalIntegrable (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hsecond)
  have hiMoment : (∫ θ in (0 : ℝ)..(2 * Real.pi), ν θ * z θ ^ (m + 1)) = 0 :=
    hmom (m + 1)
  change 0 = ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (ν θ * z θ ^ (m + 1) + c * ((a θ * K θ) * z θ ^ m)) at hFTC
  rw [intervalIntegral.integral_add hi₁ (hi₂.const_mul c),
    intervalIntegral.integral_const_mul, hiMoment, zero_add] at hFTC
  have hc : c ≠ 0 := by
    dsimp [c]
    intro hc
    have hre := congrArg Complex.re hc
    norm_num at hre
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    linarith
  exact (mul_eq_zero.mp hFTC.symm).resolve_left hc

theorem physicalMomentPeriodicPrimitive_moments_of_memLp (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0) (m : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * physicalMomentPeriodicPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) = 0 := by
  have heq := physicalMomentPeriodicPrimitive_eqOn γ H
    (by simpa only [pow_zero, mul_one] using hmom 0)
  rw [show (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * physicalMomentPeriodicPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * physicalMomentPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) from by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    simp only [heq hθ]]
  exact physicalMomentPrimitive_moments_of_memLp γ H hγ hH hmom m

/-- The actual continuous periodization has H¹ coefficients. -/
theorem physicalMomentPeriodicPrimitive_isSobolevSeq_one (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (physicalMomentPeriodicPrimitive γ H)) := by
  have heq : fourierCoeffOn Real.two_pi_pos (physicalMomentPeriodicPrimitive γ H) =
      fourierCoeffOn Real.two_pi_pos (physicalMomentPrimitive γ H) := by
    funext n
    exact fourierCoeffOn_congr_Icc (physicalMomentPeriodicPrimitive_eqOn γ H hmom0) n
  rw [heq]
  exact physicalMomentPrimitive_isSobolevSeq_one γ H hγ hH hmom0

/-- Genuine AC Fourier differentiation for all modes, including n=0. -/
theorem physicalMomentDensity_fourierCoeffOn (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv γ θ) * H θ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos
        (physicalMomentPeriodicPrimitive γ H) n := by
  have hp : physicalMomentPrimitive γ H 0 = physicalMomentPrimitive γ H (2 * Real.pi) := by
    rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0]
  rw [fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalMomentPrimitive_absolutelyContinuous γ H hγ hH)
    (physicalMomentDensity_memLp γ H hγ hH)
    (physicalMomentPrimitive_ae_hasDerivAt γ H hγ hH) hp n,
    fourierCoeffOn_congr_Icc (physicalMomentPeriodicPrimitive_eqOn γ H hmom0) n]

theorem physicalMomentDensity_fourierCoeffOn_zero (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv γ θ) * H θ) 0 = 0 := by
  rw [physicalMomentDensity_fourierCoeffOn γ H hγ hH hmom0]
  simp only [Int.cast_zero, mul_zero, zero_mul]

/-- The existing continuous criterion is applied to the actual first
primitive; the original rough density has not been made continuous. -/
theorem localConformal_physicalMomentPeriodicPrimitive_nonpositive
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball (0 : ℂ) 1 = Ω) (H : ℝ → ℂ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalMomentPeriodicPrimitive (physicalCircleTrace F) H)) := by
  have hγ : ContDiff ℝ 1 (physicalCircleTrace F) :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  exact localConformal_physicalMoments_nonpositive hb hΩ hR F hFs hhol hinj hnz himage
    (physicalMomentPeriodicPrimitive (physicalCircleTrace F) H)
    (physicalMomentPeriodicPrimitive_continuous _ H hγ hH
      (by simpa only [pow_zero, mul_one] using hmom 0))
    (physicalMomentPeriodicPrimitive_periodic _ H)
    (physicalMomentPeriodicPrimitive_moments_of_memLp _ H hγ hH hmom)

/-- The a.e. derivative has strictly negative support, with zero frequency
proved by the endpoint identity rather than discarded. -/
theorem physicalMomentDensity_strictNegative_of_primitive_support (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0)
    (hK : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalMomentPeriodicPrimitive γ H))) :
    IsStrictNegativeFourierSupport (fourierCoeffOn Real.two_pi_pos
      (fun θ => conj (deriv γ θ) * H θ)) := by
  have hp : physicalMomentPrimitive γ H 0 = physicalMomentPrimitive γ H (2 * Real.pi) := by
    rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0]
  intro n hn
  rw [fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalMomentPrimitive_absolutelyContinuous γ H hγ hH)
    (physicalMomentDensity_memLp γ H hγ hH)
    (physicalMomentPrimitive_ae_hasDerivAt γ H hγ hH) hp n]
  by_cases hn0 : n = 0
  · subst n
    simp only [Int.cast_zero, mul_zero, zero_mul]
  · rw [← fourierCoeffOn_congr_Icc (physicalMomentPeriodicPrimitive_eqOn γ H hmom0) n,
      hK n (by omega), mul_zero]

private theorem rough_fourierCoeffOn_conj (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ => conj (f θ)) n =
      conj (fourierCoeffOn Real.two_pi_pos f (-n)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [smul_eq_mul, map_mul, neg_neg]
  congr 1
  simpa only [fourier_coe_apply, sub_zero] using
    (fourier_neg (n := n) (x := (θ : AddCircle (2 * Real.pi))))

private theorem rough_fourier_one_circle (θ : ℝ) :
    fourier (T := 2 * Real.pi) 1 (θ : AddCircle (2 * Real.pi)) = circleMap 0 1 θ := by
  simp only [fourier_coe_two_pi, circleMap_zero, Int.cast_one, Complex.ofReal_one, one_mul]

private theorem rough_fourierCoeffOn_circle_mul (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ => circleMap 0 1 θ * f θ) n =
      fourierCoeffOn Real.two_pi_pos f (n - 1) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  have hrough :
      fourier (T := 2 * Real.pi - 0) 1 (θ : AddCircle (2 * Real.pi - 0)) =
        circleMap 0 1 θ := by
    rw [fourier_coe_apply, circleMap_zero]
    norm_num [Real.pi_ne_zero]
    congr 1
    field_simp [Real.pi_ne_zero]
  have hcalc :
      fourier (T := 2 * Real.pi - 0) (-n) (θ : AddCircle (2 * Real.pi - 0)) *
          (circleMap 0 1 θ * f θ) =
        fourier (T := 2 * Real.pi - 0) (-(n - 1)) (θ : AddCircle (2 * Real.pi - 0)) * f θ := by
    rw [← hrough]
    calc
      fourier (T := 2 * Real.pi - 0) (-n) (θ : AddCircle (2 * Real.pi - 0)) *
            (fourier (T := 2 * Real.pi - 0) 1 (θ : AddCircle (2 * Real.pi - 0)) * f θ) =
          (fourier (T := 2 * Real.pi - 0) (-n) (θ : AddCircle (2 * Real.pi - 0)) *
            fourier (T := 2 * Real.pi - 0) 1 (θ : AddCircle (2 * Real.pi - 0))) * f θ := by ring
      _ = fourier (T := 2 * Real.pi - 0) (-n + 1) (θ : AddCircle (2 * Real.pi - 0)) * f θ := by
        rw [fourier_add]
      _ = fourier (T := 2 * Real.pi - 0) (-(n - 1)) (θ : AddCircle (2 * Real.pi - 0)) * f θ := by
        rw [show -n + 1 = -(n - 1) by omega]
  exact hcalc

private theorem rough_c1_fourier_summable {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hp : Function.Periodic f (2 * Real.pi)) :
    Summable (fourierCoeffOn Real.two_pi_pos f) := by
  have hreg := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (rough_c1_absolutelyContinuous hf)
    (rough_continuousOn_memLp_two hf.continuous_deriv_one.continuousOn)
    (Eventually.of_forall fun θ _ => (hf.differentiable_one θ).hasDerivAt)
    (by simpa only [zero_add] using (hp 0).symm)
  exact Summable.of_norm ((sq_tsum_norm_le (s := 0) (by norm_num)
    (by simpa only [zero_add] using hreg)).1)

/-- The actual reciprocal coordinate coefficient used to recover the rough
density from its weighted derivative. -/
def physicalMomentRecoveryCoefficient (F : ℂ → ℂ) (θ : ℝ) : ℂ :=
  Complex.I * (circleMap 0 1 θ * conj (physicalCircleTrace (physicalMomentQuotient F 0) θ))

theorem physicalMomentRecoveryCoefficient_periodic (F : ℂ → ℂ) :
    Function.Periodic (physicalMomentRecoveryCoefficient F) (2 * Real.pi) := by
  intro θ
  unfold physicalMomentRecoveryCoefficient
  rw [(periodic_circleMap 0 1) θ, (physicalCircleTrace_periodic (physicalMomentQuotient F 0)) θ]

theorem physicalMomentRecoveryCoefficient_contDiff {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) :
    ContDiff ℝ 1 (physicalMomentRecoveryCoefficient F) := by
  have hq := physicalMomentQuotient_circle_contDiff hR F hFs hnz 0
  have hqconj : ContDiff ℝ 1 (fun θ => conj (physicalCircleTrace (physicalMomentQuotient F 0) θ)) := by
    simpa only [Function.comp_def, Complex.conjCLE_apply] using Complex.conjCLE.contDiff.comp hq
  exact (contDiff_const (c := Complex.I)).mul ((contDiff_circleMap 0 1).mul hqconj)

/-- The actual continuous circle coefficient, descended from its equal endpoints. -/
def physicalMomentRecoveryCircle {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) :
    C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨AddCircle.liftIoc (2 * Real.pi) 0 (physicalMomentRecoveryCoefficient F),
    AddCircle.liftIoc_zero_continuous
      (by simpa only [zero_add] using (physicalMomentRecoveryCoefficient_periodic F 0).symm)
      (physicalMomentRecoveryCoefficient_contDiff hR F hFs hnz).continuous.continuousOn⟩

theorem physicalMomentRecoveryCircle_apply {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Ioc 0 (2 * Real.pi)) :
    physicalMomentRecoveryCircle hR F hFs hnz (θ : AddCircle (2 * Real.pi)) =
      physicalMomentRecoveryCoefficient F θ := by
  change AddCircle.liftIoc (2 * Real.pi) 0 (physicalMomentRecoveryCoefficient F)
    (θ : AddCircle (2 * Real.pi)) = physicalMomentRecoveryCoefficient F θ
  exact AddCircle.liftIoc_zero_coe_apply hθ

theorem physicalMomentRecoveryCircle_summable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) :
    Summable (fourierCoeff (physicalMomentRecoveryCircle hR F hFs hnz)) := by
  have heq : fourierCoeff (physicalMomentRecoveryCircle hR F hFs hnz) =
      fourierCoeffOn Real.two_pi_pos (physicalMomentRecoveryCoefficient F) := by
    funext n
    simp only [physicalMomentRecoveryCircle, ContinuousMap.coe_mk, fourierCoeff_liftIoc_eq,
      zero_add]
  rw [heq]
  exact rough_c1_fourier_summable (physicalMomentRecoveryCoefficient_contDiff hR F hFs hnz)
    (physicalMomentRecoveryCoefficient_periodic F)

/-- The recovery multiplier has no Fourier frequencies above one. This
comes from the genuine holomorphic reciprocal differential, not an assumed
Hardy multiplier property. -/
theorem physicalMomentRecoveryCircle_coeff_eq_zero_of_one_lt
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    {n : ℤ} (hn : 1 < n) :
    fourierCoeff (physicalMomentRecoveryCircle hR F hFs hnz) n = 0 := by
  have hq : DiffContOnCl ℂ (physicalMomentQuotient F 0) (ball (0 : ℂ) 1) := by
    apply DiffContOnCl.mk_ball (physicalMomentQuotient_holomorphic F hhol hnz 0)
    intro z hz
    exact (physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz 0 hz).continuousAt.continuousWithinAt
  simp only [physicalMomentRecoveryCircle, ContinuousMap.coe_mk, fourierCoeff_liftIoc_eq,
    zero_add]
  change fourierCoeffOn Real.two_pi_pos
    (fun θ => Complex.I * (circleMap 0 1 θ * conj
      (physicalCircleTrace (physicalMomentQuotient F 0) θ))) n = 0
  rw [fourierCoeffOn.const_mul, rough_fourierCoeffOn_circle_mul, rough_fourierCoeffOn_conj,
    physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg (physicalMomentQuotient F 0) hq
      (by omega), map_zero, mul_zero]

/-- Exact pointwise recovery from the true angular derivative, valid even
for an arbitrary measurable representative of the original density. -/
theorem physicalMomentRecoveryCoefficient_mul_density {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (H : ℝ → ℂ) (θ : ℝ) :
    physicalMomentRecoveryCoefficient F θ * (conj (deriv (physicalCircleTrace F) θ) * H θ) =
      H θ := by
  let z := circleMap 0 1 θ
  let D := fderiv ℝ F z 1
  have hD : D ≠ 0 := hnz z (circleMap_mem_closedBall 0 (by norm_num) θ)
  have hz : z * conj z = 1 := by
    rw [Complex.mul_conj]
    have hnorm : ‖z‖ = 1 := by simp [z, norm_circleMap_zero]
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [physicalMomentRecoveryCoefficient, localConformal_circleTrace_deriv hR F hFs hhol]
  change (Complex.I * (z * conj (1 / D))) * (conj (D * (z * Complex.I)) * H θ) = H θ
  simp only [map_div₀, map_one, map_mul, Complex.conj_I]
  have hcD : conj D ≠ 0 := by
    simpa only [starRingEnd_apply] using (star_ne_zero.mpr hD)
  calc
    _ = ((Complex.I * -Complex.I) * (z * conj z) * (conj D / conj D)) * H θ := by ring
    _ = H θ := by rw [hz, div_self hcD]; simp

private theorem rough_seqConv_upper_one_strictNegative {a h : ℤ → ℂ}
    (ha : ∀ n : ℤ, 1 < n → a n = 0) (hh : IsStrictNegativeFourierSupport h)
    {n : ℤ} (hn : 0 < n) : seqConv a h n = 0 := by
  unfold seqConv
  calc
    _ = ∑' _ : ℤ, (0 : ℂ) := by
      apply tsum_congr
      intro k
      by_cases hk : 1 < k
      · rw [ha k hk, zero_mul]
      · rw [hh (n - k) (by omega), mul_zero]
    _ = 0 := tsum_zero

/-- Genuine L² physical moment criterion for the original density. The
all-input multiplication is the actual boundary Fourier CLM identity. -/
theorem localConformal_physicalMoments_nonpositive_of_memLp
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball (0 : ℂ) 1 = Ω) (H : ℝ → ℂ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hγ : ContDiff ℝ 1 (physicalCircleTrace F) :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hK := localConformal_physicalMomentPeriodicPrimitive_nonpositive
    hb hΩ hR F hFs hhol hinj hnz himage H hH hmom
  have hνsupport := physicalMomentDensity_strictNegative_of_primitive_support
    (physicalCircleTrace F) H hγ hH
    (by simpa only [pow_zero, mul_one] using hmom 0) hK
  let ν : ℝ → ℂ := fun θ => conj (deriv (physicalCircleTrace F) θ) * H θ
  have hν : MemLp ν 2 (volume.restrict (Ioc 0 (2 * Real.pi))) :=
    physicalMomentDensity_memLp _ H hγ hH
  let v : BoundaryL2 := hν.toLp ν
  let A := physicalMomentRecoveryCircle hR F hFs hnz
  have hrecover : boundaryContinuousMultiplier A v = hH.toLp H := by
    apply Lp.ext
    filter_upwards [boundaryContinuousMultiplier_ae A v, hν.coeFn_toLp, hH.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with θ hmul hv hHθ hθ
    rw [hmul, hv, hHθ, physicalMomentRecoveryCircle_apply hR F hFs hnz hθ]
    exact physicalMomentRecoveryCoefficient_mul_density hR F hFs hhol hnz H θ
  have hνBF : IsStrictNegativeFourierSupport (boundaryFourier v) := by
    intro n hn
    rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hν.coeFn_toLp,
      hνsupport n hn, mul_zero]
  have hsA : Summable (fourierCoeff A) := physicalMomentRecoveryCircle_summable hR F hFs hnz
  have hBF : IsNonpositiveFourierSupport (boundaryFourier (hH.toLp H)) := by
    intro n hn
    rw [← hrecover, boundaryFourier_continuousMultiplier A hsA]
    exact rough_seqConv_upper_one_strictNegative
      (fun k hk => physicalMomentRecoveryCircle_coeff_eq_zero_of_one_lt hR F hFs hhol hnz hk)
      hνBF hn
  intro n hn
  have hnBF := hBF n hn
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hH.coeFn_toLp] at hnBF
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  exact (mul_eq_zero.mp hnBF).resolve_left hs

/-- The actual BoundaryL2 form, useful without choosing any continuous
representative or assigning a value to a critical Sobolev trace. -/
theorem localConformal_physicalMoments_nonpositive_boundaryL2
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball (0 : ℂ) 1 = Ω) (H : BoundaryL2)
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (boundaryFourier H) := by
  have h := localConformal_physicalMoments_nonpositive_of_memLp
    hb hΩ hR F hFs hhol hinj hnz himage H (Lp.memLp H) hmom
  intro n hn
  rw [boundaryFourier_apply, h n hn, mul_zero]

/-- Closed-disk differential nonvanishing follows from the actual local
inverse and its genuine real smoothness. No extra boundary regularity or
nonvanishing assumption is imposed on the supplied coordinate tuple. -/
theorem localConformal_closedDifferential_ne_zero_of_smoothInverse
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) :
    ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0 := by
  intro z hz
  have hzs := hsource hz
  have hzt : F z ∈ e.target := by
    rw [← he]
    exact e.mapsTo hzs
  have hdF := ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt (by simp)).hasFDerivAt
  have hdG := ((hes.contDiffAt (e.open_target.mem_nhds hzt)).differentiableAt
    (by simp)).hasFDerivAt
  have hcomp := hdG.comp z hdF
  have hid : HasFDerivAt (fun x : ℂ => x)
      ((fderiv ℝ e.symm (F z)).comp (fderiv ℝ F z)) z := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hzs] with x hx
    rw [← he]
    exact (e.left_inv hx).symm
  have hlin := hid.unique (hasFDerivAt_id z)
  have hval := congrArg (fun A : ℂ →L[ℝ] ℂ => A 1) hlin
  change fderiv ℝ e.symm (F z) (fderiv ℝ F z 1) = (1 : ℂ) at hval
  intro hzero
  rw [hzero, map_zero] at hval
  exact zero_ne_one hval

/-- Full supplied-coordinate version of the rough physical moment
criterion. Closed injectivity and the boundary reciprocal are derived from
the actual smooth inverse. The original L² density need not be periodic as
a pointwise representative. -/
theorem localConformal_physicalMoments_nonpositive_of_memLp_of_smoothInverse
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) (H : ℝ → ℂ)
    (hH : MemLp H 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hinj : InjOn F (closedBall (0 : ℂ) 1) := by
    rw [← he]
    exact e.injOn.mono hsource
  have hnz := localConformal_closedDifferential_ne_zero_of_smoothInverse
    hR F hFs e he hsource hes
  exact localConformal_physicalMoments_nonpositive_of_memLp
    hb hL hR F hFs hhol hinj hnz rfl H hH hmom

theorem localConformal_physicalMoments_nonpositive_boundaryL2_of_smoothInverse
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) (H : BoundaryL2)
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (boundaryFourier H) := by
  have h := localConformal_physicalMoments_nonpositive_of_memLp_of_smoothInverse
    hR F hFs hb hL hhol e he hsource hes H (Lp.memLp H) hmom
  intro n hn
  rw [boundaryFourier_apply, h n hn, mul_zero]

end PolyaNeumann

end
