module

public import RequestProject.PhysicalHardySupport
public import RequestProject.CutFourier
public import RequestProject.ArcLength
public import RequestProject.HardyPrimitiveTrace

/-!
# Weighted Fourier coefficients of the supplied physical circle trace

Real C⁴ regularity near the closed disk implies the actual averaged Fourier
coefficients of `conj γ'` belong to weighted ℓ¹ of order one, and those of
`γ - γ 0` belong to weighted ℓ¹ of order two.  The estimates follow from
integration by parts and the periodic derivative summability theorem in
`CutFourier`; neither constant speed nor exterior holomorphicity is required.

The centered trace retains its actual average coefficient.  Absolute Fourier
reconstruction agrees with the physical function at every real parameter.
Holomorphicity in the open disk is used only for the support assertion imported
from `PhysicalHardySupport`, not as a substitute for the weighted estimates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate

local instance physicalWeightsTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Periodic real C⁴ regularity gives the two weighted estimates needed for
the physical primitive multiplier and the centered boundary coordinate. -/
theorem periodic_contDiff_four_fourier_weights {f : ℝ → ℂ}
    (hf : ContDiff ℝ 4 f) (hp : Function.Periodic f (2 * Real.pi)) :
    IsWL1 1 (fourierCoeffOn Real.two_pi_pos (deriv f)) ∧
      IsWL1 2 (fourierCoeffOn Real.two_pi_pos f) := by
  have hf1 : ContDiff ℝ 3 (deriv f) :=
    (show ContDiff ℝ (3 + 1) f from hf).deriv'
  have hf2 : ContDiff ℝ 2 (deriv (deriv f)) :=
    (show ContDiff ℝ (2 + 1) (deriv f) from hf1).deriv'
  have hf3 : ContDiff ℝ 1 (deriv (deriv (deriv f))) :=
    (show ContDiff ℝ (1 + 1) (deriv (deriv f)) from hf2).deriv'
  have d1 : ∀ x, HasDerivAt f (deriv f x) x :=
    fun x => (hf.differentiable (by norm_num) x).hasDerivAt
  have d2 : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    fun x => (hf1.differentiable (by norm_num) x).hasDerivAt
  have d3 : ∀ x, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x :=
    fun x => (hf2.differentiable (by norm_num) x).hasDerivAt
  have d4 : ∀ x, HasDerivAt (deriv (deriv (deriv f)))
      (deriv (deriv (deriv (deriv f))) x) x :=
    fun x => (hf3.differentiable_one x).hasDerivAt
  have hp1 := deriv_periodic hp
  have hp2 := deriv_periodic hp1
  have hp3 := deriv_periodic hp2
  have p0 : f 0 = f (2 * Real.pi) := by simpa only [zero_add] using (hp 0).symm
  have p1 : deriv f 0 = deriv f (2 * Real.pi) := by
    simpa only [zero_add] using (hp1 0).symm
  have p2 : deriv (deriv f) 0 = deriv (deriv f) (2 * Real.pi) := by
    simpa only [zero_add] using (hp2 0).symm
  have p3 : deriv (deriv (deriv f)) 0 = deriv (deriv (deriv f)) (2 * Real.pi) := by
    simpa only [zero_add] using (hp3 0).symm
  have hs1 : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos (deriv f) n‖) :=
    summable_norm_fourierCoeffOn_deriv d1 d2 d3 hf3.continuous p0 p1 p2
  have hs2 : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos (deriv (deriv f)) n‖) :=
    summable_norm_fourierCoeffOn_deriv d2 d3 d4 hf3.continuous_deriv_one p1 p2 p3
  have e1 (n : ℤ) : fourierCoeffOn Real.two_pi_pos (deriv f) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos f n :=
    fourierCoeffOn_deriv d1 hf1.continuous p0 n
  have e2 (n : ℤ) : fourierCoeffOn Real.two_pi_pos (deriv (deriv f)) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos (deriv f) n :=
    fourierCoeffOn_deriv d2 hf2.continuous p1 n
  have hs0 : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos f n‖) := by
    refine (hs1.add ((hasSum_ite_eq (0 : ℤ)
      ‖fourierCoeffOn Real.two_pi_pos f 0‖).summable)).of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => ?_)
    by_cases hn : n = 0
    · subst n
      simp
    · rw [if_neg hn, add_zero, e1]
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
      have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
        exact Int.one_le_abs hn
      nlinarith [norm_nonneg (fourierCoeffOn Real.two_pi_pos f n)]
  constructor
  · change Summable (fun n => sobWeight n ^ (1 : ℝ) *
      ‖fourierCoeffOn Real.two_pi_pos (deriv f) n‖)
    refine (hs1.add hs2).congr fun n => ?_
    rw [e2]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast,
      Real.rpow_one, sobWeight]
    ring
  · change Summable (fun n => sobWeight n ^ (2 : ℝ) *
      ‖fourierCoeffOn Real.two_pi_pos f n‖)
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _)
        (norm_nonneg _)) (fun n => ?_) ((hs0.mul_left 2).add (hs2.mul_left 2))
    rw [e2, e1]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast,
      Real.rpow_two, sobWeight]
    have hnonneg : 0 ≤ (|(n : ℝ)| - 1) ^ 2 *
        ‖fourierCoeffOn Real.two_pi_pos f n‖ :=
      mul_nonneg (sq_nonneg _) (norm_nonneg _)
    nlinarith

private theorem physicalWeights_fourierCoeffOn_conj (g : ℝ → ℂ) (n : ℤ) :
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

/-- Conjugation reflects the Fourier indices and preserves the weighted ℓ¹ norm. -/
theorem isWL1_fourierCoeffOn_conj {s : ℝ} {g : ℝ → ℂ}
    (hg : IsWL1 s (fourierCoeffOn Real.two_pi_pos g)) :
    IsWL1 s (fourierCoeffOn Real.two_pi_pos (fun θ => conj (g θ))) := by
  change Summable (fun n => sobWeight n ^ s *
    ‖fourierCoeffOn Real.two_pi_pos (fun θ => conj (g θ)) n‖)
  have hs := hg.comp_injective
    (show Function.Injective (fun n : ℤ => -n) from neg_injective)
  refine hs.congr fun n => ?_
  simp only [Function.comp_apply, physicalWeights_fourierCoeffOn_conj,
    Complex.norm_conj, sobWeight, Int.cast_neg, abs_neg]

/-- The supplied real C⁴ map is C⁴ along the actual circle. -/
theorem contDiff_physicalCircleTrace_four_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 4 F (ball (0 : ℂ) R)) :
    ContDiff ℝ 4 (physicalCircleTrace F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hz : circleMap 0 1 θ ∈ ball (0 : ℂ) R :=
    closedBall_subset_ball hR (circleMap_mem_closedBall 0 (by norm_num) θ)
  exact (hFs.contDiffAt (isOpen_ball.mem_nhds hz)).comp θ
    (contDiff_circleMap 0 1).contDiffAt

/-- Actual physical coefficients satisfy both weighted hypotheses.  Real
smoothness near the closure suffices; no boundary parametrization is assumed. -/
theorem physicalCircleTrace_fourier_weights_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 4 F (ball (0 : ℂ) R)) :
    IsWL1 1 (fourierCoeffOn Real.two_pi_pos
      (fun θ => conj (deriv (physicalCircleTrace F) θ))) ∧
      IsWL1 2 (fourierCoeffOn Real.two_pi_pos
        (fun θ => physicalCircleTrace F θ - physicalCircleTrace F 0)) := by
  have hγ := contDiff_physicalCircleTrace_four_of_neighborhood hR F hFs
  have hp := physicalCircleTrace_periodic F
  refine ⟨isWL1_fourierCoeffOn_conj
    (periodic_contDiff_four_fourier_weights hγ hp).1, ?_⟩
  exact (periodic_contDiff_four_fourier_weights
    (hγ.sub contDiff_const) (hp.comp (fun z => z - physicalCircleTrace F 0))).2

/-- Smooth supplied coordinates give the same finite weighted hypotheses. -/
theorem physicalCircleTrace_fourier_weights_of_smooth_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    IsWL1 1 (fourierCoeffOn Real.two_pi_pos
      (fun θ => conj (deriv (physicalCircleTrace F) θ))) ∧
      IsWL1 2 (fourierCoeffOn Real.two_pi_pos
        (fun θ => physicalCircleTrace F θ - physicalCircleTrace F 0)) :=
  physicalCircleTrace_fourier_weights_of_neighborhood hR F
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top))

/-- Open-disk holomorphicity supplies the genuine support of the same actual
coefficient to which the weighted estimate applies. -/
theorem physicalCircleTrace_multiplier_data_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 4 F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    IsWL1 1 (fourierCoeffOn Real.two_pi_pos
      (fun θ => conj (deriv (physicalCircleTrace F) θ))) ∧
      IsStrictNegativeFourierSupport (fourierCoeffOn Real.two_pi_pos
        (fun θ => conj (deriv (physicalCircleTrace F) θ))) :=
  ⟨(physicalCircleTrace_fourier_weights_of_neighborhood hR F hFs).1,
    physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood hR F
      (hFs.of_le (by norm_num)) hhol⟩

/-- Absolutely convergent averaged Fourier reconstruction of a continuous
periodic physical function, at every real parameter. -/
theorem hardyFourierTrace_fourierCoeffOn_of_periodic {f : ℝ → ℂ}
    (hf : Continuous f) (hp : Function.Periodic f (2 * Real.pi))
    (hs : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos f n‖)) (θ : ℝ) :
    hardyFourierTrace (fourierCoeffOn Real.two_pi_pos f) θ = f θ := by
  let u := AddCircle.equivIco (2 * Real.pi) 0 (θ : AddCircle (2 * Real.pi))
  have hu : ((u : ℝ) : AddCircle (2 * Real.pi)) = (θ : AddCircle (2 * Real.pi)) :=
    (AddCircle.equivIco (2 * Real.pi) 0).left_inv _
  have hut : (u : ℝ) ∈ Ico 0 (2 * Real.pi) := by
    simpa only [zero_add] using u.property
  have huv : f (u : ℝ) = f θ := by
    calc
      f (u : ℝ) = hp.lift ((u : ℝ) : AddCircle (2 * Real.pi)) := (hp.lift_coe _).symm
      _ = hp.lift (θ : AddCircle (2 * Real.pi)) := congrArg hp.lift hu
      _ = f θ := hp.lift_coe θ
  have p0 : f 0 = f (2 * Real.pi) := by simpa only [zero_add] using (hp 0).symm
  have hsum := hasSum_fourierCoeffOn hf p0 hs.of_norm hut
  have hsum' : HasSum (fun n : ℤ => fourierCoeffOn Real.two_pi_pos f n *
      fourier (T := 2 * Real.pi) n (θ : AddCircle (2 * Real.pi))) (f θ) := by
    simpa only [← fourier_coe_two_pi, hu, huv] using hsum
  exact hsum'.tsum_eq

/-- Reconstruction of the actual conjugated velocity from its weighted data. -/
theorem hardyFourierTrace_physical_conj_deriv_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 4 F (ball (0 : ℂ) R)) (θ : ℝ) :
    hardyFourierTrace (fourierCoeffOn Real.two_pi_pos
      (fun s => conj (deriv (physicalCircleTrace F) s))) θ =
      conj (deriv (physicalCircleTrace F) θ) := by
  have hγ := contDiff_physicalCircleTrace_four_of_neighborhood hR F hFs
  have hc : Continuous (fun s => conj (deriv (physicalCircleTrace F) s)) :=
    Complex.continuous_conj.comp (hγ.continuous_deriv (by norm_num))
  have hp : Function.Periodic (fun s => conj (deriv (physicalCircleTrace F) s))
      (2 * Real.pi) := (deriv_periodic (physicalCircleTrace_periodic F)).comp conj
  have hw := (physicalCircleTrace_fourier_weights_of_neighborhood hR F hFs).1
  have hs : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos
      (fun s => conj (deriv (physicalCircleTrace F) s)) n‖) := by
    have hw' : Summable (fun n => sobWeight n * ‖fourierCoeffOn Real.two_pi_pos
        (fun s => conj (deriv (physicalCircleTrace F) s)) n‖) := by
      simpa only [IsWL1, Real.rpow_one] using hw
    exact hw'.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      le_mul_of_one_le_left (norm_nonneg _) (one_le_sobWeight n))
  exact hardyFourierTrace_fourierCoeffOn_of_periodic hc hp hs θ

/-- Reconstruction retains the actual centered trace, including its average. -/
theorem hardyFourierTrace_physical_centered_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 4 F (ball (0 : ℂ) R)) (θ : ℝ) :
    hardyFourierTrace (fourierCoeffOn Real.two_pi_pos
      (fun s => physicalCircleTrace F s - physicalCircleTrace F 0)) θ =
      physicalCircleTrace F θ - physicalCircleTrace F 0 := by
  have hγ := contDiff_physicalCircleTrace_four_of_neighborhood hR F hFs
  have hw := (physicalCircleTrace_fourier_weights_of_neighborhood hR F hFs).2
  have hs : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos
      (fun s => physicalCircleTrace F s - physicalCircleTrace F 0) n‖) := by
    exact hw.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      le_mul_of_one_le_left (norm_nonneg _)
        (Real.one_le_rpow (one_le_sobWeight n) (by norm_num)))
  exact hardyFourierTrace_fourierCoeffOn_of_periodic (hγ.continuous.sub continuous_const)
    ((physicalCircleTrace_periodic F).comp (fun z => z - physicalCircleTrace F 0)) hs θ

end PolyaNeumann

end
