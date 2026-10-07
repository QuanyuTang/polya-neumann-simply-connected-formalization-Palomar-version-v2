module

public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import RequestProject.DiskHarmonicModes
public import RequestProject.NeumannTraceInjective
public import RequestProject.BoundaryFourier
public import RequestProject.SobolevMultiplier
public import RequestProject.Herglotz

/-!
# The actual half-order H¹ trace on the unit disk

Green's identity is tested against compactly supported extensions of the
harmonic monomials. The resulting Fourier coefficients are the coefficients
of the actual H¹ boundary trace. Bessel's inequality in the physical gradient
Hilbert space controls the nonzero frequencies. The bounded L² trace controls
the remaining part of the weight, including frequency zero.

The Fourier transform is normalized for ordinary parameter measure `dθ`.
Accordingly the nonzero-frequency estimate has constant one in these
orthonormal Fourier coordinates, and constant `1 / (2π)` for average
Fourier coefficients. The disk is an auxiliary domain throughout.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter Real
open scoped Real ComplexConjugate InnerProductSpace Topology

local instance factTwoPiPosDHT : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The already constructed physical trace, specialized to the unit disk. -/
def diskH1Trace : NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] BoundaryL2 :=
  h1BoundaryTrace unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam

/-- The two actual weak-gradient components, in their physical L² space. -/
def diskH1Gradient (u : NeumannH1 (ball (0 : ℂ) 1)) : DiskGradientSpace :=
  WithLp.toLp 2 (fun i => h1Gradient (ball (0 : ℂ) 1) i u)

theorem norm_sq_diskH1Gradient (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ‖diskH1Gradient u‖ ^ 2 = ∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i u‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

theorem norm_sq_diskH1Gradient_le (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ‖diskH1Gradient u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [norm_sq_diskH1Gradient, h1_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Orthonormal Fourier coordinates of the actual boundary trace. -/
def diskH1Fourier : NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  (boundaryFourier : BoundaryL2 →L[ℂ] L2Z).comp diskH1Trace

@[simp] theorem diskH1Fourier_apply (u : NeumannH1 (ball (0 : ℂ) 1)) (n : ℤ) :
    diskH1Fourier u n = (√(2 * π) : ℂ) *
      fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n :=
  boundaryFourier_apply (diskH1Trace u) n

private lemma disk_integral_fourier (r : ℝ → ℂ) (n : ℤ) :
    (∫ θ in Ioc (0 : ℝ) (2 * π),
      r θ * Complex.exp (-((n : ℂ) * Complex.I * θ))) =
        (2 * π : ℂ) * fourierCoeffOn two_pi_pos r n := by
  rw [← intervalIntegral.integral_of_le two_pi_pos.le,
    ← coeffIntegral_eq_fourierCoeffOn]
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast two_pi_pos.ne'
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [mul_comm (r θ)]
  congr 1
  congr 1
  ring

private lemma unitCircle_mem_cutoff_ball (θ : ℝ) :
    circleMap 0 1 θ ∈ ball (0 : ℂ) 2 := by
  rw [mem_ball_zero_iff]
  simp

private lemma inner_diskHolomorphicGradient_h1 (m : ℕ)
    (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ⟪diskHolomorphicGradient m, diskH1Gradient u⟫_ℂ =
      ∑ i : Fin 2, ∫ z in ball (0 : ℂ) 1,
        h1Gradient (ball (0 : ℂ) 1) i u z *
          dirD (diskAntiholomorphicMode m) (coordDir i) z := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diskHolomorphicGradient_ae m i] with z hz
  simp only [RCLike.inner_apply, hz, diskH1Gradient, PiLp.toLp_apply,
    conj_dirD_diskHolomorphicMode]

private lemma inner_diskAntiholomorphicGradient_h1 (m : ℕ)
    (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ⟪diskAntiholomorphicGradient m, diskH1Gradient u⟫_ℂ =
      ∑ i : Fin 2, ∫ z in ball (0 : ℂ) 1,
        h1Gradient (ball (0 : ℂ) 1) i u z *
          dirD (diskHolomorphicMode m) (coordDir i) z := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diskAntiholomorphicGradient_ae m i] with z hz
  simp only [RCLike.inner_apply, hz, diskH1Gradient, PiLp.toLp_apply,
    conj_dirD_diskAntiholomorphicMode]

/-- Fourier--Green for every actual H¹ vector, proved with the antiholomorphic test. -/
theorem disk_h1_fourier_green_pos (m : ℕ) (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ⟪diskHolomorphicGradient m, diskH1Gradient u⟫_ℂ =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (m : ℤ) := by
  have hgreen := h1_doubleLayer_green unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam
    (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)) u
  have hmass : (∫ z in ball (0 : ℂ) 1, h1Value (ball (0 : ℂ) 1) u z *
      lap (diskHarmonicCutoff (diskAntiholomorphicMode m)) z) = 0 := by
    calc
      _ = ∫ _z in ball (0 : ℂ) 1, (0 : ℂ) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro z hz
        dsimp only
        rw [lap_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz),
          lap_diskAntiholomorphicMode, mul_zero]
      _ = 0 := by simp
  have hgrad : (∑ i : Fin 2, ∫ z in ball (0 : ℂ) 1,
      h1Gradient (ball (0 : ℂ) 1) i u z *
        dirD (diskHarmonicCutoff (diskAntiholomorphicMode m)) (coordDir i) z) =
      ⟪diskHolomorphicGradient m, diskH1Gradient u⟫_ℂ := by
    rw [inner_diskHolomorphicGradient_h1]
    apply Finset.sum_congr rfl
    intro i _
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz)]
  have hboundary : (∫ θ in Ioc (0 : ℝ) (2 * π), diskH1Trace u θ *
      fderiv ℝ (diskHarmonicCutoff (diskAntiholomorphicMode m)) (circleMap 0 1 θ)
        (-(Complex.I * deriv (circleMap 0 1) θ))) =
      (m : ℂ) * ((2 * π : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (m : ℤ)) := by
    rw [← disk_integral_fourier, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ _
    dsimp only
    rw [fderiv_diskHarmonicCutoff_eq (unitCircle_mem_cutoff_ball θ),
      conormal_diskAntiholomorphicMode, diskAntiholomorphicMode_unitCircle]
    simp only [Int.cast_natCast]
    ring
  change _ = ∫ θ in Ioc (0 : ℝ) (2 * π), diskH1Trace u θ * _ at hgreen
  rw [hmass, zero_add, hgrad, hboundary] at hgreen
  exact hgreen.trans (by ring)

/-- The conjugate harmonic sector gives the negative Fourier frequencies. -/
theorem disk_h1_fourier_green_neg (m : ℕ) (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ⟪diskAntiholomorphicGradient m, diskH1Gradient u⟫_ℂ =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (-(m : ℤ)) := by
  have hgreen := h1_doubleLayer_green unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam
    (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)) u
  have hmass : (∫ z in ball (0 : ℂ) 1, h1Value (ball (0 : ℂ) 1) u z *
      lap (diskHarmonicCutoff (diskHolomorphicMode m)) z) = 0 := by
    calc
      _ = ∫ _z in ball (0 : ℂ) 1, (0 : ℂ) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro z hz
        dsimp only
        rw [lap_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz),
          lap_diskHolomorphicMode, mul_zero]
      _ = 0 := by simp
  have hgrad : (∑ i : Fin 2, ∫ z in ball (0 : ℂ) 1,
      h1Gradient (ball (0 : ℂ) 1) i u z *
        dirD (diskHarmonicCutoff (diskHolomorphicMode m)) (coordDir i) z) =
      ⟪diskAntiholomorphicGradient m, diskH1Gradient u⟫_ℂ := by
    rw [inner_diskAntiholomorphicGradient_h1]
    apply Finset.sum_congr rfl
    intro i _
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz)]
  have hboundary : (∫ θ in Ioc (0 : ℝ) (2 * π), diskH1Trace u θ *
      fderiv ℝ (diskHarmonicCutoff (diskHolomorphicMode m)) (circleMap 0 1 θ)
        (-(Complex.I * deriv (circleMap 0 1) θ))) =
      (m : ℂ) * ((2 * π : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (-(m : ℤ))) := by
    rw [← disk_integral_fourier, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ _
    dsimp only
    rw [fderiv_diskHarmonicCutoff_eq (unitCircle_mem_cutoff_ball θ),
      conormal_diskHolomorphicMode, diskHolomorphicMode_unitCircle]
    simp only [Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]
    ring
  change _ = ∫ θ in Ioc (0 : ℝ) (2 * π), diskH1Trace u θ * _ at hgreen
  rw [hmass, zero_add, hgrad, hboundary] at hgreen
  exact hgreen.trans (by ring)

private lemma disk_normalized_coefficient_norm (m : ℕ) (a : ℂ) :
    ‖conj (diskHarmonicGradientScale m) *
        ((2 * π : ℂ) * ((m + 1 : ℕ) : ℂ) * a)‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖(√(2 * π) : ℂ) * a‖ ^ 2 := by
  have hp : 0 < 2 * π * ((m + 1 : ℕ) : ℝ) := by positivity
  have hk : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hscale : ‖diskHarmonicGradientScale m‖ =
      (Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ :=
    Complex.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hperiod : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_of_nonneg two_pi_pos.le
  rw [norm_mul, Complex.norm_conj, hscale, norm_mul, norm_mul, hperiod,
    Complex.norm_natCast, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  simp only [mul_pow, inv_pow]
  rw [Real.sq_sqrt hp.le, Real.sq_sqrt two_pi_pos.le]
  field_simp [two_pi_pos.ne', hk]

theorem norm_sq_diskNormalizedHarmonicGradient_pos (m : ℕ)
    (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ‖⟪diskNormalizedHarmonicGradient (Sum.inl m), diskH1Gradient u⟫_ℂ‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖diskH1Fourier u ((m + 1 : ℕ) : ℤ)‖ ^ 2 := by
  rw [diskNormalizedHarmonicGradient, inner_smul_left, disk_h1_fourier_green_pos,
    diskH1Fourier_apply]
  exact disk_normalized_coefficient_norm m _

theorem norm_sq_diskNormalizedHarmonicGradient_neg (m : ℕ)
    (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ‖⟪diskNormalizedHarmonicGradient (Sum.inr m), diskH1Gradient u⟫_ℂ‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖diskH1Fourier u (-((m + 1 : ℕ) : ℤ))‖ ^ 2 := by
  rw [diskNormalizedHarmonicGradient, inner_smul_left, disk_h1_fourier_green_neg,
    diskH1Fourier_apply]
  exact disk_normalized_coefficient_norm m _

private lemma int_tsum_eq_halves (a : ℤ → ℝ) (b : ℕ ⊕ ℕ → ℝ)
    (hb : Summable b) (hzero : a 0 = 0)
    (hpos : ∀ m : ℕ, a ((m + 1 : ℕ) : ℤ) = b (Sum.inl m))
    (hneg : ∀ m : ℕ, a (-((m + 1 : ℕ) : ℤ)) = b (Sum.inr m)) :
    Summable a ∧ (∑' n : ℤ, a n) = ∑' j : ℕ ⊕ ℕ, b j := by
  have hbl := hb.comp_injective Sum.inl_injective
  have hbr := hb.comp_injective Sum.inr_injective
  have hpos' : Summable (fun m : ℕ => a ((m + 1 : ℕ) : ℤ)) :=
    hbl.congr (fun m => (hpos m).symm)
  have hpos0 : Summable (fun m : ℕ => a (m : ℤ)) :=
    (summable_nat_add_iff 1).mp hpos'
  have hneg' : Summable (fun m : ℕ => a (-((m + 1 : ℕ) : ℤ))) :=
    hbr.congr (fun m => (hneg m).symm)
  have hneg0 : Summable (fun m : ℕ => a (-(m + 1 : ℤ))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hneg'
  refine ⟨Summable.of_nat_of_neg_add_one hpos0 hneg0, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos0 hneg0, hpos0.tsum_eq_zero_add]
  simp only [Nat.cast_zero, hzero, zero_add]
  calc
    _ = (∑' m : ℕ, b (Sum.inl m)) + ∑' m : ℕ, b (Sum.inr m) := by
      congr 1
      · exact tsum_congr hpos
      · apply tsum_congr
        intro m
        simpa only [Nat.cast_add, Nat.cast_one] using hneg m
    _ = _ := (hbl.tsum_sum hbr).symm

/-- The weighted nonzero Fourier coefficients are summable, with the physical
gradient energy as their bound. Frequency zero contributes zero here. -/
theorem disk_h1_fourier_energy (u : NeumannH1 (ball (0 : ℂ) 1)) :
    Summable (fun n : ℤ => |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2) ∧
      (∑' n : ℤ, |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2) ≤
        ‖diskH1Gradient u‖ ^ 2 := by
  let a : ℤ → ℝ := fun n => |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2
  let b : ℕ ⊕ ℕ → ℝ := fun j =>
    ‖⟪diskNormalizedHarmonicGradient j, diskH1Gradient u⟫_ℂ‖ ^ 2
  have hb : Summable b :=
    orthonormal_diskNormalizedHarmonicGradient.inner_products_summable (diskH1Gradient u)
  have hpos (m : ℕ) : a ((m + 1 : ℕ) : ℤ) = b (Sum.inl m) := by
    simp only [a, b, Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg (m + 1) : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    exact (norm_sq_diskNormalizedHarmonicGradient_pos m u).symm
  have hneg (m : ℕ) : a (-((m + 1 : ℕ) : ℤ)) = b (Sum.inr m) := by
    simp only [a, b, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (m + 1) : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    exact (norm_sq_diskNormalizedHarmonicGradient_neg m u).symm
  obtain ⟨ha, hsum⟩ := int_tsum_eq_halves a b hb (by simp [a]) hpos hneg
  refine ⟨ha, ?_⟩
  change (∑' n : ℤ, a n) ≤ _
  rw [hsum]
  exact orthonormal_diskNormalizedHarmonicGradient.tsum_inner_products_le (diskH1Gradient u)

theorem diskH1Fourier_norm_sq (u : NeumannH1 (ball (0 : ℂ) 1)) (n : ℤ) :
    ‖diskH1Fourier u n‖ ^ 2 = (2 * π) *
      ‖fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n‖ ^ 2 := by
  rw [diskH1Fourier_apply, norm_mul,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt two_pi_pos.le]

/-- The same physical estimate in average, rather than orthonormal, Fourier coordinates. -/
theorem disk_h1_average_fourier_energy (u : NeumannH1 (ball (0 : ℂ) 1)) :
    Summable (fun n : ℤ => |(n : ℝ)| *
      ‖fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n‖ ^ 2) ∧
      (∑' n : ℤ, |(n : ℝ)| *
        ‖fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n‖ ^ 2) ≤
          ‖diskH1Gradient u‖ ^ 2 / (2 * π) := by
  let a : ℤ → ℝ := fun n => |(n : ℝ)| *
    ‖fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n‖ ^ 2
  let b : ℤ → ℝ := fun n => |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2
  have hb : Summable b := (disk_h1_fourier_energy u).1
  have hrel (n : ℤ) : (2 * π)⁻¹ * b n = a n := by
    dsimp [a, b]
    rw [diskH1Fourier_norm_sq]
    field_simp [two_pi_pos.ne']
  have ha : Summable a := (hb.mul_left ((2 * π)⁻¹)).congr hrel
  refine ⟨ha, ?_⟩
  change (∑' n : ℤ, a n) ≤ _
  calc
    _ = (2 * π)⁻¹ * ∑' n : ℤ, b n := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun n => (hrel n).symm)
    _ ≤ (2 * π)⁻¹ * ‖diskH1Gradient u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (disk_h1_fourier_energy u).2
        (inv_nonneg.mpr two_pi_pos.le)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

private lemma disk_half_weight_norm (u : NeumannH1 (ball (0 : ℂ) 1)) (n : ℤ) :
    ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2 =
      ‖diskH1Fourier u n‖ ^ 2 + |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2 := by
  rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sobWeight_pos n).le]
  unfold sobWeight
  ring

theorem disk_h1_half_trace_summable (u : NeumannH1 (ball (0 : ℂ) 1)) :
    Summable (fun n : ℤ =>
      ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2) :=
  ((summable_norm_sq_L2Z (diskH1Fourier u)).add
    (disk_h1_fourier_energy u).1).congr (fun n => (disk_half_weight_norm u n).symm)

/-- Half-order trace bound in the orthonormal Fourier coordinates. -/
theorem disk_h1_half_trace_bound (u : NeumannH1 (ball (0 : ℂ) 1)) :
    (∑' n : ℤ, ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2) ≤
      ‖diskH1Trace u‖ ^ 2 + ‖diskH1Gradient u‖ ^ 2 := by
  simp_rw [disk_half_weight_norm]
  rw [Summable.tsum_add (summable_norm_sq_L2Z (diskH1Fourier u))
    (disk_h1_fourier_energy u).1, ← norm_sq_L2Z]
  have hnorm : ‖diskH1Fourier u‖ = ‖diskH1Trace u‖ :=
    boundaryFourier.norm_map _
  rw [hnorm]
  exact add_le_add le_rfl (disk_h1_fourier_energy u).2

theorem disk_h1_fourier_isSobolevSeq_half (u : NeumannH1 (ball (0 : ℂ) 1)) :
    IsSobolevSeq (1 / 2 : ℝ) (diskH1Fourier u : ℤ → ℂ) := by
  unfold IsSobolevSeq
  have h := disk_h1_half_trace_summable u
  simp only [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _)] at h
  simpa only [Real.sqrt_eq_rpow] using h

theorem disk_h1_fourier_sobNormSq_half_le (u : NeumannH1 (ball (0 : ℂ) 1)) :
    sobNormSq (1 / 2 : ℝ) (diskH1Fourier u : ℤ → ℂ) ≤
      ‖diskH1Trace u‖ ^ 2 + ‖diskH1Gradient u‖ ^ 2 := by
  unfold sobNormSq
  have h := disk_h1_half_trace_bound u
  simp only [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _)] at h
  simpa only [Real.sqrt_eq_rpow] using h

private lemma disk_average_half_weight (u : NeumannH1 (ball (0 : ℂ) 1)) (n : ℤ) :
    (2 * π)⁻¹ *
      ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2 =
        (sobWeight n ^ (1 / 2 : ℝ) *
          ‖fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n‖) ^ 2 := by
  rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    diskH1Fourier_norm_sq, Real.sq_sqrt (sobWeight_pos n).le]
  rw [← Real.sqrt_eq_rpow, mul_pow, Real.sq_sqrt (sobWeight_pos n).le]
  field_simp [two_pi_pos.ne']

/-- The actual boundary representative belongs to the existing Fourier H¹ᐟ² space. -/
theorem disk_h1_average_fourier_isSobolevSeq_half
    (u : NeumannH1 (ball (0 : ℂ) 1)) :
    IsSobolevSeq (1 / 2 : ℝ)
      (fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ)) :=
  ((disk_h1_half_trace_summable u).mul_left ((2 * π)⁻¹)).congr
    (disk_average_half_weight u)

theorem disk_h1_average_fourier_sobNormSq_half_le
    (u : NeumannH1 (ball (0 : ℂ) 1)) :
    sobNormSq (1 / 2 : ℝ)
      (fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ)) ≤
        (‖diskH1Trace u‖ ^ 2 + ‖diskH1Gradient u‖ ^ 2) / (2 * π) := by
  unfold sobNormSq
  calc
    _ = (2 * π)⁻¹ * (∑' n : ℤ,
        ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2) := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun n => (disk_average_half_weight u n).symm)
    _ ≤ (2 * π)⁻¹ * (‖diskH1Trace u‖ ^ 2 + ‖diskH1Gradient u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (disk_h1_half_trace_bound u)
        (inv_nonneg.mpr two_pi_pos.le)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- The weighted actual Fourier trace, first as a linear map. -/
def diskHalfTraceLin : NeumannH1 (ball (0 : ℂ) 1) →ₗ[ℂ] L2Z where
  toFun u := ⟨fun n => (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n,
    memℓp_two_iff_summable.mpr (disk_h1_half_trace_summable u)⟩
  map_add' u v := by
    apply lp.ext
    funext n
    change (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier (u + v) n =
      (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n +
        (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier v n
    simp only [map_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c u := by
    apply lp.ext
    funext n
    change (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier (c • u) n =
      c * ((Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n)
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem norm_diskHalfTraceLin_le (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ‖diskHalfTraceLin u‖ ≤ Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) * ‖u‖ := by
  have ht : ‖diskH1Trace u‖ ^ 2 ≤ ‖diskH1Trace‖ ^ 2 * ‖u‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (diskH1Trace.le_opNorm u)
  have hs : ‖diskHalfTraceLin u‖ ^ 2 ≤
      (Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) * ‖u‖) ^ 2 := by
    rw [norm_sq_L2Z, mul_pow, Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ‖diskH1Trace u‖ ^ 2 + ‖diskH1Gradient u‖ ^ 2 := disk_h1_half_trace_bound u
      _ ≤ ‖diskH1Trace‖ ^ 2 * ‖u‖ ^ 2 + ‖u‖ ^ 2 :=
        add_le_add ht (norm_sq_diskH1Gradient_le u)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

/-- A bounded actual H¹-to-half-order Fourier trace on the unit disk. -/
def diskHalfTrace : NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  diskHalfTraceLin.mkContinuous (Real.sqrt (‖diskH1Trace‖ ^ 2 + 1))
    norm_diskHalfTraceLin_le

@[simp] theorem diskHalfTrace_apply (u : NeumannH1 (ball (0 : ℂ) 1)) (n : ℤ) :
    diskHalfTrace u n = (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
      boundaryFourier (diskH1Trace u) n := rfl

theorem norm_diskHalfTrace_le (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ‖diskHalfTrace u‖ ≤ Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) * ‖u‖ :=
  norm_diskHalfTraceLin_le u

theorem norm_diskHalfTrace_operator_le :
    ‖diskHalfTrace‖ ≤ Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

end PolyaNeumann

end
