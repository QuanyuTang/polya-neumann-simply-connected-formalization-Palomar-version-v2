module

public import RequestProject.SobolevCircle
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fourier coefficients of Lipschitz rows (the Hilbert–Schmidt estimate of Lemma 6.3)

Let `r : ℝ → H` be a `2π`-periodic `K`-Lipschitz map into a complex inner product space and
`(vⱼ)` an orthonormal family. For the scalar functions `φⱼ(θ) = ⟨r(θ), vⱼ⟩` with Fourier
coefficients `cⱼ(n)` on `[0, 2π]`,

  `∑ⱼ ∑ₙ n² |cⱼ(n)|² ≤ π² K² / 4`     (`sum_sq_mul_fourierCoeff_le`, `summable_sq_mul_fourierCoeff`).

This is the Hilbert–Schmidt bound into `H¹(𝕋)` used in Lemma 6.3 (periodic projected observation)
for the row `r(θ) = Π^c_E W_E(θ)^* e₀`. The proof uses difference quotients instead of
derivatives: by Parseval, `∑ₙ |e^{inh} - 1|² |cⱼ(n)|² = (2π)⁻¹ ∫ |φⱼ(θ+h) - φⱼ(θ)|²`, the Bessel
inequality sums this over `j` to at most `K² h²`, and `|e^{inh} - 1| ≥ 2|nh|/π` for `|nh| ≤ π`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory
open scoped InnerProductSpace

/-- Fourier coefficients of a shifted periodic function. -/
lemma fourierCoeffOn_comp_add {φ : ℝ → ℂ} (hper : Function.Periodic φ (2 * π)) (h : ℝ)
    (n : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => φ (θ + h)) n =
      Complex.exp (n * h * Complex.I) * fourierCoeffOn two_pi_pos φ n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  set F : ℝ → ℂ := fun u => (fourier (-n) (u : AddCircle (2 * π - 0))) • φ u with hF
  have hFper : Function.Periodic F (2 * π) := by
    intro u
    show (fourier (-n) (((u + 2 * π : ℝ)) : AddCircle (2 * π - 0))) • φ (u + 2 * π) =
      (fourier (-n) ((u : ℝ) : AddCircle (2 * π - 0))) • φ u
    have : ((u + 2 * π : ℝ) : AddCircle (2 * π - 0)) = ((u + (2 * π - 0) : ℝ) : AddCircle _) := by
      rw [sub_zero]
    rw [this, AddCircle.coe_add_period, hper u]
  have hpt : ∀ θ : ℝ, (fourier (-n) (θ : AddCircle (2 * π - 0))) • φ (θ + h) =
      Complex.exp (n * h * Complex.I) * F (θ + h) := by
    intro θ
    simp only [hF, fourier_coe_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    push_cast
    field_simp
    ring
  have hcongr : ∫ x in (0 : ℝ)..(2 * π), (fourier (-n) (x : AddCircle (2 * π - 0))) • φ (x + h) =
      ∫ x in (0 : ℝ)..(2 * π), Complex.exp (n * h * Complex.I) * F (x + h) :=
    intervalIntegral.integral_congr fun θ _ => hpt θ
  rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right]
  have := hFper.intervalIntegral_add_eq h 0
  rw [zero_add, add_comm h (2 * π)] at this
  rw [zero_add, this]
  simp only [Complex.real_smul]
  ring

/-- Fourier coefficients on `[0, 2π]` are additive for continuous functions. -/
lemma fourierCoeffOn_sub_of_continuous {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (n : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => f θ - g θ) n =
      fourierCoeffOn two_pi_pos f n - fourierCoeffOn two_pi_pos g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    ← smul_sub, ← intervalIntegral.integral_sub]
  · simp_rw [smul_sub]
  · exact (((map_continuous (fourier (-n))).comp continuous_quotient_mk').smul
      hf).intervalIntegrable _ _
  · exact (((map_continuous (fourier (-n))).comp continuous_quotient_mk').smul
      hg).intervalIntegrable _ _

/-- Parseval's identity on `[0, 2π]` for continuous functions. -/
lemma hasSum_sq_fourierCoeffOn_of_continuous {φ : ℝ → ℂ} (hφ : Continuous φ) :
    HasSum (fun n => ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖φ θ‖ ^ 2) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hmem : MemLp φ 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
    refine MemLp.of_bound hφ.aestronglyMeasurable C ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Set.Ioc_subset_Icc_self hx)
  have := hasSum_sq_fourierCoeffOn two_pi_pos hmem
  simpa [smul_eq_mul] using this

/-- `|e^{ix} - 1|² ≥ 4x²/π²` for `|x| ≤ π`. -/
lemma sq_le_norm_exp_sub_one_sq {x : ℝ} (hx : |x| ≤ π) :
    4 / π ^ 2 * x ^ 2 ≤ ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 := by
  have hnorm : ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 = 4 * Real.sin (|x| / 2) ^ 2 := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.mul_im, Complex.one_im]
    have h1 : Real.sin (|x| / 2) ^ 2 = Real.sin (x / 2) ^ 2 := by
      rcases abs_choice x with h | h
      · rw [h]
      · rw [h, neg_div, Real.sin_neg, neg_sq]
    rw [h1]
    have h2 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      have := Real.cos_two_mul (x / 2)
      rw [show 2 * (x / 2) = x by ring] at this
      nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    have h4 := Real.sin_sq_add_cos_sq x
    nlinarith [h2, h4]
  rw [hnorm]
  have hpos : 0 ≤ |x| / 2 := by positivity
  have hle : |x| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin hpos hle
  have hs0 : 0 ≤ 2 / π * (|x| / 2) := by positivity
  have : (2 / π * (|x| / 2)) ^ 2 ≤ Real.sin (|x| / 2) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hpi : 0 < π := pi_pos
  rw [hx2]
  calc 4 / π ^ 2 * |x| ^ 2 = 4 * (2 / π * (|x| / 2)) ^ 2 := by field_simp
    _ ≤ 4 * Real.sin (|x| / 2) ^ 2 := by linarith

section Rows

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {v : ι → H} (hv : Orthonormal ℂ v) {r : ℝ → H} {K : NNReal} (hr : LipschitzWith K r)
  (hper : Function.Periodic r (2 * π))
include hv hr hper

/-- The difference-quotient estimate: `∑ⱼ ∑ₙ |e^{inh} - 1|² |cⱼ(n)|² ≤ K² h²` over finite sets
of indices `j`. -/
lemma sum_tsum_diff_le (J : Finset ι) (h : ℝ) :
    ∑ j ∈ J, ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 *
        ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 ≤ K ^ 2 * h ^ 2 := by
  have hcont : ∀ j, Continuous fun θ => ⟪r θ, v j⟫_ℂ := fun j =>
    hr.continuous.inner continuous_const
  have hperj : ∀ j, Function.Periodic (fun θ => ⟪r θ, v j⟫_ℂ) (2 * π) := fun j θ => by
    simp only [hper θ]
  -- coefficients of the difference
  have hcoef : ∀ j n, fourierCoeffOn two_pi_pos (fun θ => ⟪r (θ + h) - r θ, v j⟫_ℂ) n =
      (Complex.exp (n * h * Complex.I) - 1) *
        fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n := by
    intro j n
    simp_rw [inner_sub_left]
    have h1 := fourierCoeffOn_sub_of_continuous (f := fun θ => ⟪r (θ + h), v j⟫_ℂ)
      (g := fun θ => ⟪r θ, v j⟫_ℂ) ((hcont j).comp ((continuous_id.add continuous_const : Continuous fun x => x + h))) (hcont j) n
    have h2 := fourierCoeffOn_comp_add (hperj j) h n
    try simp only at h2
    rw [h1, h2]
    ring
  have hterm : ∀ j, ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 *
        ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2 := by
    intro j
    have hc : Continuous fun θ => ⟪r (θ + h) - r θ, v j⟫_ℂ :=
      ((hr.continuous.comp ((continuous_id.add continuous_const : Continuous fun x => x + h))).sub hr.continuous).inner continuous_const
    rw [← (hasSum_sq_fourierCoeffOn_of_continuous hc).tsum_eq]
    congr 1
    funext n
    rw [hcoef, norm_mul, mul_pow]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum]
  swap
  · intro j _
    exact (((hr.continuous.comp ((continuous_id.add continuous_const : Continuous fun x => x + h))).sub hr.continuous).inner
      continuous_const).norm.pow 2 |>.intervalIntegrable _ _
  have hbound : ∀ θ, ∑ j ∈ J, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2 ≤ K ^ 2 * h ^ 2 := by
    intro θ
    have hb := hv.sum_inner_products_le (r (θ + h) - r θ) (s := J)
    have hl : ‖r (θ + h) - r θ‖ ≤ K * |h| := by
      have := hr.dist_le_mul (θ + h) θ
      rw [dist_eq_norm, Real.dist_eq] at this
      simpa using this
    calc ∑ j ∈ J, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2
        = ∑ j ∈ J, ‖⟪v j, r (θ + h) - r θ⟫_ℂ‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_inner_symm]
      _ ≤ ‖r (θ + h) - r θ‖ ^ 2 := hb
      _ ≤ (K * |h|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hl 2
      _ = K ^ 2 * h ^ 2 := by rw [mul_pow, sq_abs]
  have hint : ∫ θ in (0 : ℝ)..(2 * π), ∑ j ∈ J, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2 ≤
      ∫ θ in (0 : ℝ)..(2 * π), (K : ℝ) ^ 2 * h ^ 2 := by
    refine intervalIntegral.integral_mono_on two_pi_pos.le ?_ intervalIntegrable_const
      fun θ _ => hbound θ
    refine (continuous_finset_sum _ fun j _ => ?_).intervalIntegrable _ _
    exact (((hr.continuous.comp ((continuous_id.add continuous_const : Continuous fun x => x + h))).sub hr.continuous).inner
      continuous_const).norm.pow 2
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  have hpi : 0 < 2 * π := two_pi_pos
  calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ∑ j ∈ J, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2
      ≤ (2 * π)⁻¹ * (2 * π * (K ^ 2 * h ^ 2)) := by gcongr
    _ = K ^ 2 * h ^ 2 := by field_simp

/-- Finite form of the `H¹` Hilbert–Schmidt estimate. -/
lemma sum_sq_mul_fourierCoeff_le_of_finite (J : Finset ι) (N : ℕ) :
    ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        (n : ℝ) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 ≤
      π ^ 2 * K ^ 2 / 4 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton, Int.cast_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      Finset.sum_const_zero]
    positivity
  set h : ℝ := π / N with hh
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hhpos : 0 < h := div_pos pi_pos hNpos
  set c : ι → ℤ → ℂ := fun j n => fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n
  have hsumm : ∀ j, Summable fun n : ℤ =>
      ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2 := by
    intro j
    have hc : Continuous fun θ => ⟪r θ, v j⟫_ℂ := hr.continuous.inner continuous_const
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hasSum_sq_fourierCoeffOn_of_continuous hc).summable.mul_left 4)
    have : ‖Complex.exp (n * h * Complex.I) - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [show (n : ℂ) * h * Complex.I = ((n * h : ℝ) : ℂ) * Complex.I from (by push_cast; ring),
        Complex.norm_exp_ofReal_mul_I]
      norm_num
    have h2 : ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 ≤ 4 := by
      have h0 := norm_nonneg (Complex.exp (n * h * Complex.I) - 1)
      nlinarith
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hpt : ∀ j, ∀ n ∈ Finset.Icc (-(N : ℤ)) N, (n : ℝ) ^ 2 * ‖c j n‖ ^ 2 ≤
      π ^ 2 / (4 * h ^ 2) * (‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2) := by
    intro j n hn
    rw [Finset.mem_Icc] at hn
    have habs : |(n : ℝ) * h| ≤ π := by
      rw [abs_mul, abs_of_pos hhpos, hh]
      have : |(n : ℝ)| ≤ N := by
        rw [abs_le]; exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
      calc |(n : ℝ)| * (π / N) ≤ N * (π / N) := by gcongr
        _ = π := by field_simp
    have hk := sq_le_norm_exp_sub_one_sq habs
    have heq : ((n * h : ℝ) : ℂ) * Complex.I = (n : ℂ) * h * Complex.I := by push_cast; ring
    rw [heq] at hk
    have hpi : 0 < π := pi_pos
    have key : (n : ℝ) ^ 2 ≤ π ^ 2 / (4 * h ^ 2) * ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 4 / π ^ 2 * ((n : ℝ) * h) ^ 2 * π ^ 2 = 4 * h ^ 2 * (n : ℝ) ^ 2 := by
        field_simp
      nlinarith
    calc (n : ℝ) ^ 2 * ‖c j n‖ ^ 2 ≤
        (π ^ 2 / (4 * h ^ 2) * ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2) * ‖c j n‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  calc ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (n : ℝ) ^ 2 * ‖c j n‖ ^ 2
      ≤ ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          π ^ 2 / (4 * h ^ 2) * (‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun n hn => hpt j n hn
    _ = π ^ 2 / (4 * h ^ 2) * ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ ≤ π ^ 2 / (4 * h ^ 2) * ∑ j ∈ J, ∑' n : ℤ,
          ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2 := by
        gcongr with j hj
        exact (hsumm j).sum_le_tsum _ fun n _ => by positivity
    _ ≤ π ^ 2 / (4 * h ^ 2) * (K ^ 2 * h ^ 2) := by
        gcongr
        exact sum_tsum_diff_le hv hr hper J h
    _ = π ^ 2 * K ^ 2 / 4 := by field_simp

/-- **`H¹` Hilbert–Schmidt estimate for Lipschitz rows.** For a `2π`-periodic `K`-Lipschitz
`r : ℝ → H` and an orthonormal family `(vⱼ)`, the Fourier coefficients `cⱼ(n)` of
`θ ↦ ⟨r(θ), vⱼ⟩` satisfy `∑ⱼ ∑ₙ n² |cⱼ(n)|² < ∞`, with sum at most `π² K² / 4`. -/
theorem summable_sq_mul_fourierCoeff :
    Summable fun p : ι × ℤ =>
      ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := by
  classical
  refine summable_of_sum_le (c := π ^ 2 * K ^ 2 / 4) (fun p => by positivity) fun u => ?_
  set J : Finset ι := u.image Prod.fst
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ∈ u, p.2 ∈ Finset.Icc (-(N : ℤ)) N := by
    refine ⟨(u.image fun p => p.2.natAbs).sup id, fun p hp => ?_⟩
    have : p.2.natAbs ≤ (u.image fun p => p.2.natAbs).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hp)
    rw [Finset.mem_Icc]
    constructor <;> omega
  calc ∑ p ∈ u, ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2
      ≤ ∑ p ∈ J ×ˢ Finset.Icc (-(N : ℤ)) N,
          ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
        rw [Finset.mem_product]
        exact ⟨Finset.mem_image_of_mem _ hp, hN p hp⟩
    _ = ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          (n : ℝ) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 :=
        Finset.sum_product _ _ _
    _ ≤ π ^ 2 * K ^ 2 / 4 := sum_sq_mul_fourierCoeff_le_of_finite hv hr hper J N

/-- The value bound: `∑ⱼ ∑ₙ n² |cⱼ(n)|² ≤ π² K² / 4`. -/
theorem tsum_sq_mul_fourierCoeff_le :
    ∑' p : ι × ℤ,
      ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 ≤
      π ^ 2 * K ^ 2 / 4 := by
  classical
  refine (summable_sq_mul_fourierCoeff hv hr hper).tsum_le_of_sum_le fun u => ?_
  set J : Finset ι := u.image Prod.fst
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ∈ u, p.2 ∈ Finset.Icc (-(N : ℤ)) N := by
    refine ⟨(u.image fun p => p.2.natAbs).sup id, fun p hp => ?_⟩
    have : p.2.natAbs ≤ (u.image fun p => p.2.natAbs).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hp)
    rw [Finset.mem_Icc]
    constructor <;> omega
  calc ∑ p ∈ u, ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2
      ≤ ∑ p ∈ J ×ˢ Finset.Icc (-(N : ℤ)) N,
          ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
        rw [Finset.mem_product]
        exact ⟨Finset.mem_image_of_mem _ hp, hN p hp⟩
    _ = ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          (n : ℝ) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 :=
        Finset.sum_product _ _ _
    _ ≤ π ^ 2 * K ^ 2 / 4 := sum_sq_mul_fourierCoeff_le_of_finite hv hr hper J N

end Rows

end PolyaNeumann
