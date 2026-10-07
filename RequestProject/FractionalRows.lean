module

public import RequestProject.FractionalSobolev

/-!
# Fractional regularity for families of rows

Vector-valued form of `FractionalSobolev.lean`. For a continuous `2π`-periodic `r : ℝ → H` and
an orthonormal family `(vⱼ)` in `H`, write `cⱼ(n)` for the Fourier coefficients of
`θ ↦ ⟨r(θ), vⱼ⟩` and `Δ²_h r(θ) = r(θ+2h) - 2 r(θ+h) + r(θ)` (`secondDiff`).

* `secondDiff_integral_le`: if `‖Δ²_h r(θ)‖ ≤ A h²` away from the cut (`θ ≤ 2π - 2h`) and
  `‖Δ²_h r(θ)‖ ≤ B h` everywhere, then `∫₀^{2π} ‖Δ²_h r‖² ≤ (π² A² + 2B²) h³`.
* `summable_rpow_mul_fourierCoeff_rows`: if `∫₀^{2π} ‖Δ²_h r‖² ≤ C h^β` for `0 < h ≤ π/2`,
  then `∑ⱼ ∑ₙ |n|^{2s} |cⱼ(n)|² < ∞` for `0 < 2s < β`.
* `summable_fourierCoeff_rows_three_halves`: under the two pointwise bounds,
  `∑ⱼ ∑ₙ |n|^{2+2δ} |cⱼ(n)|² < ∞` for `0 ≤ δ < 1/2`.

With `H = L²(𝕋)` and the Fourier basis, the last statement is the `H^{1+δ}` estimate in the
first variable for a kernel `k(θ, t)` whose `θ`-derivative is Lipschitz off the cut
(Lemma 6.6); see `summable_kernelCoeff_three_halves`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory
open scoped InnerProductSpace

/-- The second difference `Δ²_h r(θ) = (r(θ+2h) - r(θ+h)) - (r(θ+h) - r(θ))`. -/
def secondDiff {E : Type*} [AddCommGroup E] (r : ℝ → E) (h θ : ℝ) : E :=
  r (θ + 2 * h) - r (θ + h) - (r (θ + h) - r θ)

/-- **Second-difference integral from pointwise bounds.** If `‖Δ²_h r(θ)‖ ≤ A h²` for
`θ ∈ [0, 2π - 2h]` and `‖Δ²_h r(θ)‖ ≤ B h` for all `θ`, then
`∫₀^{2π} ‖Δ²_h r‖² ≤ (π² A² + 2B²) h³` for `0 < h ≤ π/2`. -/
theorem secondDiff_integral_le {E : Type*} [NormedAddCommGroup E] {r : ℝ → E}
    (hr : Continuous r) {A B h : ℝ} (hh : 0 < h) (hh' : h ≤ π / 2)
    (hgood : ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h), ‖secondDiff r h θ‖ ≤ A * h ^ 2)
    (hbad : ∀ θ, ‖secondDiff r h θ‖ ≤ B * h) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖secondDiff r h θ‖ ^ 2 ≤ (π ^ 2 * A ^ 2 + 2 * B ^ 2) * h ^ (3 : ℝ) := by
  set F : ℝ → ℝ := fun θ => ‖secondDiff r h θ‖ ^ 2 with hF
  have hFc : Continuous F := by
    refine (((hr.comp (continuous_id.add continuous_const)).sub (hr.comp (continuous_id.add continuous_const))).sub
      ((hr.comp (continuous_id.add continuous_const)).sub hr)).norm.pow 2
  have hpi : 0 < π := pi_pos
  set a : ℝ := 2 * π - 2 * h with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha2 : a ≤ 2 * π := by rw [ha]; linarith
  have hI1 : ∫ θ in (0 : ℝ)..a, F θ ≤ a * (A * h ^ 2) ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := volume) ha0 (hFc.intervalIntegrable _ _)
      intervalIntegrable_const fun θ hθ => pow_le_pow_left₀ (norm_nonneg _) (hgood θ hθ) 2
    simpa [intervalIntegral.integral_const] using this
  have hI2 : ∫ θ in a..(2 * π), F θ ≤ (2 * π - a) * (B * h) ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := volume) ha2 (hFc.intervalIntegrable _ _)
      intervalIntegrable_const fun θ _ => pow_le_pow_left₀ (norm_nonneg _) (hbad θ) 2
    simpa [intervalIntegral.integral_const] using this
  rw [← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable 0 a)
    (hFc.intervalIntegrable a (2 * π))]
  have h3 : h ^ (3 : ℝ) = h ^ 3 := by exact_mod_cast Real.rpow_natCast h 3
  rw [h3]
  have hA : a * (A * h ^ 2) ^ 2 ≤ π ^ 2 * A ^ 2 * h ^ 3 := by
    have e : a * (A * h ^ 2) ^ 2 = a * h * (A ^ 2 * h ^ 3) := by ring
    have e' : π ^ 2 * A ^ 2 * h ^ 3 = π ^ 2 * (A ^ 2 * h ^ 3) := by ring
    rw [e, e']
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : a * h ≤ 2 * π * (π / 2) := mul_le_mul ha2 hh' hh.le (by positivity)
    nlinarith
  have hB : (2 * π - a) * (B * h) ^ 2 = 2 * B ^ 2 * h ^ 3 := by rw [ha]; ring
  nlinarith

section Rows

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {v : ι → H} (hv : Orthonormal ℂ v) {r : ℝ → H} (hr : Continuous r)
  (hper : Function.Periodic r (2 * π))

include hv hr hper

/-- Bessel–Parseval for second differences of rows:
`∑_{j ∈ J} ∑ₙ |e^{inh} - 1|⁴ |cⱼ(n)|² ≤ (2π)⁻¹ ∫₀^{2π} ‖Δ²_h r‖²`. -/
lemma sum_tsum_secondDiff_le (J : Finset ι) (h : ℝ) :
    ∑ j ∈ J, ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * 2) *
        ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 ≤
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖secondDiff r h θ‖ ^ 2 := by
  have hcont : ∀ j, Continuous fun θ => ⟪r θ, v j⟫_ℂ := fun j => hr.inner continuous_const
  have hperj : ∀ j, Function.Periodic (fun θ => ⟪r θ, v j⟫_ℂ) (2 * π) := fun j θ => by
    simp only [hper θ]
  have hsd : Continuous fun θ => secondDiff r h θ :=
    ((hr.comp (continuous_id.add continuous_const)).sub (hr.comp (continuous_id.add continuous_const))).sub
      ((hr.comp (continuous_id.add continuous_const)).sub hr)
  have hinner : ∀ j θ, ⟪r (θ + 2 * h), v j⟫_ℂ - 2 * ⟪r (θ + h), v j⟫_ℂ + ⟪r θ, v j⟫_ℂ =
      ⟪secondDiff r h θ, v j⟫_ℂ := by
    intro j θ
    simp only [secondDiff, inner_sub_left]
    ring
  simp_rw [fun j => tsum_second_diff_eq_integral (hcont j) (hperj j) h, hinner]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum]
  swap
  · intro j _
    exact (hsd.inner continuous_const).norm.pow 2 |>.intervalIntegrable _ _
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine intervalIntegral.integral_mono_on two_pi_pos.le
    ((continuous_finset_sum _ fun j _ => (hsd.inner continuous_const).norm.pow 2)
      |>.intervalIntegrable _ _) ((hsd.norm.pow 2).intervalIntegrable _ _) fun θ _ => ?_
  calc ∑ j ∈ J, ‖⟪secondDiff r h θ, v j⟫_ℂ‖ ^ 2
      = ∑ j ∈ J, ‖⟪v j, secondDiff r h θ⟫_ℂ‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [norm_inner_symm]
    _ ≤ ‖secondDiff r h θ‖ ^ 2 := hv.sum_inner_products_le _

/-- **Fractional regularity of rows.** If `∫₀^{2π} ‖Δ²_h r‖² ≤ C h^β` for `0 < h ≤ π/2`, then
`∑ⱼ ∑ₙ |n|^{2s} |cⱼ(n)|² < ∞` for `0 < 2s < β`. -/
theorem summable_rpow_mul_fourierCoeff_rows {C β s : ℝ} (hs : 0 < s) (hsβ : 2 * s < β)
    (hdiff : ∀ h : ℝ, 0 < h → h ≤ π / 2 →
      ∫ θ in (0 : ℝ)..(2 * π), ‖secondDiff r h θ‖ ^ 2 ≤ C * h ^ β) :
    Summable fun p : ι × ℤ => |(p.2 : ℝ)| ^ (2 * s) *
      ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := by
  classical
  set c : ι → ℤ → ℂ := fun j n => fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n with hc
  have hcont : ∀ j, Continuous fun θ => ⟪r θ, v j⟫_ℂ := fun j => hr.inner continuous_const
  have hsumj : ∀ j, Summable fun n => ‖c j n‖ ^ 2 := fun j =>
    (hasSum_sq_fourierCoeffOn_of_continuous (hcont j)).summable
  set Cb : ℝ := (2 * π)⁻¹ * C * (π / 2) ^ β with hCb
  set bound : ℝ := |Cb| * 2 ^ (2 * s) * (1 - (2 : ℝ) ^ (2 * s - β))⁻¹ with hbound
  have hfin : ∀ (J : Finset ι) (U : Finset ℤ),
      ∑ n ∈ U, |(n : ℝ)| ^ (2 * s) * ∑ j ∈ J, ‖c j n‖ ^ 2 ≤ bound := by
    intro J U
    set aJ : ℤ → ℝ := fun n => ∑ j ∈ J, ‖c j n‖ ^ 2 with haJ
    have haJ0 : ∀ n, 0 ≤ aJ n := fun n => Finset.sum_nonneg fun j _ => by positivity
    have haJs : Summable aJ := summable_sum fun j _ => hsumj j
    have hblock := fun N hN u hu => block_bound_of_diff_bound haJ0 haJs 2
      (C := (2 * π)⁻¹ * C) (β := β) (fun h h0 h1 => ?_) N hN u hu
    · have := sum_rpow_mul_le_of_block_bound haJ0 hs.le hsβ hblock U
      rwa [Real.zero_rpow (by positivity), zero_mul, zero_add] at this
    · have hw : ∀ j ∈ J, Summable fun n : ℤ =>
          ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * 2) * ‖c j n‖ ^ 2 := by
        intro j _
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
          ((hsumj j).mul_left (2 ^ (2 * 2)))
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ _) (by positivity)
        refine (norm_sub_le _ _).trans ?_
        rw [show (n : ℂ) * h * Complex.I = ((n * h : ℝ) : ℂ) * Complex.I from (by push_cast; ring),
          Complex.norm_exp_ofReal_mul_I]
        norm_num
      simp only [haJ, Finset.mul_sum]
      rw [Summable.tsum_finsetSum hw]
      refine (sum_tsum_secondDiff_le hv hr hper J h).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hdiff h h0 h1) (by positivity)
  refine summable_of_sum_le (c := bound) (fun p => by positivity) fun u => ?_
  set J : Finset ι := u.image Prod.fst
  set U : Finset ℤ := u.image Prod.snd
  calc ∑ p ∈ u, |(p.2 : ℝ)| ^ (2 * s) * ‖c p.1 p.2‖ ^ 2
      ≤ ∑ p ∈ J ×ˢ U, |(p.2 : ℝ)| ^ (2 * s) * ‖c p.1 p.2‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
        rw [Finset.mem_product]
        exact ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    _ = ∑ n ∈ U, |(n : ℝ)| ^ (2 * s) * ∑ j ∈ J, ‖c j n‖ ^ 2 := by
        rw [Finset.sum_product_right]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
    _ ≤ bound := hfin J U

/-- **`H^{1+δ}` regularity of rows** (vector form of the fractional gain in Lemma 6.6). If
`‖Δ²_h r(θ)‖ ≤ A h²` for `θ ∈ [0, 2π - 2h]` and `‖Δ²_h r(θ)‖ ≤ B h` for all `θ`, whenever
`0 < h ≤ π/2`, then `∑ⱼ ∑ₙ |n|^{2+2δ} |cⱼ(n)|² < ∞` for every `0 ≤ δ < 1/2`. -/
theorem summable_fourierCoeff_rows_three_halves {A B : ℝ}
    (hgood : ∀ h : ℝ, 0 < h → h ≤ π / 2 →
      ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h), ‖secondDiff r h θ‖ ≤ A * h ^ 2)
    (hbad : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ, ‖secondDiff r h θ‖ ≤ B * h)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    Summable fun p : ι × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := by
  have h := summable_rpow_mul_fourierCoeff_rows hv hr hper (s := 1 + δ) (β := 3)
    (C := π ^ 2 * A ^ 2 + 2 * B ^ 2) (by linarith) (by linarith) fun h h0 h1 =>
      secondDiff_integral_le hr h0 h1 (hgood h h0 h1) (hbad h h0 h1)
  simpa only [show 2 * (1 + δ) = 2 + 2 * δ by ring] using h

end Rows

end PolyaNeumann
