module

public import RequestProject.FractionalKernel

/-!
# Quantitative fractional estimates and interpolation

Quantitative forms of the fractional estimates of `FractionalRows.lean` and
`FractionalKernel.lean`, used for the continuity in the energy of the `H^{1+δ}` bound in
Lemma 6.6.

* `sum_rpow_mul_fourierCoeff_rows_le`: an explicit bound for the partial sums of
  `∑ⱼ ∑ₙ |n|^{2s} |cⱼ(n)|²` in terms of the constant `C` of the second-difference estimate
  `∫₀^{2π} ‖Δ²_h r‖² ≤ C h^β`; it is linear in `C`.
* `secondDiff_integral_le_interp`: interpolating between the `h³` estimate (from a Lipschitz
  derivative off the cut) and the trivial bound by `sup ‖r‖`, the `L²` norm of second
  differences is at most `X^τ Y^{1-τ} h^{3τ}` with `Y` proportional to `sup ‖r‖²`.
* `kernelCoeff_interp`: for a kernel `k(θ, t)` bounded by `M`, `K`-Lipschitz in `θ` with second
  differences `≤ A h²` off the cut, `∑_{n,m} |m|^{2+2δ} |k_{n m}|² ≤ interpBound A K M δ`, and
  `interpBound A K M δ → 0` as `M → 0` (`tendsto_interpBound`). This is the estimate that turns
  uniform convergence of kernels with uniformly bounded regularity constants into convergence in
  the `H^{1+δ}` seminorm.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory Topology
open scoped InnerProductSpace ComplexConjugate

local instance factTwoPiPosFI : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- `min a b ≤ a^τ b^{1-τ}` for `a, b ≥ 0` and `0 ≤ τ ≤ 1`. -/
lemma min_le_rpow_mul_rpow {a b τ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    min a b ≤ a ^ τ * b ^ (1 - τ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    calc a = a ^ τ * a ^ (1 - τ) := by
          rw [← Real.rpow_add' ha (by norm_num), add_sub_cancel, Real.rpow_one]
      _ ≤ a ^ τ * b ^ (1 - τ) := by
          gcongr
  · rw [min_eq_right h]
    calc b = b ^ τ * b ^ (1 - τ) := by
          rw [← Real.rpow_add' hb (by norm_num), add_sub_cancel, Real.rpow_one]
      _ ≤ a ^ τ * b ^ (1 - τ) := by gcongr

section Rows

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {v : ι → H} (hv : Orthonormal ℂ v) {r : ℝ → H} (hr : Continuous r)
  (hper : Function.Periodic r (2 * π))

include hv hr hper

/-- **Fractional regularity of rows, quantitative form.** If `∫₀^{2π} ‖Δ²_h r‖² ≤ C h^β` for
`0 < h ≤ π/2` and `0 < 2s < β`, every partial sum of `∑ⱼ ∑ₙ |n|^{2s} |cⱼ(n)|²` is at most
`|(2π)⁻¹ C (π/2)^β| 2^{2s} / (1 - 2^{2s-β})`. -/
theorem sum_rpow_mul_fourierCoeff_rows_le {C β s : ℝ} (hs : 0 < s) (hsβ : 2 * s < β)
    (hdiff : ∀ h : ℝ, 0 < h → h ≤ π / 2 →
      ∫ θ in (0 : ℝ)..(2 * π), ‖secondDiff r h θ‖ ^ 2 ≤ C * h ^ β) (u : Finset (ι × ℤ)) :
    ∑ p ∈ u, |(p.2 : ℝ)| ^ (2 * s) *
      ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 ≤
      |(2 * π)⁻¹ * C * (π / 2) ^ β| * 2 ^ (2 * s) * (1 - (2 : ℝ) ^ (2 * s - β))⁻¹ := by
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

omit [InnerProductSpace ℂ H] hv hper in
/-- **Interpolated second-difference bound.** If `‖Δ²_h r(θ)‖ ≤ A h²` for `θ ∈ [0, 2π - 2h]`,
`‖Δ²_h r(θ)‖ ≤ B h` for all `θ` and `‖r‖ ≤ M`, then for `0 ≤ τ ≤ 1` and `0 < h ≤ π/2`,
`∫₀^{2π} ‖Δ²_h r‖² ≤ (π² A² + 2B²)^τ (32 π M²)^{1-τ} h^{3τ}`. -/
theorem secondDiff_integral_le_interp {A B M τ h : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hh : 0 < h) (hh' : h ≤ π / 2)
    (hgood : ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h), ‖secondDiff r h θ‖ ≤ A * h ^ 2)
    (hbad : ∀ θ, ‖secondDiff r h θ‖ ≤ B * h) (hM : ∀ θ, ‖r θ‖ ≤ M) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖secondDiff r h θ‖ ^ 2 ≤
      ((π ^ 2 * A ^ 2 + 2 * B ^ 2) ^ τ * (32 * π * M ^ 2) ^ (1 - τ)) * h ^ (3 * τ) := by
  have hFc : Continuous fun θ => ‖secondDiff r h θ‖ ^ 2 :=
    (((hr.comp (continuous_id.add continuous_const)).sub (hr.comp (continuous_id.add continuous_const))).sub
      ((hr.comp (continuous_id.add continuous_const)).sub hr)).norm.pow 2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h1 := secondDiff_integral_le hr hh hh' hgood hbad
  have h4 : ∀ θ, ‖secondDiff r h θ‖ ≤ 4 * M := by
    intro θ
    unfold secondDiff
    have := hM (θ + 2 * h); have := hM (θ + h); have := hM θ
    have e1 := norm_sub_le (r (θ + 2 * h) - r (θ + h)) (r (θ + h) - r θ)
    have e2 := norm_sub_le (r (θ + 2 * h)) (r (θ + h))
    have e3 := norm_sub_le (r (θ + h)) (r θ)
    linarith
  have h2 : ∫ θ in (0 : ℝ)..(2 * π), ‖secondDiff r h θ‖ ^ 2 ≤ 32 * π * M ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
      (hFc.intervalIntegrable _ _) intervalIntegrable_const
      fun θ _ => pow_le_pow_left₀ (norm_nonneg _) (h4 θ) 2
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
    linarith
  have hX : 0 ≤ π ^ 2 * A ^ 2 + 2 * B ^ 2 := by positivity
  have hm := min_le_rpow_mul_rpow (mul_nonneg hX (by positivity : (0 : ℝ) ≤ h ^ (3 : ℝ)))
    (by positivity : (0 : ℝ) ≤ 32 * π * M ^ 2) hτ0 hτ1
  have e : ((π ^ 2 * A ^ 2 + 2 * B ^ 2) * h ^ (3 : ℝ)) ^ τ * (32 * π * M ^ 2) ^ (1 - τ) =
      ((π ^ 2 * A ^ 2 + 2 * B ^ 2) ^ τ * (32 * π * M ^ 2) ^ (1 - τ)) * h ^ (3 * τ) := by
    rw [Real.mul_rpow hX (by positivity), ← Real.rpow_mul hh.le]
    ring
  rw [← e]
  exact (le_min h1 h2).trans hm

end Rows

/-- The exponent `τ = (5 + 2δ)/6` used for the interpolation: `2 + 2δ < 3τ ≤ 3` for
`0 ≤ δ < 1/2`. -/
def interpExp (δ : ℝ) : ℝ := (5 + 2 * δ) / 6

/-- The explicit `H^{1+δ}` bound of a kernel with second-difference constant `A`, Lipschitz
constant `K` and sup bound `M`. -/
def interpBound (A K M δ : ℝ) : ℝ :=
  |(2 * π)⁻¹ * ((π ^ 2 * A ^ 2 + 2 * (2 * K) ^ 2) ^ interpExp δ *
      (32 * π * M ^ 2) ^ (1 - interpExp δ)) * (π / 2) ^ (3 * interpExp δ)| *
    2 ^ (2 * (1 + δ)) * (1 - (2 : ℝ) ^ (2 * (1 + δ) - 3 * interpExp δ))⁻¹

/-- `interpBound A K M δ → 0` as `M → 0`, for `δ < 1/2`. -/
theorem tendsto_interpBound (A K : ℝ) {δ : ℝ} (hδ' : δ < 1 / 2) :
    Tendsto (fun M => interpBound A K M δ) (𝓝 0) (𝓝 0) := by
  have hτ : 0 < 1 - interpExp δ := by unfold interpExp; linarith
  have hc : Continuous fun M : ℝ => (32 * π * M ^ 2) ^ (1 - interpExp δ) :=
    (continuous_const.mul (continuous_pow 2)).rpow_const fun _ => Or.inr hτ.le
  have hcont : Continuous fun M => interpBound A K M δ := by
    unfold interpBound
    exact (((continuous_const.mul (continuous_const.mul hc)).mul continuous_const).abs.mul
      continuous_const).mul continuous_const
  have := hcont.tendsto 0
  convert this using 2
  unfold interpBound
  rw [show (32 * π * (0 : ℝ) ^ 2) = 0 by ring, Real.zero_rpow hτ.ne']
  simp

section Kernel

variable {k : ℝ → ℝ → ℂ} {M : ℝ} (hmeas : ∀ θ, Measurable (k θ)) (hbd : ∀ θ t, ‖k θ t‖ ≤ M)

include hmeas hbd in
lemma norm_kernelRow_le (θ : ℝ) : ‖kernelRow hmeas hbd θ‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbd 0 0)
  unfold kernelRow
  have h := Lp.norm_le_of_ae_bound (μ := (@AddCircle.haarAddCircle (2 * π) _)) (p := 2)
    (f := MemLp.toLp _ (memLp_liftIco_two_pi (hmeas θ) (hbd θ))) (C := M) hM0 ?_
  · have h1 : measureUnivNNReal (@AddCircle.haarAddCircle (2 * π) _) = 1 := by
      simp [measureUnivNNReal]
    simpa [h1] using h
  · filter_upwards [MemLp.coeFn_toLp (memLp_liftIco_two_pi (hmeas θ) (hbd θ))] with x hx
    rw [hx, liftIco_eq_comp]
    exact hbd θ _

include hmeas hbd in
/-- **Quantitative `H^{1+δ}` bound for kernels.** Let `k(θ, t)` be bounded by `M`, measurable in
`t`, `2π`-periodic and uniformly `K`-Lipschitz in `θ`, with second differences in `θ` at most
`A h²` on `[0, 2π - 2h]`. Then for `0 ≤ δ < 1/2` the double Fourier coefficients satisfy
`∑_{n,m} |m|^{2+2δ} |k_{n m}|² < ∞` and this sum is at most `interpBound A K M δ`. -/
theorem kernelCoeff_interp {K : NNReal} {A : ℝ} (hA : 0 ≤ A)
    (hlip : ∀ θ θ' t, t ∈ Set.Ico 0 (2 * π) → ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|)
    (hper : ∀ θ t, t ∈ Set.Ico 0 (2 * π) → k (θ + 2 * π) t = k θ t)
    (hsecond : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h),
      ∀ t ∈ Set.Ico 0 (2 * π), ‖secondDiff (fun θ => k θ t) h θ‖ ≤ A * h ^ 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    Summable (fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2) ∧
    ∑' p : ℤ × ℤ, |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2 ≤
      interpBound A K M δ := by
  have hL : LipschitzWith K (kernelRow hmeas hbd) := by
    refine LipschitzWith.of_dist_le_mul fun θ θ' => ?_
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_kernelRow_sub_le hmeas hbd hlip θ θ'
  have hbad : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ,
      ‖secondDiff (kernelRow hmeas hbd) h θ‖ ≤ (2 * K) * h := by
    intro h hh _ θ
    have e1 := norm_kernelRow_sub_le hmeas hbd hlip (θ + 2 * h) (θ + h)
    have e2 := norm_kernelRow_sub_le hmeas hbd hlip (θ + h) θ
    rw [show θ + 2 * h - (θ + h) = h by ring, abs_of_pos hh] at e1
    rw [show θ + h - θ = h by ring, abs_of_pos hh] at e2
    unfold secondDiff
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hgood : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h),
      ‖secondDiff (kernelRow hmeas hbd) h θ‖ ≤ A * h ^ 2 := fun h h0 h1 θ hθ =>
    norm_secondDiff_kernelRow_le hmeas hbd (by positivity) (hsecond h h0 h1 θ hθ)
  have hτ0 : 0 ≤ interpExp δ := by unfold interpExp; linarith
  have hτ1 : interpExp δ ≤ 1 := by unfold interpExp; linarith
  have hfin := sum_rpow_mul_fourierCoeff_rows_le (fourierBasis (T := 2 * π)).orthonormal
    hL.continuous (kernelRow_periodic hmeas hbd hper) (s := 1 + δ) (β := 3 * interpExp δ)
    (by linarith) (by unfold interpExp; linarith) fun h h0 h1 =>
      secondDiff_integral_le_interp hL.continuous hτ0 hτ1 h0 h1 (hgood h h0 h1) (hbad h h0 h1)
        (norm_kernelRow_le hmeas hbd)
  simp_rw [inner_kernelRow_fourierBasis, fourierCoeffOn_conj, Complex.norm_conj] at hfin
  set f : ℤ × ℤ → ℝ := fun p => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2 with hf
  set σ : ℤ × ℤ ≃ ℤ × ℤ := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hfσ : ∀ u : Finset (ℤ × ℤ), ∑ p ∈ u, f (σ p) ≤ interpBound A K M δ := by
    intro u
    refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) (hfin u)
    simp [hf, σ, show 2 * (1 + δ) = 2 + 2 * δ by ring]
  have hs : Summable (f ∘ σ) := summable_of_sum_le (fun p => by simp only [Function.comp_apply, hf]; positivity) hfσ
  have hs' : Summable f := (Equiv.summable_iff σ).mp hs
  refine ⟨hs', ?_⟩
  rw [← Equiv.tsum_eq σ]
  exact hs.tsum_le_of_sum_le hfσ

end Kernel

end PolyaNeumann
