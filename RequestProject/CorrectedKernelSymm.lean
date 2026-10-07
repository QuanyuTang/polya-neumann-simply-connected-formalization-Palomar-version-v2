module

public import RequestProject.CorrectedKernelSmooth
public import RequestProject.MatrixHS

/-!
# Hermitian symmetry of the corrected kernel (Lemma 6.6, second variable)

The operator `i(T_E - T_E^*) + O_E B_E O_E^*` is self-adjoint, and so is `2D^{-1}`; accordingly
the corrected kernel is Hermitian:

  `r_E(θ, t) = conj (r_E(t, θ))`  (`correctedKernel_conj_symm`),

because `w_E(θ, t) = conj (w_E(t, θ))` and `B_E` is self-adjoint (Lemma 6.3). For a bounded,
jointly measurable Hermitian kernel on `[0, L]²` the double Fourier coefficients satisfy
`k_{n m} = conj (k_{-m, -n})` (`doubleCoeff_conj_symm`, by Fubini). Hence the fractional
gain of `summable_rpow_mul_correctedKernelCoeff` in the first variable transfers to the second
variable (`summable_rpow_mul_correctedKernelCoeff_snd`), as in the paper:

  `∑_{n, m} |n|^{2+2δ} |r_{n m}|² < ∞`  for `0 ≤ δ < 1/2`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

/-- **Fubini for a Hermitian kernel.** For a bounded, jointly measurable kernel on `[0, 2π]²`
with `k(θ, t) = conj (k(t, θ))`, the double Fourier integrals satisfy
`∫∫ e_{-m}(θ) e_{-n}(t) k(θ, t) = conj (∫∫ e_n(θ) e_m(t) k(θ, t))`. -/
lemma doubleIntegral_conj_symm {k : ℝ → ℝ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry k)
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))))
    (hb : ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π), ‖k θ t‖ ≤ C)
    (hs : ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π), k θ t = conj (k t θ)) (n m : ℤ) :
    ∫ θ in Ioc 0 (2 * π), fourier (-m) (θ : AddCircle (2 * π - 0)) *
        ∫ t in Ioc 0 (2 * π), fourier (-n) (t : AddCircle (2 * π - 0)) * k θ t =
      conj (∫ θ in Ioc 0 (2 * π), fourier n (θ : AddCircle (2 * π - 0)) *
        ∫ t in Ioc 0 (2 * π), fourier m (t : AddCircle (2 * π - 0)) * k θ t) := by
  simp only [← integral_const_mul]
  set μ := volume.restrict (Ioc (0:ℝ) (2 * π))
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩; simp [μ]; exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
  set e : ℤ → ℝ → ℂ := fun j x => fourier j (x : AddCircle (2 * π - 0)) with he
  have hec : ∀ j, Continuous (e j) := fun j => (map_continuous (fourier j)).comp
    (AddCircle.continuous_mk' _)
  have hen : ∀ j x, ‖e j x‖ = 1 := fun j x => by
    simp only [he]; rw [fourier_apply]; exact Circle.norm_coe _
  have hconj : ∀ j x, conj (e j x) = e (-j) x := fun j x => by simp only [he, fourier_neg]
  have hae : ∀ᵐ p ∂(μ.prod μ), p ∈ Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π) := by
    simp only [μ]; rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hmS : AEStronglyMeasurable (fun p : ℝ × ℝ => k p.2 p.1) (μ.prod μ) :=
    hm.comp_measurePreserving (Measure.measurePreserving_swap)
  have hint : Integrable (Function.uncurry fun θ t =>
      e (-m) θ * (e (-n) t * conj (k t θ))) (μ.prod μ) := by
    refine Integrable.of_bound (C := C) ?_ ?_
    · exact ((hec _).comp continuous_fst).aestronglyMeasurable.mul
        (((hec _).comp continuous_snd).aestronglyMeasurable.mul
          (Complex.continuous_conj.comp_aestronglyMeasurable hmS))
    · filter_upwards [hae] with p hp
      simp only [Function.uncurry, norm_mul, hen, Complex.norm_conj, one_mul]
      exact hb _ (Ioc_subset_Icc_self hp.2) _ (Ioc_subset_Icc_self hp.1)
  have h1 : ∫ θ, ∫ t, e (-m) θ * (e (-n) t * k θ t) ∂μ ∂μ =
      ∫ θ, ∫ t, e (-m) θ * (e (-n) t * conj (k t θ)) ∂μ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hs θ (Ioc_subset_Icc_self hθ) t (Ioc_subset_Icc_self ht)]
  change ∫ θ, ∫ t, e (-m) θ * (e (-n) t * k θ t) ∂μ ∂μ =
    conj (∫ θ, ∫ t, e n θ * (e m t * k θ t) ∂μ ∂μ)
  rw [h1, integral_integral_swap hint, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  dsimp only
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [map_mul, hconj]
  ring

/-- **Double Fourier coefficients of a Hermitian kernel.** For a bounded, jointly measurable
kernel on `[0, 2π]²` with `k(θ, t) = conj (k(t, θ))`, the coefficient `k_{n m}` (frequency `n`
in `t`, `m` in `θ`) is `conj (k_{-m, -n})`. -/
theorem doubleCoeff_conj_symm {k : ℝ → ℝ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry k)
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))))
    (hb : ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π), ‖k θ t‖ ≤ C)
    (hs : ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π), k θ t = conj (k t θ)) (n m : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) n) m =
      conj (fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) (-m)) (-n)) := by
  simp only [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le two_pi_pos.le,
    smul_eq_mul, neg_neg, Complex.real_smul]
  set c : ℂ := ((1 / (2 * π - 0) : ℝ) : ℂ)
  simp only [mul_left_comm _ c, integral_const_mul]
  rw [doubleIntegral_conj_symm hm hb hs n m]
  simp only [map_mul, c, Complex.conj_ofReal]

variable {γ : ℝ → ℂ} {K K' : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

/-- `B_E` is self-adjoint (Lemma 6.3), with no assumption on `c_E`. -/
lemma cutBE_isSelfAdjoint (hK : LipschitzWith K γ) (hW : IsTransport γ E W) :
    IsSelfAdjoint (cutBE W) :=
  cutB_isSelfAdjoint (inner_cutD_cutC (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩) _)

/-- **Hermitian symmetry of the corrected kernel:** `r_E(θ, t) = conj (r_E(t, θ))`. -/
theorem correctedKernel_conj_symm (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (θ t : ℝ) : correctedKernel W θ t = conj (correctedKernel W t θ) := by
  have hB := cutBE_isSelfAdjoint hK hW
  have hw : volterraKernel W θ t = conj (volterraKernel W t θ) := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.adjoint_adjoint]
  have hb : ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W t) (basisVec 0)))⟫_ℂ =
      conj ⟪basisVec 0, W t (cutBE W (ContinuousLinearMap.adjoint (W θ) (basisVec 0)))⟫_ℂ := by
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.adjoint_inner_left (cutBE W), hB.adjoint_eq,
      ContinuousLinearMap.adjoint_inner_right]
  have hsign : Real.sign (θ - t) = -Real.sign (t - θ) := by
    rw [← Real.sign_neg, neg_sub]
  simp only [correctedKernel, map_add, map_mul, map_sub, Complex.conj_I, Complex.conj_ofReal,
    map_div₀, map_one, hw, hb, hsign, Complex.ofReal_neg]
  ring

/-- Joint measurability of the corrected kernel on `[0, L]²`. -/
lemma aestronglyMeasurable_correctedKernel (hW : IsTransport γ E W) :
    AEStronglyMeasurable (Function.uncurry (correctedKernel W))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  have hWc : Continuous fun t => W (clampTwoPi t) :=
    hW.1.comp_continuous continuous_clampTwoPi clampTwoPi_mem
  have hx : Continuous fun t => ContinuousLinearMap.adjoint (W (clampTwoPi t)) (basisVec 0) :=
    ((ContinuousLinearMap.adjoint.toLinearIsometry.continuous.comp hWc).clm_apply
      continuous_const)
  have hmeas : Measurable fun p : ℝ × ℝ =>
      correctedKernel W (clampTwoPi p.1) (clampTwoPi p.2) := by
    have h1 : Measurable fun p : ℝ × ℝ =>
        (Real.sign (clampTwoPi p.1 - clampTwoPi p.2) : ℂ) :=
      Complex.measurable_ofReal.comp (measurable_real_sign.comp
        ((continuous_clampTwoPi.comp continuous_fst).sub
          (continuous_clampTwoPi.comp continuous_snd)).measurable)
    have h2 : Continuous fun p : ℝ × ℝ =>
        volterraKernel W (clampTwoPi p.1) (clampTwoPi p.2) := by
      unfold volterraKernel
      exact continuous_const.inner ((hWc.comp continuous_fst).clm_apply (hx.comp continuous_snd))
    have h3 : Continuous fun p : ℝ × ℝ => ⟪basisVec 0, W (clampTwoPi p.1) (cutBE W
        (ContinuousLinearMap.adjoint (W (clampTwoPi p.2)) (basisVec 0)))⟫_ℂ :=
      continuous_const.inner ((hWc.comp continuous_fst).clm_apply
        ((cutBE W).continuous.comp (hx.comp continuous_snd)))
    have h4 : Continuous fun p : ℝ × ℝ =>
        Complex.I * (((clampTwoPi p.1 : ℂ) - (clampTwoPi p.2 : ℂ)) / (π : ℂ)) :=
      continuous_const.mul (((Complex.continuous_ofReal.comp
        (continuous_clampTwoPi.comp continuous_fst)).sub
        (Complex.continuous_ofReal.comp (continuous_clampTwoPi.comp continuous_snd))).div_const _)
    unfold correctedKernel
    exact ((measurable_const.mul h1).mul (h2.measurable.sub measurable_const)).add
      h4.measurable |>.add h3.measurable
  refine hmeas.aestronglyMeasurable.congr ?_
  have hae : ∀ᵐ p ∂((volume.restrict (Ioc (0:ℝ) (2 * π))).prod
      (volume.restrict (Ioc (0:ℝ) (2 * π)))), p ∈ Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π) := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  filter_upwards [hae] with p hp
  simp only [Function.uncurry]
  rw [clampTwoPi_of_mem (Ioc_subset_Icc_self hp.1), clampTwoPi_of_mem (Ioc_subset_Icc_self hp.2)]

/-- The double Fourier coefficients of the corrected kernel satisfy `r_{n m} = conj (r_{-m,-n})`. -/
theorem correctedKernelCoeff_conj_symm (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (n m : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) n) m =
      conj (fourierCoeffOn two_pi_pos
        (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) (-m)) (-n)) :=
  doubleCoeff_conj_symm (aestronglyMeasurable_correctedKernel hW)
    (fun _ hθ _ ht => norm_correctedKernel_le hK hW hθ ht)
    (fun θ _ t _ => correctedKernel_conj_symm hK hW θ t) n m

/-- **Lemma 6.6 (fractional gain, second variable).** For a curve with Lipschitz `γ'` on
`[0, L]` and `c_E ≠ 0`, `∑_{n, m} |n|^{2+2δ} |r_{n m}|² < ∞` for `0 ≤ δ < 1/2`, where `n` is the
frequency in the second variable `t`. -/
theorem summable_rpow_mul_correctedKernelCoeff_snd (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ' : δ < 1 / 2) :
    Summable fun p : ℤ × ℤ => |(p.1 : ℝ)| ^ (2 + 2 * δ) * ‖fourierCoeffOn two_pi_pos
      (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) p.1) p.2‖ ^ 2 := by
  have h := summable_rpow_mul_correctedKernelCoeff hK hγ' hW hc hδ hδ'
  let σ : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (-p.2, -p.1)
      invFun := fun p => (-p.2, -p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  refine ((σ.summable_iff).mpr h).congr fun p => ?_
  simp only [Function.comp_apply, σ, Equiv.coe_fn_mk, Int.cast_neg, abs_neg]
  congr 2
  rw [correctedKernelCoeff_conj_symm hK hW p.1 p.2, Complex.norm_conj]

/-- **Mixed weights from isotropic ones.** If `∑ |n|^s a_{n m}` and `∑ |m|^s a_{n m}` converge
(`a ≥ 0`), then so does `∑ (1 + |m|)^α (1 + |n|)^β a_{n m}` whenever `α, β ≥ 0`, `α + β = s`. -/
lemma summable_mixed_weight {a : ℤ × ℤ → ℝ} (ha : ∀ p, 0 ≤ a p) {s α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = s)
    (h1 : Summable fun p : ℤ × ℤ => |(p.1 : ℝ)| ^ s * a p)
    (h2 : Summable fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ s * a p) :
    Summable fun p : ℤ × ℤ => (1 + |(p.2 : ℝ)|) ^ α * (1 + |(p.1 : ℝ)|) ^ β * a p := by
  have hs : 0 ≤ s := hαβ ▸ add_nonneg hα hβ
  have h0 : Summable fun p : ℤ × ℤ => if p = 0 then a p else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun p hp => by simp_all
  refine Summable.of_nonneg_of_le (fun p => mul_nonneg (by positivity) (ha p)) (fun p => ?_)
    (((h1.add h2).add h0).mul_left (2 ^ s))
  set x := |(p.1 : ℝ)| with hxdef
  set y := |(p.2 : ℝ)| with hydef
  have hx : 0 ≤ x := abs_nonneg _
  have hy : 0 ≤ y := abs_nonneg _
  set M := max x y
  have hM : 0 ≤ M := le_max_of_le_left hx
  have hw : (1 + y) ^ α * (1 + x) ^ β ≤ (1 + M) ^ s := by
    rw [← hαβ, Real.rpow_add (by positivity)]
    gcongr
    · exact le_max_right _ _
    · exact le_max_left _ _
  have hM1 : (1 + M) ^ s ≤ 2 ^ s * (max 1 M) ^ s := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    gcongr
    linarith [le_max_left 1 M, le_max_right 1 M]
  have hint : ∀ n : ℤ, |(n : ℝ)| < 1 → n = 0 := fun n hn => by
    rw [← Int.cast_abs] at hn
    have : |n| < 1 := by exact_mod_cast hn
    exact Int.abs_lt_one_iff.mp this
  have hcase : (max 1 M) ^ s ≤ x ^ s + y ^ s + if p = 0 then 1 else 0 := by
    by_cases hp : p = 0
    · subst hp
      simp only [x, y, M, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, abs_zero, max_self,
        if_true]
      rw [max_eq_left zero_le_one, Real.one_rpow]
      have := Real.rpow_nonneg (le_refl (0:ℝ)) s
      linarith
    · rw [if_neg hp, add_zero]
      have h1M : 1 ≤ M := by
        by_contra hlt
        push_neg at hlt
        exact hp (Prod.ext (hint _ (lt_of_le_of_lt (le_max_left _ _) hlt))
          (hint _ (lt_of_le_of_lt (le_max_right _ _) hlt)))
      rw [max_eq_right h1M]
      rcases le_total x y with h | h
      · rw [show M = y from max_eq_right h]
        linarith [Real.rpow_nonneg hx s]
      · rw [show M = x from max_eq_left h]
        linarith [Real.rpow_nonneg hy s]
  calc (1 + y) ^ α * (1 + x) ^ β * a p ≤ 2 ^ s * (max 1 M) ^ s * a p :=
        mul_le_mul_of_nonneg_right (hw.trans hM1) (ha p)
    _ ≤ 2 ^ s * (x ^ s + y ^ s + if p = 0 then 1 else 0) * a p := by
        gcongr
        exact ha p
    _ = 2 ^ s * (x ^ s * a p + y ^ s * a p + if p = 0 then a p else 0) := by
        split_ifs <;> ring

/-- **Weighted Hilbert–Schmidt bound for the corrected kernel** (proof of Lemma 6.7). With
`λ_n = 1 + |n|`, for `0 ≤ t ≤ 1/2` and `0 ≤ δ < 1/2`,
`∑_{n, m} λ_m^{1+2t+2δ} λ_n^{1-2t} |r_{n m}|² < ∞` (`m` the frequency in `θ`, `n` in `t`):
the normalized remainder is Hilbert–Schmidt from `H^t` to `H^{t+δ}`. -/
theorem summable_mixed_correctedKernelCoeff (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {δ s : ℝ} (hδ : 0 ≤ δ)
    (hδ' : δ < 1 / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Summable fun p : ℤ × ℤ => (1 + |(p.2 : ℝ)|) ^ (1 + 2 * s + 2 * δ) *
      (1 + |(p.1 : ℝ)|) ^ (1 - 2 * s) * ‖fourierCoeffOn two_pi_pos
        (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) p.1) p.2‖ ^ 2 :=
  summable_mixed_weight (fun _ => by positivity) (by linarith) (by linarith) (by ring)
    (summable_rpow_mul_correctedKernelCoeff_snd hK hγ' hW hc hδ hδ')
    (summable_rpow_mul_correctedKernelCoeff hK hγ' hW hc hδ hδ')

/-- The Fourier matrix of the normalized corrected-kernel remainder
`Λ^{t+δ} (Λ^{1/2} R_E Λ^{1/2}) Λ^{-t}` on `ℓ²(ℤ)`: its `(m, n)` entry is
`λ_m^{1/2+t+δ} λ_n^{1/2-t} r̂_E(m, n)` with `r̂_E(m, n) = 2π · (r_E)_{-n, m}`. Unfolding the Fourier
coefficients, `r̂_E(m, n) = ⟨φ_m, R_E φ_n⟩` is the matrix of the integral operator
`(R_E g)(θ) = ∫₀^L r_E(θ, s) g(s) ds` in the orthonormal Fourier basis `φ_n = e^{in·}/√(2π)`. -/
def correctedRemainderMatrix (W : ℝ → Ell2 →L[ℂ] Ell2) (δ s : ℝ) (p : ℤ × ℤ) : ℂ :=
  (((1 + |(p.1 : ℝ)|) ^ ((1 + 2 * s + 2 * δ) / 2) * (1 + |(p.2 : ℝ)|) ^ ((1 - 2 * s) / 2) *
    (2 * π) : ℝ) : ℂ) *
    fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) (-p.2)) p.1

/-- The normalized remainder matrix is square summable for `0 ≤ t ≤ 1/2`, `0 ≤ δ < 1/2`. -/
theorem summable_correctedRemainderMatrix (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {δ s : ℝ} (hδ : 0 ≤ δ)
    (hδ' : δ < 1 / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Summable fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2 := by
  have h := (summable_mixed_correctedKernelCoeff hK hγ' hW hc hδ hδ' hs0 hs1).mul_left
    ((2 * π) ^ 2)
  let σ : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (-p.2, p.1)
      invFun := fun p => (p.2, -p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hsq : ∀ x : ℝ, 0 ≤ x → ∀ c : ℝ, (x ^ (c / 2)) ^ 2 = x ^ c := fun x hx c => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  refine ((σ.summable_iff).mpr h).congr fun p => ?_
  have h1 : 0 ≤ (1 + |(p.1 : ℝ)|) := by positivity
  have h2 : 0 ≤ (1 + |(p.2 : ℝ)|) := by positivity
  have hn : ‖correctedRemainderMatrix W δ s p‖ ^ 2 =
      ((1 + |(p.1 : ℝ)|) ^ ((1 + 2 * s + 2 * δ) / 2)) ^ 2 *
        ((1 + |(p.2 : ℝ)|) ^ ((1 - 2 * s) / 2)) ^ 2 * (2 * π) ^ 2 *
        ‖fourierCoeffOn two_pi_pos
          (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) (-p.2)) p.1‖ ^ 2 := by
    rw [correctedRemainderMatrix, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    ring
  rw [hn, hsq _ h1, hsq _ h2]
  simp only [Function.comp_apply, σ, Equiv.coe_fn_mk, Int.cast_neg, abs_neg]
  ring

/-- **Compactness of the normalized corrected-kernel remainder** (Lemma 6.7, kernel part): for a
curve with Lipschitz `γ'`, `c_E ≠ 0`, `0 ≤ t ≤ 1/2` and `0 ≤ δ < 1/2`, the operator on `ℓ²(ℤ)`
with matrix `λ_m^{1/2+t+δ} λ_n^{1/2-t} r̂_E(m, n)`, i.e. `Λ^{1/2} R_E Λ^{1/2} : H^t → H^{t+δ}`,
is a compact (Hilbert–Schmidt) operator. -/
theorem isCompactOperator_correctedRemainder (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {δ s : ℝ} (hδ : 0 ≤ δ)
    (hδ' : δ < 1 / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    IsCompactOperator (hsMatrixOp (correctedRemainderMatrix W δ s)
      (summable_correctedRemainderMatrix hK hγ' hW hc hδ hδ' hs0 hs1)) :=
  isCompactOperator_hsMatrixOp _ _

end PolyaNeumann
