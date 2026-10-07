module

public import RequestProject.ObservationHS
public import RequestProject.CorrectedKernelCont

/-!
# Lemma 6.3: continuity in the energy of the projected observation in Hilbert–Schmidt norm

Let `W_E` be the transports of a Lipschitz curve and `E₀` an energy with
`c_{E₀} = (V_{E₀}^* - I) e₀ ≠ 0`. For an orthonormal family `(vⱼ)` of `ℓ²`, write
`cⱼ^E(n)` for the Fourier coefficients on `[0, L]` of `O_E Π^c_E vⱼ`. Then, as `E → E₀`,

* `∑ⱼ ∑ₙ n² |cⱼ^E(n) - cⱼ^{E₀}(n)|² → 0` (`tendsto_projected_observation_H1_energy`), and
* `∑ⱼ ∑ₙ |cⱼ^E(n) - cⱼ^{E₀}(n)|² → 0` (`tendsto_projected_observation_L2_energy`).

Together these say that `E ↦ O_E Π^c_E : ℓ² → H¹(𝕋)` is continuous in Hilbert–Schmidt norm,
the continuity statement of Lemma 6.3.

The proof avoids derivatives. The difference of rows
`D_E(θ) = Π^c_E W_E(θ)^* e₀ - Π^c_{E₀} W_{E₀}(θ)^* e₀` has matching endpoint values and a
Lipschitz constant that tends to `0`: the increments of `W_E - W_{E₀}` are integrals of
`C_E W_E - C_{E₀} W_{E₀}`, which is uniformly small, and `Π^c_E → Π^c_{E₀}` in norm. The
difference-quotient estimate of `FourierLipschitz.lean` then bounds the `H¹` part by
`π² Lip(D_E)² / 4`, and Bessel's inequality bounds the `L²` part by `sup ‖D_E‖²`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

/-! ### Bessel's inequality for rows -/

section BesselRows

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {v : ι → H} {r : ℝ → H}

/-- **`L²` Hilbert–Schmidt bound for bounded continuous rows.** If `r` is continuous with
`‖r(θ)‖ ≤ B` on `[0, 2π]` and `(vⱼ)` is orthonormal, the Fourier coefficients `cⱼ(n)` of
`θ ↦ ⟨r(θ), vⱼ⟩` satisfy `∑ⱼ ∑ₙ |cⱼ(n)|² ≤ B²`. -/
theorem tsum_sq_fourierCoeff_rows_le (hv : Orthonormal ℂ v) (hr : Continuous r) {B : ℝ}
    (hB : ∀ θ ∈ Icc 0 (2 * π), ‖r θ‖ ≤ B) :
    Summable (fun p : ι × ℤ => ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2) ∧
    ∑' p : ι × ℤ, ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 ≤ B ^ 2 := by
  have hcont : ∀ j, Continuous fun θ => ⟪r θ, v j⟫_ℂ := fun j => hr.inner continuous_const
  have hrow : ∀ j, HasSum (fun n => ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖⟪r θ, v j⟫_ℂ‖ ^ 2) := fun j =>
    hasSum_sq_fourierCoeffOn_of_continuous (hcont j)
  have hfin : ∀ J : Finset ι,
      ∑ j ∈ J, (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖⟪r θ, v j⟫_ℂ‖ ^ 2 ≤ B ^ 2 := by
    intro J
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum
      (f := fun j θ => ‖⟪r θ, v j⟫_ℂ‖ ^ 2) fun j _ =>
      (((hcont j).norm.pow 2 : Continuous fun θ => ‖⟪r θ, v j⟫_ℂ‖ ^ 2)).intervalIntegrable _ _]
    have hint : ∫ θ in (0 : ℝ)..(2 * π), ∑ j ∈ J, ‖⟪r θ, v j⟫_ℂ‖ ^ 2 ≤
        ∫ θ in (0 : ℝ)..(2 * π), B ^ 2 := by
      refine intervalIntegral.integral_mono_on two_pi_pos.le ?_ intervalIntegrable_const
        fun θ hθ => ?_
      · exact (continuous_finset_sum _ fun j _ => (hcont j).norm.pow 2).intervalIntegrable _ _
      · calc ∑ j ∈ J, ‖⟪r θ, v j⟫_ℂ‖ ^ 2 = ∑ j ∈ J, ‖⟪v j, r θ⟫_ℂ‖ ^ 2 :=
              Finset.sum_congr rfl fun j _ => by rw [norm_inner_symm]
          _ ≤ ‖r θ‖ ^ 2 := hv.sum_inner_products_le (r θ)
          _ ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB θ hθ) 2
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
    have hpi : 0 < 2 * π := two_pi_pos
    calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ∑ j ∈ J, ‖⟪r θ, v j⟫_ℂ‖ ^ 2
        ≤ (2 * π)⁻¹ * (2 * π * B ^ 2) := by gcongr
      _ = B ^ 2 := by field_simp
  have hnn : 0 ≤ fun p : ι × ℤ =>
      ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := fun p => by positivity
  have hsumm_rows : Summable fun j : ι =>
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖⟪r θ, v j⟫_ℂ‖ ^ 2 := by
    refine summable_of_sum_le (c := B ^ 2) (fun j => ?_) hfin
    exact (hrow j).nonneg fun n => by positivity
  have hS : Summable (fun p : ι × ℤ =>
      ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg hnn]
    refine ⟨fun j => (hrow j).summable, ?_⟩
    simp only [fun j => (hrow j).tsum_eq]
    exact hsumm_rows
  refine ⟨hS, ?_⟩
  rw [hS.tsum_prod]
  simp only [fun j => (hrow j).tsum_eq]
  exact hsumm_rows.tsum_le_of_sum_le hfin

end BesselRows

variable {γ : ℝ → ℂ} {K : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}

/-- Increments of the difference of two transports: if `‖W'(s) - W(s)‖ ≤ d` on `[0, L]`, then
`‖(W' - W)(θ₁) - (W' - W)(θ₂)‖ ≤ (|√E' - √E| κ K + √E κ K d) |θ₁ - θ₂|`. -/
lemma norm_transport_diff_sub_le (hK : LipschitzWith K γ) {E E' : ℝ}
    {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') {d : ℝ}
    (hd : ∀ s ∈ Icc 0 (2 * π), ‖W' s - W s‖ ≤ d) {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π)) :
    ‖(W' θ₁ - W θ₁) - (W' θ₂ - W θ₂)‖ ≤
      (|Real.sqrt E' - Real.sqrt E| * shiftConst * K + Real.sqrt E * shiftConst * K * d) *
        |θ₁ - θ₂| := by
  have hC := transportCoeff_aestronglyMeasurable γ E
  have hM := transportCoeff_norm_le γ E hK
  have hC' := transportCoeff_aestronglyMeasurable γ E'
  have hM' := transportCoeff_norm_le γ E' hK
  have hκ := shiftConst_nonneg
  have e : (W' θ₁ - W θ₁) - (W' θ₂ - W θ₂) = (W' θ₁ - W' θ₂) - (W θ₁ - W θ₂) := by abel
  have a1 := intervalIntegrable_mul_of_continuousOn hC hM hW.1 h₁
  have a2 := intervalIntegrable_mul_of_continuousOn hC hM hW.1 h₂
  have b1 := intervalIntegrable_mul_of_continuousOn hC' hM' hW'.1 h₁
  have b2 := intervalIntegrable_mul_of_continuousOn hC' hM' hW'.1 h₂
  rw [e, hW.2 θ₁ h₁, hW.2 θ₂ h₂, hW'.2 θ₁ h₁, hW'.2 θ₂ h₂, add_sub_add_left_eq_sub,
    add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left a1 a2,
    intervalIntegral.integral_interval_sub_left b1 b2,
    ← intervalIntegral.integral_sub (b2.symm.trans b1) (a2.symm.trans a1)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  have ht' : t ∈ Icc 0 (2 * π) := by
    have := uIoc_subset_uIcc ht
    rw [mem_uIcc] at this
    rcases this with h | h
    · exact ⟨h₂.1.trans h.1, h.2.trans h₁.2⟩
    · exact ⟨h₁.1.trans h.1, h.2.trans h₂.2⟩
  have e2 : transportCoeff γ E' t * W' t - transportCoeff γ E t * W t =
      (transportCoeff γ E' t - transportCoeff γ E t) * W' t +
        transportCoeff γ E t * (W' t - W t) := by
    rw [sub_mul, mul_sub]; abel
  rw [e2]
  have hCC : ‖transportCoeff γ E' t - transportCoeff γ E t‖ ≤
      |Real.sqrt E' - Real.sqrt E| * shiftConst * K := by
    rw [transportCoeff_eq_coeffOf, transportCoeff_eq_coeffOf]
    refine (norm_coeffOf_sub_coeffOf_le E' E _).trans ?_
    have := norm_deriv_le_of_lipschitz hK (x₀ := t)
    gcongr
  have hW1 := norm_transport_le_one hK hW' ht'
  have hCt := norm_transportCoeff_le_const hK E t
  have hdt := hd t ht'
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_mul_le _ _).trans ?_) ((norm_mul_le _ _).trans ?_)
  · calc _ ≤ (|Real.sqrt E' - Real.sqrt E| * shiftConst * K) * 1 :=
          mul_le_mul hCC hW1 (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  · exact mul_le_mul hCt hdt (norm_nonneg _) (by positivity)

/-- Lipschitz bound for the difference of two projected observation rows. -/
lemma norm_projObsRow_diff_sub_le (hK : LipschitzWith K γ) {E E' : ℝ}
    {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') {d : ℝ}
    (hd : ∀ s ∈ Icc 0 (2 * π), ‖W' s - W s‖ ≤ d) {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π)) :
    ‖(projObsRow W' θ₁ - projObsRow W θ₁) - (projObsRow W' θ₂ - projObsRow W θ₂)‖ ≤
      (|Real.sqrt E' - Real.sqrt E| * shiftConst * K + Real.sqrt E * shiftConst * K * d +
        ‖cutProj (cutC (W' (2 * π)) (basisVec 0)) - cutProj (cutC (W (2 * π)) (basisVec 0))‖ *
          (Real.sqrt E * shiftConst * K)) * |θ₁ - θ₂| := by
  set P' := cutProj (cutC (W' (2 * π)) (basisVec 0))
  set P := cutProj (cutC (W (2 * π)) (basisVec 0))
  have hadj : ∀ X : Ell2 →L[ℂ] Ell2, ‖ContinuousLinearMap.adjoint X (basisVec 0)‖ ≤ ‖X‖ := by
    intro X
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map, norm_basisVec_zero, mul_one]
  have e : (projObsRow W' θ₁ - projObsRow W θ₁) - (projObsRow W' θ₂ - projObsRow W θ₂) =
      P' (ContinuousLinearMap.adjoint ((W' θ₁ - W θ₁) - (W' θ₂ - W θ₂)) (basisVec 0)) +
        (P' - P) (ContinuousLinearMap.adjoint (W θ₁ - W θ₂) (basisVec 0)) := by
    simp only [projObsRow, P, P', map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [e]
  have t1 := (norm_cutProj_apply_le (cutC (W' (2 * π)) (basisVec 0))
    (ContinuousLinearMap.adjoint ((W' θ₁ - W θ₁) - (W' θ₂ - W θ₂)) (basisVec 0))).trans
    ((hadj _).trans (norm_transport_diff_sub_le hK hW hW' hd h₁ h₂))
  have t2 : ‖(P' - P) (ContinuousLinearMap.adjoint (W θ₁ - W θ₂) (basisVec 0))‖ ≤
      ‖P' - P‖ * (Real.sqrt E * shiftConst * K * |θ₁ - θ₂|) :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left ((hadj _).trans (norm_transport_sub_le_lip hK hW h₁ h₂))
        (norm_nonneg _))
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ (|Real.sqrt E' - Real.sqrt E| * shiftConst * K + Real.sqrt E * shiftConst * K * d) *
        |θ₁ - θ₂| + ‖P' - P‖ * (Real.sqrt E * shiftConst * K * |θ₁ - θ₂|) := add_le_add t1 t2
    _ = _ := by ring

/-- Pointwise bound for the difference of two projected observation rows. -/
lemma norm_projObsRow_diff_le (hK : LipschitzWith K γ) {E : ℝ}
    {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {d : ℝ}
    (hd : ∀ s ∈ Icc 0 (2 * π), ‖W' s - W s‖ ≤ d) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖projObsRow W' θ - projObsRow W θ‖ ≤
      d + ‖cutProj (cutC (W' (2 * π)) (basisVec 0)) - cutProj (cutC (W (2 * π)) (basisVec 0))‖ := by
  set P' := cutProj (cutC (W' (2 * π)) (basisVec 0))
  set P := cutProj (cutC (W (2 * π)) (basisVec 0))
  have hadj : ∀ X : Ell2 →L[ℂ] Ell2, ‖ContinuousLinearMap.adjoint X (basisVec 0)‖ ≤ ‖X‖ := by
    intro X
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map, norm_basisVec_zero, mul_one]
  have e : projObsRow W' θ - projObsRow W θ =
      P' (ContinuousLinearMap.adjoint (W' θ - W θ) (basisVec 0)) +
        (P' - P) (ContinuousLinearMap.adjoint (W θ) (basisVec 0)) := by
    simp only [projObsRow, P, P', map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [e]
  have t1 := (norm_cutProj_apply_le (cutC (W' (2 * π)) (basisVec 0))
    (ContinuousLinearMap.adjoint (W' θ - W θ) (basisVec 0))).trans ((hadj _).trans (hd θ hθ))
  have t2 : ‖(P' - P) (ContinuousLinearMap.adjoint (W θ) (basisVec 0))‖ ≤ ‖P' - P‖ * 1 :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left ((hadj _).trans (norm_transport_le_one hK hW hθ))
        (norm_nonneg _))
  rw [mul_one] at t2
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

/-- Continuity of the projection `Π^c_E` in the energy at `E₀` when `c_{E₀} ≠ 0`. -/
theorem tendsto_cutProj_energy (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E))
    (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    Tendsto (fun E => cutProj (cutC (Ws E (2 * π)) (basisVec 0))) (𝓝 E₀)
      (𝓝 (cutProj (cutC (Ws E₀ (2 * π)) (basisVec 0)))) := by
  have h2π : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hV := tendsto_transport_energy hK hWs E₀ h2π
  have hVa : Tendsto (fun E => ContinuousLinearMap.adjoint (Ws E (2 * π)) (basisVec 0)) (𝓝 E₀)
      (𝓝 (ContinuousLinearMap.adjoint (Ws E₀ (2 * π)) (basisVec 0))) :=
    ((continuous_eval_const (basisVec 0)).tendsto _).comp
      (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.tendsto _).comp
        hV)
  have hC : Tendsto (fun E => cutC (Ws E (2 * π)) (basisVec 0)) (𝓝 E₀)
      (𝓝 (cutC (Ws E₀ (2 * π)) (basisVec 0))) := by
    unfold cutC; exact hVa.sub tendsto_const_nhds
  have hn : Tendsto (fun E => ((‖cutC (Ws E (2 * π)) (basisVec 0)‖ ^ 2 : ℝ) : ℂ)) (𝓝 E₀)
      (𝓝 ((‖cutC (Ws E₀ (2 * π)) (basisVec 0)‖ ^ 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (hC.norm.pow 2)
  have h0 : ((‖cutC (Ws E₀ (2 * π)) (basisVec 0)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := norm_pos_iff.mpr hc
    exact_mod_cast (by positivity : (0 : ℝ) < ‖cutC (Ws E₀ (2 * π)) (basisVec 0)‖ ^ 2).ne'
  unfold cutProj
  exact tendsto_const_nhds.sub ((hn.inv₀ h0).smul (tendsto_rankOne hC hC))

/-- The difference of projected observation rows at energies `E` and `E₀`. -/
def projObsRowDiff (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (E₀ E : ℝ) : ℝ → Ell2 :=
  fun θ => projObsRow (Ws E) θ - projObsRow (Ws E₀) θ

/-- Fourier coefficients of the difference of projected observations are those of the
periodized row difference paired with the vector. -/
lemma fourierCoeffOn_observation_diff (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ E : ℝ)
    (x : Ell2) (n : ℤ) :
    fourierCoeffOn two_pi_pos
      (fun θ => observation (Ws E) (cutProj (cutC (Ws E (2 * π)) (basisVec 0)) x) θ -
        observation (Ws E₀) (cutProj (cutC (Ws E₀ (2 * π)) (basisVec 0)) x) θ) n =
      fourierCoeffOn two_pi_pos (fun θ => ⟪periodize (projObsRowDiff Ws E₀ E) θ, x⟫_ℂ) n := by
  have hend : projObsRowDiff Ws E₀ E (2 * π) = projObsRowDiff Ws E₀ E 0 := by
    simp only [projObsRowDiff, projObsRow_endpoint (hWs E), projObsRow_endpoint (hWs E₀)]
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [Set.uIcc_of_le two_pi_pos.le] at hθ
  simp only [observation_cutProj_eq, periodize_eqOn_Icc hend hθ, projObsRowDiff, inner_sub_left]

/-- The row difference has a Lipschitz periodization and a sup bound, both with constants
tending to `0` as `E → E₀`. -/
lemma projObsRowDiff_data (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E))
    (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    ∃ Lf Bf : ℝ → ℝ, Tendsto Lf (𝓝 E₀) (𝓝 0) ∧ Tendsto Bf (𝓝 E₀) (𝓝 0) ∧
      ∀ E, LipschitzWith (Lf E).toNNReal (periodize (projObsRowDiff Ws E₀ E)) ∧
        ∀ θ ∈ Icc 0 (2 * π), ‖projObsRowDiff Ws E₀ E θ‖ ≤ Bf E := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  set pf : ℝ → ℝ := fun E =>
    ‖cutProj (cutC (Ws E (2 * π)) (basisVec 0)) - cutProj (cutC (Ws E₀ (2 * π)) (basisVec 0))‖
  have hp : Tendsto pf (𝓝 E₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_cutProj_energy hK hWs E₀ hc)
  have hD := tendsto_transportDist K R E₀
  have hsq : Tendsto (fun E => |Real.sqrt E - Real.sqrt E₀|) (𝓝 E₀) (𝓝 0) := by
    have : Continuous fun E => |Real.sqrt E - Real.sqrt E₀| := by fun_prop
    simpa using this.tendsto E₀
  refine ⟨fun E => |Real.sqrt E - Real.sqrt E₀| * shiftConst * K +
      Real.sqrt E₀ * shiftConst * K * transportDist K R E₀ E + pf E * (Real.sqrt E₀ * shiftConst * K),
    fun E => transportDist K R E₀ E + pf E, ?_, ?_, fun E => ⟨?_, ?_⟩⟩
  · have := ((hsq.mul_const shiftConst).mul_const (K : ℝ)).add
      ((hD.const_mul (Real.sqrt E₀ * shiftConst * K)).add
        (hp.mul_const (Real.sqrt E₀ * shiftConst * K)))
    simpa only [zero_mul, mul_zero, add_zero, add_assoc] using this
  · simpa only [add_zero] using hD.add hp
  · have hd : ∀ s ∈ Icc 0 (2 * π), ‖Ws E s - Ws E₀ s‖ ≤ transportDist K R E₀ E :=
      fun s hs => norm_transport_sub_le hK hR (hWs E₀) (hWs E) hs
    have hend : projObsRowDiff Ws E₀ E (2 * π) = projObsRowDiff Ws E₀ E 0 := by
      simp only [projObsRowDiff, projObsRow_endpoint (hWs E), projObsRow_endpoint (hWs E₀)]
    refine lipschitzWith_periodize (fun x hx y hy => ?_) hend
    refine (norm_projObsRow_diff_sub_le hK (hWs E₀) (hWs E) hd hx hy).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _)
  · intro θ hθ
    exact norm_projObsRow_diff_le hK (hWs E₀)
      (fun s hs => norm_transport_sub_le hK hR (hWs E₀) (hWs E) hs) hθ

/-- **Lemma 6.3 (continuity in `E`, `H¹` part).** If `c_{E₀} ≠ 0`, then for every orthonormal
family `(vⱼ)` of `ℓ²`, `∑ⱼ ∑ₙ n² |cⱼ^E(n) - cⱼ^{E₀}(n)|² → 0` as `E → E₀`, where `cⱼ^E(n)` are
the Fourier coefficients on `[0, L]` of `O_E Π^c_E vⱼ`. -/
theorem tendsto_projected_observation_H1_energy (hK : LipschitzWith K γ)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0)
    {ι : Type*} {v : ι → Ell2} (hv : Orthonormal ℂ v) :
    Tendsto (fun E => ∑' p : ι × ℤ, ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos
      (fun θ => observation (Ws E) (cutProj (cutC (Ws E (2 * π)) (basisVec 0)) (v p.1)) θ -
        observation (Ws E₀) (cutProj (cutC (Ws E₀ (2 * π)) (basisVec 0)) (v p.1)) θ) p.2‖ ^ 2)
      (𝓝 E₀) (𝓝 0) := by
  obtain ⟨Lf, Bf, hL, -, hdat⟩ := projObsRowDiff_data hK hWs E₀ hc
  simp only [fourierCoeffOn_observation_diff hWs]
  have hlim : Tendsto (fun E => π ^ 2 * ((Lf E).toNNReal : ℝ) ^ 2 / 4) (𝓝 E₀) (𝓝 0) := by
    have h1 : Tendsto (fun E => ((Lf E).toNNReal : ℝ)) (𝓝 E₀) (𝓝 0) := by
      have := (continuous_real_toNNReal.tendsto 0).comp hL
      simpa [Function.comp_def] using (NNReal.continuous_coe.tendsto _).comp this
    simpa using ((h1.pow 2).const_mul (π ^ 2)).div_const 4
  refine squeeze_zero (fun E => tsum_nonneg fun p => by positivity) (fun E => ?_) hlim
  exact tsum_sq_mul_fourierCoeff_le hv (hdat E).1 (periodic_periodize _)

/-- **Lemma 6.3 (continuity in `E`, `L²` part).** If `c_{E₀} ≠ 0`, then for every orthonormal
family `(vⱼ)` of `ℓ²`, `∑ⱼ ∑ₙ |cⱼ^E(n) - cⱼ^{E₀}(n)|² → 0` as `E → E₀`. -/
theorem tendsto_projected_observation_L2_energy (hK : LipschitzWith K γ)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0)
    {ι : Type*} {v : ι → Ell2} (hv : Orthonormal ℂ v) :
    Tendsto (fun E => ∑' p : ι × ℤ, ‖fourierCoeffOn two_pi_pos
      (fun θ => observation (Ws E) (cutProj (cutC (Ws E (2 * π)) (basisVec 0)) (v p.1)) θ -
        observation (Ws E₀) (cutProj (cutC (Ws E₀ (2 * π)) (basisVec 0)) (v p.1)) θ) p.2‖ ^ 2)
      (𝓝 E₀) (𝓝 0) := by
  obtain ⟨Lf, Bf, -, hB, hdat⟩ := projObsRowDiff_data hK hWs E₀ hc
  simp only [fourierCoeffOn_observation_diff hWs]
  refine squeeze_zero (fun E => tsum_nonneg fun p => by positivity) (fun E => ?_)
    (by simpa using hB.pow 2)
  have hend : projObsRowDiff Ws E₀ E (2 * π) = projObsRowDiff Ws E₀ E 0 := by
    simp only [projObsRowDiff, projObsRow_endpoint (hWs E), projObsRow_endpoint (hWs E₀)]
  refine (tsum_sq_fourierCoeff_rows_le hv (hdat E).1.continuous (fun θ hθ => ?_)).2
  rw [periodize_eqOn_Icc hend hθ]
  exact (hdat E).2 θ hθ

end PolyaNeumann
