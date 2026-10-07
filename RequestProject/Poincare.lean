module

public import RequestProject.Spectrum
public import RequestProject.Rellich

/-!
# Positivity of the first nonzero Neumann eigenvalue (Lemma 3.3)

We deduce `μ_j(Ω) > 0` for `j ≥ 1` from the Poincaré–Wirtinger inequality, which is part of
External theorem E2 ("Sobolev traces, compactness, and coordinates") of the paper:
for a bounded connected Lipschitz domain,
`‖u - |Ω|⁻¹ ∫_Ω u‖_{L²} ≤ C_Ω ‖∇u‖_{L²}`.
We use it in its (equivalent) mean-zero form.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-- The mean `∫_Ω u` is continuous on `L²(Ω)` when `|Ω| < ∞`. -/
lemma tendsto_integral_of_tendsto {Ω : Set ℂ} [IsFiniteMeasure (volume.restrict Ω)]
    {f : ℕ → L2 Ω} {F : L2 Ω} (hf : Tendsto f atTop (𝓝 F)) :
    Tendsto (fun n => ∫ w in Ω, f n w) atTop (𝓝 (∫ w in Ω, F w)) := by
  have h := tendsto_integral_mul (ψ := fun _ => (1 : ℂ)) (by simpa using memLp_const (1 : ℂ)) hf
  simpa using h

/-- **Poincaré–Wirtinger inequality** (part of External theorem E2 of the paper): on a bounded
Lipschitz domain there is `C > 0` with `‖u‖²_{L²} ≤ C ‖∇u‖²_{L²}` for every `u ∈ H¹(Ω)` with
`∫_Ω u = 0`.
Proved, as usual, by contradiction from the Rellich compactness theorem `rellich_compact`
and the constancy lemma `ae_const_of_weakGradient_zero`. -/
theorem poincare_wirtinger {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : L2 Ω) (g : Fin 2 → L2 Ω), IsWeakGradient Ω u g →
      ∫ w in Ω, u w = 0 → ‖u‖ ^ 2 ≤ C * ∑ i, ‖g i‖ ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr
    hb.measure_lt_top.ne
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ (u : L2 Ω) (g : Fin 2 → L2 Ω), IsWeakGradient Ω u g ∧
      ∫ w in Ω, u w = 0 ∧ ((n : ℝ) + 1) * ∑ i, ‖g i‖ ^ 2 < ‖u‖ ^ 2 :=
    fun n => hcon _ (by positivity)
  choose u g hg hmean hlt using hseq
  have hune : ∀ n, u n ≠ 0 := by
    intro n h
    have := hlt n
    rw [h, norm_zero] at this
    have : 0 ≤ ((n : ℝ) + 1) * ∑ i, ‖g n i‖ ^ 2 := by positivity
    linarith
  have hpos : ∀ n, 0 < ‖u n‖ := fun n => norm_pos_iff.mpr (hune n)
  -- normalize
  set v : ℕ → L2 Ω := fun n => ((‖u n‖⁻¹ : ℝ) : ℂ) • u n with hv
  set h : ℕ → Fin 2 → L2 Ω := fun n => ((‖u n‖⁻¹ : ℝ) : ℂ) • g n with hh
  have hvg : ∀ n, IsWeakGradient Ω (v n) (h n) := fun n => isWeakGradient_smul (hg n) _
  have hvnorm : ∀ n, ‖v n‖ = 1 := by
    intro n
    simp only [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (hpos n).ne'
  have hhsum : ∀ n, ∑ i, ‖h n i‖ ^ 2 < 1 / ((n : ℝ) + 1) := by
    intro n
    have e : ∑ i, ‖h n i‖ ^ 2 = (∑ i, ‖g n i‖ ^ 2) / ‖u n‖ ^ 2 := by
      simp only [hh, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
        abs_norm, mul_pow, inv_pow, ← Finset.mul_sum]
      field_simp
    have hp := hpos n
    rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith [hlt n]
  have hhle : ∀ n i, ‖h n i‖ ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
    intro n i
    have := Finset.single_le_sum (f := fun i => ‖h n i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ i)
    linarith [hhsum n]
  have hhC : ∀ n i, ‖h n i‖ ≤ 1 := by
    intro n i
    have h1 := hhle n i
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith [norm_nonneg (h n i)]
  obtain ⟨φ, hφ, V, hV⟩ := rellich_compact hb hL v h hvg 1 (fun n => (hvnorm n).le) hhC
  -- the limit has norm one, zero mean and zero weak gradient
  have hVnorm : ‖V‖ = 1 := by
    have := (continuous_norm.tendsto V).comp hV
    exact tendsto_nhds_unique this (by simp [Function.comp_def, hvnorm])
  have hVmean : ∫ w in Ω, V w = 0 := by
    have h1 := tendsto_integral_of_tendsto hV
    have h2 : ∀ n, ∫ w in Ω, (v ∘ φ) n w = 0 := by
      intro n
      simp only [Function.comp_apply, hv]
      rw [integral_congr_ae (Lp.coeFn_smul _ (u (φ n)))]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [integral_const_mul, hmean, mul_zero]
    simp only [h2, tendsto_const_nhds_iff] at h1
    exact h1.symm
  have hhlim : ∀ i, Tendsto (fun n => h (φ n) i) atTop (𝓝 ((0 : Fin 2 → L2 Ω) i)) := by
    intro i
    rw [Pi.zero_apply, tendsto_zero_iff_norm_tendsto_zero]
    have hsq : Tendsto (fun n => ‖h (φ n) i‖ ^ 2) atTop (𝓝 0) := by
      have hlim : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
        simpa [Function.comp_def] using this
      exact squeeze_zero (fun n => by positivity) (fun n => hhle (φ n) i) hlim
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  have hVg : IsWeakGradient Ω V 0 :=
    isWeakGradient_of_tendsto (fun n => hvg (φ n)) hV hhlim
  -- so the limit is constant, hence zero
  obtain ⟨c, hc⟩ := ae_const_of_weakGradient_zero hL.1 V hVg
  have hint : ∫ w in Ω, V w = c * (volume Ω).toReal := by
    rw [integral_congr_ae hc]
    simp [Measure.real, mul_comm]
  have hvol : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  have hc0 : c = 0 := by
    rw [hVmean] at hint
    have := hint.symm
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 (by exact_mod_cast hvol.ne')
  have hV0 : V = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hc] with w hw
    simp [hw, hc0]
  rw [hV0, norm_zero] at hVnorm
  exact zero_ne_one hVnorm

/-- The integral `u ↦ ∫_Ω u` as a linear functional on `L²(Ω)` for `|Ω| < ∞`. -/
def meanFunctional (Ω : Set ℂ) [IsFiniteMeasure (volume.restrict Ω)] : L2 Ω →ₗ[ℂ] ℂ where
  toFun u := ∫ w in Ω, u w
  map_add' u v := by
    have hu := (Lp.memLp u).integrable one_le_two
    have hv := (Lp.memLp v).integrable one_le_two
    rw [integral_congr_ae (Lp.coeFn_add u v)]
    exact integral_add hu hv
  map_smul' c u := by
    rw [integral_congr_ae (Lp.coeFn_smul c u)]
    exact integral_smul c _

/-- Every two-dimensional subspace of `L²(Ω)` contains a nonzero function of mean zero. -/
lemma exists_mean_zero (Ω : Set ℂ) [IsFiniteMeasure (volume.restrict Ω)]
    (S : Submodule ℂ (L2 Ω)) (hS : Module.finrank ℂ S = 2) :
    ∃ u ∈ S, u ≠ 0 ∧ ∫ w in Ω, u w = 0 := by
  haveI : Module.Finite ℂ S := Module.finite_of_finrank_pos (by omega)
  set ℓ := (meanFunctional Ω).domRestrict S
  have h1 := LinearMap.finrank_range_add_finrank_ker ℓ
  have h2 : Module.finrank ℂ (LinearMap.range ℓ) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range ℓ)
  have h3 : 0 < Module.finrank ℂ (LinearMap.ker ℓ) := by omega
  obtain ⟨x, hx⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := LinearMap.ker ℓ)).mp (by exact h3)
  refine ⟨((x : S) : L2 Ω), (x : S).2, ?_, ?_⟩
  · exact fun h => hx (Subtype.ext (Subtype.ext h))
  · have := x.2
    rw [LinearMap.mem_ker] at this
    exact this

/-- Under a Poincaré inequality with constant `C`, the Rayleigh quotient of a nonzero
mean-zero function is at least `1 / C`. -/
lemma rayleigh_ge_of_poincare {Ω : Set ℂ} {C : ℝ} (hC : 0 < C)
    (hP : ∀ (u : L2 Ω) (g : Fin 2 → L2 Ω), IsWeakGradient Ω u g →
      ∫ w in Ω, u w = 0 → ‖u‖ ^ 2 ≤ C * ∑ i, ‖g i‖ ^ 2)
    (u : L2 Ω) (hu : u ≠ 0) (h0 : ∫ w in Ω, u w = 0) :
    ENNReal.ofReal C⁻¹ ≤ rayleigh Ω u := by
  have hn : (‖u‖₊ : ENNReal) ^ 2 ≠ 0 := by simpa using hu
  have hn' : (‖u‖₊ : ENNReal) ^ 2 ≠ ⊤ := by simp
  rw [rayleigh, ENNReal.le_div_iff_mul_le (Or.inl hn) (Or.inl hn')]
  refine le_iInf₂ fun g hg => ?_
  have hreal := hP u g hg h0
  have e1 : (‖u‖₊ : ENNReal) ^ 2 = ENNReal.ofReal (‖u‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
  have e2 : ∑ i, (‖g i‖₊ : ENNReal) ^ 2 = ENNReal.ofReal (∑ i, ‖g i‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
  rw [e1, e2, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [inv_mul_le_iff₀ hC]
  exact hreal

/-- `μ_1(Ω) ≥ 1 / C` under a Poincaré inequality with constant `C`. -/
lemma neumannEigenvalue_one_ge_of_poincare {Ω : Set ℂ} [IsFiniteMeasure (volume.restrict Ω)]
    {C : ℝ} (hC : 0 < C)
    (hP : ∀ (u : L2 Ω) (g : Fin 2 → L2 Ω), IsWeakGradient Ω u g →
      ∫ w in Ω, u w = 0 → ‖u‖ ^ 2 ≤ C * ∑ i, ‖g i‖ ^ 2) :
    ENNReal.ofReal C⁻¹ ≤ neumannEigenvalue Ω 1 := by
  unfold neumannEigenvalue
  refine le_iInf₂ fun S hS => ?_
  obtain ⟨u, huS, hu0, hmean⟩ := exists_mean_zero Ω S hS
  exact (rayleigh_ge_of_poincare hC hP u hu0 hmean).trans
    (le_iSup₂_of_le u huS (le_iSup_of_le hu0 le_rfl))

/-- Lemma 3.3: `μ_j(Ω) > 0` for `j ≥ 1` on a bounded Lipschitz domain (from the
Poincaré–Wirtinger inequality). -/
theorem neumannEigenvalue_pos {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (j : ℕ) (hj : 1 ≤ j) : 0 < neumannEigenvalue Ω j := by
  haveI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr
    hb.measure_lt_top.ne
  obtain ⟨C, hC, hP⟩ := poincare_wirtinger hb hL
  have h1 := neumannEigenvalue_one_ge_of_poincare hC hP
  have h2 := neumannEigenvalue_monotone Ω hj
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr hC)) (h1.trans h2)

end PolyaNeumann

end
