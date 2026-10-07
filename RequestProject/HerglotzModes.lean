module

public import RequestProject.HerglotzMean

/-!
# Smallness of the negative Herglotz modes

Fix a disc `B(z₁, r) ⊆ Ω`. If the Herglotz coefficients `F_{-j}` (`j ≥ 1`) of a density all vanish
at `z₁`, each of them has zero mean over the disc (mean value property), so the ball Poincaré
inequality gives `∫_Ω |F_{-j}|² ≤ C (k²/2) ∫_Ω (|F_{-j+1}|² + |F_{-j-1}|²)`. Summing this chain
(the sum converges by Parseval) and combining with the Poincaré–Wirtinger inequality for `F₀`
(when `∫_Ω F₀ = 0`) yields, for small `k`,

  `∫_Ω |F₀|² ≤ C k² ∫_Ω |F₁|²`,   `∫_Ω (|F₋₁|² + |F₋₂|²) ≤ C k⁴ ∫_Ω |F₁|²`

(`herglotz_modes_small`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {a : ℝ → ℂ}

/-- Parseval for the Herglotz coefficients at a point. -/
lemma hasSum_sq_herglotzCoeff (ha : IsDirDensity a) (k : ℝ) (z : ℂ) :
    HasSum (fun m : ℤ => ‖herglotzCoeff k a m z‖ ^ 2)
      ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ ^ 2) := by
  have hm : MemLp (fun φ => a φ * planeWave k z φ) 2 (volume.restrict (Ioc 0 (2 * π))) := by
    have hb : MemLp (planeWave k z) ⊤ (volume.restrict (Ioc 0 (2 * π))) :=
      memLp_top_of_bound (continuous_planeWave k z).aestronglyMeasurable 1
        (Eventually.of_forall fun φ => (norm_planeWave k z φ).le)
    have := ha.mul' (r := 2) hb
    refine this.congr_norm (ha.aestronglyMeasurable.mul hb.aestronglyMeasurable)
      (Eventually.of_forall fun φ => ?_)
    simp only [norm_mul, mul_comm]
  simp_rw [herglotzCoeff_eq_fourierCoeffOn]
  convert hasSum_sq_fourierCoeffOn Real.two_pi_pos hm using 1
  rw [smul_eq_mul, sub_zero]
  congr 1
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [norm_mul, norm_planeWave, mul_one]

/-- `N_j = ∫_Ω |F_{-j}|²`. -/
def negModeNorm (Ω : Set ℂ) (k : ℝ) (a : ℝ → ℂ) (j : ℕ) : ℝ :=
  ∫ z in Ω, ‖herglotzCoeff k a (-(j : ℤ)) z‖ ^ 2

lemma negModeNorm_nonneg (k : ℝ) (a : ℝ → ℂ) (j : ℕ) : 0 ≤ negModeNorm Ω k a j :=
  integral_nonneg fun _ => by positivity

lemma integrable_herglotzCoeff_sq (hb : Bornology.IsBounded Ω)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ) :
    Integrable (fun z => ‖herglotzCoeff k a m z‖ ^ 2) (volume.restrict Ω) :=
  integrable_norm_sq_of_bounded hb.measure_lt_top (continuous_herglotzCoeff ha k m)
    (norm_herglotzCoeff_le k m)

lemma summable_negModeNorm (hb : Bornology.IsBounded Ω) (ha : IsDirDensity a) (k : ℝ) :
    Summable (negModeNorm Ω k a) := by
  set A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ ^ 2 with hA
  refine summable_of_sum_range_le (c := A * (volume Ω).toReal) (negModeNorm_nonneg k a)
    fun N => ?_
  unfold negModeNorm
  rw [← integral_finset_sum _ fun j _ => integrable_herglotzCoeff_sq hb ha.intervalIntegrable k _]
  have hpt : ∀ z, ∑ j ∈ Finset.range N, ‖herglotzCoeff k a (-(j : ℤ)) z‖ ^ 2 ≤ A := by
    intro z
    have e : ∑ j ∈ Finset.range N, ‖herglotzCoeff k a (-(j : ℤ)) z‖ ^ 2 =
        ∑ m ∈ (Finset.range N).map ⟨fun j : ℕ => -(j : ℤ), fun i j h => by simpa using h⟩,
          ‖herglotzCoeff k a m z‖ ^ 2 := by
      rw [Finset.sum_map]; rfl
    rw [e]
    exact sum_le_hasSum _ (fun _ _ => by positivity) (hasSum_sq_herglotzCoeff ha k z)
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  calc ∫ z in Ω, ∑ j ∈ Finset.range N, ‖herglotzCoeff k a (-(j : ℤ)) z‖ ^ 2
      ≤ ∫ _ in Ω, A := integral_mono (integrable_finset_sum _ fun j _ =>
          integrable_herglotzCoeff_sq hb ha.intervalIntegrable k _) (integrable_const _) hpt
    _ = A * (volume Ω).toReal := by
        rw [integral_const, smul_eq_mul, Measure.real_def,
          Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm]

/-- The Poincaré chain for the negative modes. -/
lemma negModeNorm_chain (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {z₁ : ℂ}
    {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ → ℂ, IntervalIntegrable a volume 0 (2 * π) → ∀ k : ℝ,
      (∀ j : ℕ, 1 ≤ j → herglotzCoeff k a (-(j : ℤ)) z₁ = 0) → ∀ j : ℕ,
        negModeNorm Ω k a (j + 1) ≤ c * k ^ 2 * (negModeNorm Ω k a j + negModeNorm Ω k a (j + 2)) := by
  obtain ⟨C, hC, hP⟩ := poincare_herglotzCoeff_ball hb hL hr hball
  refine ⟨C / 2, by positivity, fun a ha k hz j => ?_⟩
  have h0 : ∫ z in ball z₁ r, herglotzCoeff k a (-((j + 1 : ℕ) : ℤ)) z = 0 := by
    rw [integral_ball_herglotzCoeff ha, hz (j + 1) (by omega), mul_zero]
  have key := hP a ha k _ h0
  have e1 : -((j + 1 : ℕ) : ℤ) + 1 = -(j : ℤ) := by push_cast; ring
  have e2 : -((j + 1 : ℕ) : ℤ) - 1 = -((j + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, integral_add (integrable_herglotzCoeff_sq hb ha k _)
    (integrable_herglotzCoeff_sq hb ha k _)] at key
  unfold negModeNorm
  calc _ ≤ C * (k ^ 2 / 2 * ((∫ z in Ω, ‖herglotzCoeff k a (-(j : ℤ)) z‖ ^ 2) +
        ∫ z in Ω, ‖herglotzCoeff k a (-((j + 2 : ℕ) : ℤ)) z‖ ^ 2)) := key
    _ = _ := by ring

/-- **Smallness of `F₀` and of the negative modes.** -/
theorem herglotz_modes_small (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {z₁ : ℂ}
    {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a, IsDirDensity a → ∀ k : ℝ, k ^ 2 ≤ δ →
      (∀ j : ℕ, 1 ≤ j → herglotzCoeff k a (-(j : ℤ)) z₁ = 0) →
      ∫ z in Ω, herglotzCoeff k a 0 z = 0 →
        ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2 ≤
            C * k ^ 2 * ∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2 ∧
          (∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2) + ∫ z in Ω, ‖herglotzCoeff k a (-2) z‖ ^ 2 ≤
            C * k ^ 4 * ∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2 := by
  obtain ⟨c, hc, hchain⟩ := negModeNorm_chain hb hL hr hball
  obtain ⟨cP, hcP, hP⟩ := poincare_herglotzCoeff hb hL
  refine ⟨cP + 2 * c * cP, min 1 (min (1 / (4 * c)) (1 / (2 * c * cP))), by positivity,
    by positivity, fun a ha k hk hz hmean => ?_⟩
  have hai := ha.intervalIntegrable
  set N := negModeNorm Ω k a with hN
  set A1 := ∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2 with hA1
  have hA10 : 0 ≤ A1 := integral_nonneg fun _ => by positivity
  have hN0 : ∀ j, 0 ≤ N j := negModeNorm_nonneg k a
  have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
  have hkδ1 : k ^ 2 ≤ 1 := hk.trans (min_le_left _ _)
  have hkδ2 : k ^ 2 ≤ 1 / (4 * c) := hk.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkδ3 : k ^ 2 ≤ 1 / (2 * c * cP) := hk.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hck : c * k ^ 2 ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * c)] at hkδ2
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]; nlinarith
  -- the summed chain
  set T : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, N (i + 1) with hT
  have hTbound : ∀ n, T n ≤ 2 * (c * k ^ 2) * (N 0 + N (n + 1)) := by
    intro n
    have hsum : T n ≤ c * k ^ 2 * ((∑ i ∈ Finset.range n, N i) +
        ∑ i ∈ Finset.range n, N (i + 2)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hchain a hai k hz i
    have h1 : ∑ i ∈ Finset.range n, N i ≤ N 0 + T n := by
      have := Finset.sum_range_succ' N n
      have h2 := Finset.sum_range_succ N n
      rw [hT]; linarith [hN0 n]
    have h3 : ∑ i ∈ Finset.range n, N (i + 2) ≤ T n + N (n + 1) := by
      have := Finset.sum_range_succ' (fun i => N (i + 1)) n
      have h4 := Finset.sum_range_succ (fun i => N (i + 1)) n
      rw [hT]; linarith [hN0 1]
    have hTn : 0 ≤ T n := Finset.sum_nonneg fun i _ => hN0 _
    have hck0 : 0 ≤ c * k ^ 2 := by positivity
    nlinarith
  have h12 : N 1 + N 2 ≤ 2 * (c * k ^ 2) * N 0 := by
    have hsum := summable_negModeNorm hb ha k
    have ht : Tendsto (fun n => N (n + 1)) atTop (nhds 0) :=
      (hsum.tendsto_atTop_zero).comp (tendsto_add_atTop_nat 1)
    have hlim : Tendsto (fun n => 2 * (c * k ^ 2) * (N 0 + N (n + 1))) atTop
        (nhds (2 * (c * k ^ 2) * (N 0 + 0))) := (ht.const_add _).const_mul _
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim (eventually_atTop.mpr ⟨2, fun n hn => ?_⟩)
    have : N 1 + N 2 ≤ T n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      simp only [hT, Finset.sum_range_succ', zero_add]
      have : 0 ≤ ∑ i ∈ Finset.range m, N (i + 1 + 1 + 1) := Finset.sum_nonneg fun i _ => hN0 _
      linarith
    exact this.trans (hTbound n)
  -- `F₀`
  have hF0 := hP a hai k 0 hmean
  rw [integral_add (integrable_herglotzCoeff_sq hb hai k _)
    (integrable_herglotzCoeff_sq hb hai k _)] at hF0
  have eN1 : ∫ z in Ω, ‖herglotzCoeff k a (0 - 1) z‖ ^ 2 = N 1 := by
    simp [hN, negModeNorm]
  have eN0 : ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2 = N 0 := by simp [hN, negModeNorm]
  simp only [zero_add] at hF0
  rw [eN1, eN0] at hF0
  have hcc : cP * c * k ^ 4 ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c * cP)] at hkδ3
    have : k ^ 4 ≤ k ^ 2 := by nlinarith
    nlinarith [mul_pos hc hcP]
  have hN0b : N 0 ≤ cP * k ^ 2 * A1 := by
    have : N 0 ≤ cP * (k ^ 2 / 2) * A1 + cP * c * k ^ 4 * N 0 := by
      have h1 : N 1 ≤ 2 * (c * k ^ 2) * N 0 := by linarith [hN0 2]
      calc N 0 ≤ cP * (k ^ 2 / 2 * (A1 + N 1)) := hF0
        _ ≤ cP * (k ^ 2 / 2 * (A1 + 2 * (c * k ^ 2) * N 0)) := by gcongr
        _ = _ := by ring
    nlinarith [hN0 0]
  constructor
  · rw [eN0]
    calc N 0 ≤ cP * k ^ 2 * A1 := hN0b
      _ ≤ (cP + 2 * c * cP) * k ^ 2 * A1 := by
          have : 0 ≤ 2 * c * cP * k ^ 2 * A1 := by positivity
          nlinarith
  · calc _ = N 1 + N 2 := by
          simp only [hN, negModeNorm, Nat.cast_one, Nat.cast_ofNat]
      _ ≤ 2 * (c * k ^ 2) * N 0 := h12
      _ ≤ 2 * (c * k ^ 2) * (cP * k ^ 2 * A1) := by gcongr
      _ = 2 * c * cP * k ^ 4 * A1 := by ring
      _ ≤ (cP + 2 * c * cP) * k ^ 4 * A1 := by
          have : 0 ≤ cP * k ^ 4 * A1 := by positivity
          nlinarith

end PolyaNeumann
