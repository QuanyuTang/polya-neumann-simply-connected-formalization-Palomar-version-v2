module

public import RequestProject.TraceIneq
public import RequestProject.HerglotzModes
public import RequestProject.HerglotzSchurBound

/-!
# Lemma 8.5: nonnegativity of the Schur complement on Herglotz data

Fix a disc `B(z₁, r) ⊆ Ω`. For small `E = k² > 0` and every density `a` whose Herglotz wave has
zero mean over `Ω` and whose negative coefficients `F_{-j}` (`j ≥ 1`) vanish at `z₁`, the Schur
complement `C(v_a)` of the Herglotz vector is nonnegative (`herglotz_imSchur_nonneg`).

The principal part is `2k² ∫_Ω (|F₁|² + 2|F₋₁|² − 3|F₀|²) − 2k² Im ∫ conj(q) Q`, the remainder is
`O(E (∫|G − c|)²)` (`imSchur_herglotzVec_sub_principal_le`). The smallness of `F₀`, `F₋₁`, `F₋₂`
(`herglotz_modes_small`) and the trace inequality (`trace_sq_le`) bound everything except
`2k² ∫ |F₁|²` by `O(k⁴) ∫ |F₁|²`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section
namespace PolyaNeumann
variable {Ω : Set ℂ} {γ : ℝ → ℂ} {a : ℝ → ℂ}

/-- Cauchy–Schwarz on `[0, 2π]`: `(∫ |g|)² ≤ 2π ∫ |g|²`. -/
lemma sq_intervalIntegral_norm_le {g : ℝ → ℂ} (hg : Continuous g) :
    (∫ θ in (0:ℝ)..(2 * π), ‖g θ‖) ^ 2 ≤ 2 * π * ∫ θ in (0:ℝ)..(2 * π), ‖g θ‖ ^ 2 := by
  have h2π : (0:ℝ) < 2 * π := by positivity
  set S := ∫ θ in (0:ℝ)..(2 * π), ‖g θ‖ with hS
  set m := S / (2 * π) with hm
  have h1 : IntervalIntegrable (fun θ => ‖g θ‖ ^ 2) volume 0 (2 * π) :=
    (hg.norm.pow 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => 2 * m * ‖g θ‖) volume 0 (2 * π) :=
    (continuous_const.mul hg.norm).intervalIntegrable _ _
  have hnn : 0 ≤ ∫ θ in (0:ℝ)..(2 * π), (‖g θ‖ - m) ^ 2 :=
    intervalIntegral.integral_nonneg h2π.le fun θ _ => sq_nonneg _
  have hexp : ∫ θ in (0:ℝ)..(2 * π), (‖g θ‖ - m) ^ 2 =
      (∫ θ in (0:ℝ)..(2 * π), ‖g θ‖ ^ 2) - 2 * m * S + m ^ 2 * (2 * π) := by
    have : (fun θ => (‖g θ‖ - m) ^ 2) = fun θ => (‖g θ‖ ^ 2 - 2 * m * ‖g θ‖) + m ^ 2 := by
      funext θ; ring
    rw [this, intervalIntegral.integral_add (h1.sub h2) intervalIntegrable_const,
      intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp, hm] at hnn
  field_simp at hnn
  nlinarith

/-- `∫ |q| ≤ K ∫ |F₋₁ ∘ γ|`. -/
lemma integral_norm_herglotzQd_le (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) :
    ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖ ≤
      K * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a (-1) (γ θ)‖ := by
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by positivity)
    ((intervalIntegrable_of_norm_le hqm (fun θ => hqB θ) _ _).norm)
    ((continuous_const.mul ((continuous_herglotzCoeff ha k (-1)).comp
      hK.continuous).norm).intervalIntegrable _ _) fun θ _ => ?_
  rw [herglotzQd, norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hK) (norm_nonneg _)

lemma norm_herglotzQ_le (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖herglotzQ k a γ θ‖ ≤ ∫ t in (0:ℝ)..(2 * π), ‖herglotzQd k a γ t‖ := by
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  have hqi : ∀ b c, IntervalIntegrable (fun t => ‖herglotzQd k a γ t‖) volume b c := fun b c =>
    (intervalIntegrable_of_norm_le hqm (fun θ => hqB θ) _ _).norm
  rw [herglotzQ]
  refine (intervalIntegral.norm_integral_le_integral_norm hθ.1).trans ?_
  refine intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2
    (Eventually.of_forall fun t => norm_nonneg _) (hqi _ _)

/-- `|∫ conj(q) Q| ≤ (∫ |q|)²`. -/
lemma norm_integral_conj_herglotzQd_mul_le (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) :
    ‖∫ θ in (0:ℝ)..(2 * π), conj (herglotzQd k a γ θ) * herglotzQ k a γ θ‖ ≤
      (∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖) ^ 2 := by
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  set S := ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖
  have hqi : IntervalIntegrable (fun t => ‖herglotzQd k a γ t‖) volume 0 (2 * π) :=
    (intervalIntegrable_of_norm_le hqm (fun θ => hqB θ) _ _).norm
  refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
  calc ∫ θ in (0:ℝ)..(2 * π), ‖conj (herglotzQd k a γ θ) * herglotzQ k a γ θ‖
      ≤ ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖ * S := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo (by positivity) ?_ (hqi.mul_const _)
          fun θ hθ => ?_
        · have hQ : Continuous (herglotzQ k a γ) := by
            unfold herglotzQ
            exact intervalIntegral.continuous_primitive
              (fun b c => intervalIntegrable_of_norm_le hqm (fun θ => hqB θ) _ _) 0
          have := ((intervalIntegrable_conj' (intervalIntegrable_of_norm_le hqm
            (fun θ => hqB θ) 0 (2 * π))).mul_continuousOn hQ.continuousOn).norm
          simpa using this
        · rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (norm_herglotzQ_le ha k hK ⟨hθ.1.le, hθ.2.le⟩)
            (norm_nonneg _)
    _ = S ^ 2 := by rw [intervalIntegral.integral_mul_const]; ring

/-- With `c = i h_a(0)`: `∫ |G - c| ≤ ∫ |h_a| + 2π |k| ∫ |q|`. -/
lemma integral_norm_primitive_sub_le (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) :
    ∫ θ in (0:ℝ)..(2 * π), ‖(∫ s in (0:ℝ)..θ, herglotzConormal k a γ s) -
        Complex.I * herglotzCoeff k a 0 (γ 0)‖ ≤
      (∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a 0 (γ θ)‖) +
        2 * π * |k| * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖ := by
  obtain ⟨hgm, Bg, hgB⟩ := herglotzConormal_bounded ha k hK
  set S := ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖
  have hGc : Continuous fun θ => ‖(∫ s in (0:ℝ)..θ, herglotzConormal k a γ s) -
      Complex.I * herglotzCoeff k a 0 (γ 0)‖ :=
    ((intervalIntegral.continuous_primitive
      (fun b c => intervalIntegrable_of_norm_le hgm hgB _ _) 0).sub continuous_const).norm
  have hh : Continuous fun θ => ‖herglotzCoeff k a 0 (γ θ)‖ :=
    ((continuous_herglotzCoeff ha k 0).comp hK.continuous).norm
  calc _ ≤ ∫ θ in (0:ℝ)..(2 * π), (‖herglotzCoeff k a 0 (γ θ)‖ + |k| * S) := by
        refine intervalIntegral.integral_mono_on (by positivity) (hGc.intervalIntegrable _ _)
          ((hh.add continuous_const).intervalIntegrable _ _) fun θ hθ => ?_
        rw [primitive_herglotzConormal_eq ha k hK θ]
        have he : -Complex.I * (herglotzCoeff k a 0 (γ θ) - herglotzCoeff k a 0 (γ 0)) +
            k * herglotzQ k a γ θ - Complex.I * herglotzCoeff k a 0 (γ 0) =
            -Complex.I * herglotzCoeff k a 0 (γ θ) + k * herglotzQ k a γ θ := by ring
        rw [he]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_herglotzQ_le ha k hK hθ) (abs_nonneg _)
    _ = _ := by
        rw [intervalIntegral.integral_add (hh.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        ring

/-- Trace inequality for a Herglotz coefficient. -/
theorem trace_herglotzCoeff (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, IntervalIntegrable a volume 0 (2 * π) → ∀ (k : ℝ) (m : ℤ),
      ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a m (γ θ)‖ ^ 2 ≤
        C * ((∫ z in Ω, ‖herglotzCoeff k a m z‖ ^ 2) +
          k ^ 2 / 2 * ((∫ z in Ω, ‖herglotzCoeff k a (m + 1) z‖ ^ 2) +
            ∫ z in Ω, ‖herglotzCoeff k a (m - 1) z‖ ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := trace_sq_le hb hL hγ
  refine ⟨C, hC0, fun a ha k m => ?_⟩
  obtain ⟨⟨Kf, hKf⟩, hB⟩ := herglotzCoeff_bounded_lipschitz ha k m
  have h := hC _ Kf hKf _ hB
  simp only [gradSq_herglotzCoeff ha] at h
  rwa [integral_const_mul, integral_add (integrable_herglotzCoeff_sq hb ha k _)
    (integrable_herglotzCoeff_sq hb ha k _)] at h

/-- The numerical core of Lemma 8.5. -/
lemma schur_numeric {E A I0 Im1 Im2 T0 T1 S G C₁ CT CS K : ℝ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hC₁ : 0 ≤ C₁) (hCT : 0 ≤ CT) (hCS : 0 ≤ CS) (hA : 0 ≤ A) (hI0 : 0 ≤ I0) (hIm1 : 0 ≤ Im1)
    (hIm2 : 0 ≤ Im2)
    (hED : E * (6 * C₁ + 2 * (2 * π * K ^ 2 * (2 * CT * C₁)) +
      CS * (4 * π * (CT * (2 * C₁ + 1)) + 8 * π ^ 2 * (2 * π * K ^ 2 * (2 * CT * C₁))) + 1) ≤ 1)
    (hm0 : I0 ≤ C₁ * E * A) (hm12 : Im1 + Im2 ≤ C₁ * E ^ 2 * A)
    (hT0 : T0 ≤ CT * (I0 + E / 2 * (A + Im1))) (hT1 : T1 ≤ CT * (Im1 + E / 2 * (I0 + Im2)))
    (hS : S ^ 2 ≤ K ^ 2 * (2 * π * T1)) (hG : G ^ 2 ≤ 2 * (2 * π * T0) + 2 * (4 * π ^ 2 * E * S ^ 2)) :
    0 ≤ 2 * E * A - 6 * E * I0 - 2 * E * S ^ 2 - CS * E * G ^ 2 := by
  set b0 := CT * (2 * C₁ + 1) with hb0
  set cq := 2 * π * K ^ 2 * (2 * CT * C₁) with hcq
  set cG := 4 * π * b0 + 8 * π ^ 2 * cq with hcG
  have hb00 : 0 ≤ b0 := by positivity
  have hcq0 : 0 ≤ cq := by positivity
  have hcG0 : 0 ≤ cG := by positivity
  have hE2 : E ^ 2 ≤ E := by nlinarith
  have hE32 : E ^ 3 ≤ E ^ 2 := by nlinarith
  have hCA : 0 ≤ C₁ * A := by positivity
  have hEA : 0 ≤ E * A := by positivity
  have hCEA : 0 ≤ C₁ * E * A := by positivity
  have hCE2A : 0 ≤ C₁ * E ^ 2 * A := by positivity
  have hIm1b : Im1 ≤ C₁ * E ^ 2 * A := by linarith
  have hIm2b : Im2 ≤ C₁ * E ^ 2 * A := by linarith
  have hEIm1 : E * Im1 ≤ C₁ * E ^ 3 * A := by
    have := mul_le_mul_of_nonneg_left hIm1b hE.le
    linarith [show E * (C₁ * E ^ 2 * A) = C₁ * E ^ 3 * A by ring]
  have hEIm2 : E * Im2 ≤ C₁ * E ^ 3 * A := by
    have := mul_le_mul_of_nonneg_left hIm2b hE.le
    linarith [show E * (C₁ * E ^ 2 * A) = C₁ * E ^ 3 * A by ring]
  have hEI0 : E * I0 ≤ C₁ * E ^ 2 * A := by
    have := mul_le_mul_of_nonneg_left hm0 hE.le
    linarith [show E * (C₁ * E * A) = C₁ * E ^ 2 * A by ring]
  have h32 : C₁ * E ^ 3 * A ≤ C₁ * E ^ 2 * A := by
    have := mul_le_mul_of_nonneg_left hE32 hCA
    linarith [show C₁ * A * E ^ 3 = C₁ * E ^ 3 * A by ring,
      show C₁ * A * E ^ 2 = C₁ * E ^ 2 * A by ring]
  have h21 : C₁ * E ^ 2 * A ≤ C₁ * E * A := by
    have := mul_le_mul_of_nonneg_left hE2 hCA
    linarith [show C₁ * A * E ^ 2 = C₁ * E ^ 2 * A by ring, show C₁ * A * E = C₁ * E * A by ring]
  have hT0' : T0 ≤ b0 * E * A := by
    refine hT0.trans ?_
    have h : I0 + E / 2 * (A + Im1) ≤ (2 * C₁ + 1) * E * A := by
      have : E / 2 * (A + Im1) = E * A / 2 + E * Im1 / 2 := by ring
      rw [this]
      linarith
    calc CT * (I0 + E / 2 * (A + Im1)) ≤ CT * ((2 * C₁ + 1) * E * A) :=
          mul_le_mul_of_nonneg_left h hCT
      _ = b0 * E * A := by rw [hb0]; ring
  have hT1' : T1 ≤ 2 * CT * C₁ * E ^ 2 * A := by
    refine hT1.trans ?_
    have h : Im1 + E / 2 * (I0 + Im2) ≤ 2 * C₁ * E ^ 2 * A := by
      have : E / 2 * (I0 + Im2) = E * I0 / 2 + E * Im2 / 2 := by ring
      rw [this]
      linarith
    calc CT * (Im1 + E / 2 * (I0 + Im2)) ≤ CT * (2 * C₁ * E ^ 2 * A) :=
          mul_le_mul_of_nonneg_left h hCT
      _ = 2 * CT * C₁ * E ^ 2 * A := by ring
  have hSq : S ^ 2 ≤ cq * E ^ 2 * A := by
    refine hS.trans ?_
    calc K ^ 2 * (2 * π * T1) ≤ K ^ 2 * (2 * π * (2 * CT * C₁ * E ^ 2 * A)) := by gcongr
      _ = cq * E ^ 2 * A := by rw [hcq]; ring
  have hcqA : 0 ≤ cq * A := by positivity
  have hES : E * S ^ 2 ≤ cq * E * A := by
    have h1 := mul_le_mul_of_nonneg_left hSq hE.le
    have h2 : E * (cq * E ^ 2 * A) ≤ cq * E * A := by
      have := mul_le_mul_of_nonneg_left (hE32.trans hE2) hcqA
      linarith [show cq * A * E ^ 3 = E * (cq * E ^ 2 * A) by ring,
        show cq * A * E = cq * E * A by ring]
    linarith
  have hES2 : E * S ^ 2 ≤ cq * E ^ 2 * A := by
    have h1 := mul_le_mul_of_nonneg_left hSq hE.le
    have := mul_le_mul_of_nonneg_left hE32 hcqA
    linarith [show cq * A * E ^ 3 = E * (cq * E ^ 2 * A) by ring,
      show cq * A * E ^ 2 = cq * E ^ 2 * A by ring]
  have hGsq : G ^ 2 ≤ cG * E * A := by
    refine hG.trans ?_
    have h1 : 2 * (2 * π * T0) ≤ 4 * π * b0 * E * A := by
      have := mul_le_mul_of_nonneg_left hT0' (show (0:ℝ) ≤ 4 * π by positivity)
      linarith [show 4 * π * (b0 * E * A) = 4 * π * b0 * E * A by ring]
    have h2 : 2 * (4 * π ^ 2 * E * S ^ 2) ≤ 8 * π ^ 2 * cq * E * A := by
      have := mul_le_mul_of_nonneg_left hES (show (0:ℝ) ≤ 8 * π ^ 2 by positivity)
      linarith [show 8 * π ^ 2 * (E * S ^ 2) = 2 * (4 * π ^ 2 * E * S ^ 2) by ring,
        show 8 * π ^ 2 * (cq * E * A) = 8 * π ^ 2 * cq * E * A by ring]
    rw [hcG]; linarith [show (4 * π * b0 + 8 * π ^ 2 * cq) * E * A =
      4 * π * b0 * E * A + 8 * π ^ 2 * cq * E * A by ring]
  -- final
  have t1 : 6 * E * I0 ≤ 6 * C₁ * E ^ 2 * A := by linarith
  have t2 : 2 * E * S ^ 2 ≤ 2 * cq * E ^ 2 * A := by linarith
  have t3 : CS * E * G ^ 2 ≤ CS * cG * E ^ 2 * A := by
    have := mul_le_mul_of_nonneg_left hGsq (show 0 ≤ CS * E by positivity)
    linarith [show CS * E * (cG * E * A) = CS * cG * E ^ 2 * A by ring]
  have t4 : (6 * C₁ + 2 * cq + CS * cG) * (E * (E * A)) ≤ E * A := by
    have h := mul_le_mul_of_nonneg_right hED hEA
    linarith [mul_nonneg hE.le hEA]
  linarith

/-- **Lemma 8.5 on Herglotz data.** Fix a disc `B(z₁, r) ⊆ Ω`. For small `E > 0`, the Schur
complement is nonnegative on the Herglotz vector of every density whose wave has zero mean over
`Ω` and whose negative coefficients `F_{-j}` (`j ≥ 1`) vanish at `z₁`. -/
theorem herglotz_imSchur_nonneg (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) {z₁ : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ a (ha : IsDirDensity a),
        (∀ j : ℕ, 1 ≤ j → herglotzCoeff (Real.sqrt E) a (-(j : ℤ)) z₁ = 0) →
        ∫ z in Ω, herglotzCoeff (Real.sqrt E) a 0 z = 0 →
          0 ≤ imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨C₁, δ₁, hC₁, hδ₁, hmodes⟩ := herglotz_modes_small hb hL hr hball
  obtain ⟨CT, hCT0, htrace⟩ := trace_herglotzCoeff hb hL hγ
  obtain ⟨CS, δS, hδS, hS⟩ := imSchur_herglotzVec_sub_principal_le hb hL hγ
  have hCS'0 : 0 ≤ max CS 0 := le_max_right _ _
  obtain ⟨D, hD, hD0⟩ : ∃ D : ℝ, D = 6 * C₁ + 2 * (2 * π * (Kγ : ℝ) ^ 2 * (2 * CT * C₁)) +
      max CS 0 * (4 * π * (CT * (2 * C₁ + 1)) + 8 * π ^ 2 * (2 * π * (Kγ : ℝ) ^ 2 *
        (2 * CT * C₁))) + 1 ∧ 0 < D := ⟨_, rfl, by positivity⟩
  refine ⟨min (min 1 δ₁) (min δS (1 / D)), by positivity,
    fun E hE hEδ W hW a ha hz hmean => ?_⟩
  have hE1 : E ≤ 1 := (hEδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hEδ₁ : E ≤ δ₁ := (hEδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hEδS : E < δS := hEδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hED : E * D ≤ 1 := by
    have : E ≤ 1 / D := (hEδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    rwa [le_div_iff₀ hD0] at this
  rw [hD] at hED
  have hai := ha.intervalIntegrable
  have hk0 : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hk2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE.le
  have hk4 : Real.sqrt E ^ 4 = E ^ 2 := by
    rw [show Real.sqrt E ^ 4 = (Real.sqrt E ^ 2) ^ 2 by ring, hk2]
  obtain ⟨hm0, hm12⟩ := hmodes a ha (Real.sqrt E) (by rw [hk2]; exact hEδ₁) hz hmean
  rw [hk2] at hm0
  rw [hk4] at hm12
  have hT0 := htrace a hai (Real.sqrt E) 0
  have hT1 := htrace a hai (Real.sqrt E) (-1)
  norm_num at hT0 hT1
  rw [hk2] at hT0 hT1
  -- the boundary density `q`
  have hSq : (∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd (Real.sqrt E) a γ θ‖) ^ 2 ≤
      Kγ ^ 2 * (2 * π * ∫ θ in (0:ℝ)..(2 * π),
        ‖herglotzCoeff (Real.sqrt E) a (-1) (γ θ)‖ ^ 2) := by
    have h1 := integral_norm_herglotzQd_le hai (Real.sqrt E) hKγ (γ := γ)
    have h2 := sq_intervalIntegral_norm_le ((continuous_herglotzCoeff hai (Real.sqrt E) (-1)).comp
      hKγ.continuous)
    have hS0 : 0 ≤ ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd (Real.sqrt E) a γ θ‖ :=
      intervalIntegral.integral_nonneg (by positivity) fun _ _ => norm_nonneg _
    calc _ ≤ (Kγ * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a (-1) (γ θ)‖) ^ 2 :=
          pow_le_pow_left₀ hS0 h1 2
      _ = Kγ ^ 2 * (∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a (-1) (γ θ)‖) ^ 2 := by
          ring
      _ ≤ _ := by gcongr; exact h2
  -- the kernel term
  have hGsq : (∫ θ in (0:ℝ)..(2 * π), ‖(∫ s in (0:ℝ)..θ, herglotzConormal (Real.sqrt E) a γ s) -
      Complex.I * herglotzCoeff (Real.sqrt E) a 0 (γ 0)‖) ^ 2 ≤
      2 * (2 * π * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a 0 (γ θ)‖ ^ 2) +
        2 * (4 * π ^ 2 * E * (∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd (Real.sqrt E) a γ θ‖) ^ 2) := by
    have h1 := integral_norm_primitive_sub_le hai (Real.sqrt E) hKγ (γ := γ)
    have h2 : (∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a 0 (γ θ)‖) ^ 2 ≤
        2 * π * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a 0 (γ θ)‖ ^ 2 :=
      sq_intervalIntegral_norm_le ((continuous_herglotzCoeff hai (Real.sqrt E) 0).comp
        hKγ.continuous)
    rw [abs_of_nonneg hk0] at h1
    have hG0 : 0 ≤ ∫ θ in (0:ℝ)..(2 * π), ‖(∫ s in (0:ℝ)..θ,
        herglotzConormal (Real.sqrt E) a γ s) - Complex.I * herglotzCoeff (Real.sqrt E) a 0 (γ 0)‖ :=
      intervalIntegral.integral_nonneg (by positivity) fun _ _ => norm_nonneg _
    generalize (∫ θ in (0:ℝ)..(2 * π), ‖(∫ s in (0:ℝ)..θ,
        herglotzConormal (Real.sqrt E) a γ s) - Complex.I * herglotzCoeff (Real.sqrt E) a 0 (γ 0)‖)
      = G at h1 hG0 ⊢
    generalize (∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a 0 (γ θ)‖) = H at h1 h2
    generalize (∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd (Real.sqrt E) a γ θ‖) = S at h1 ⊢
    have h3 : G ^ 2 ≤ 2 * H ^ 2 + 2 * (2 * π * Real.sqrt E * S) ^ 2 := by
      have := pow_le_pow_left₀ hG0 h1 2
      nlinarith [sq_nonneg (H - 2 * π * Real.sqrt E * S)]
    have h4 : (2 * π * Real.sqrt E * S) ^ 2 = 4 * π ^ 2 * E * S ^ 2 := by
      rw [show (2 * π * Real.sqrt E * S) ^ 2 = 4 * π ^ 2 * Real.sqrt E ^ 2 * S ^ 2 by ring, hk2]
    linarith
  -- the principal part
  have hP : 2 * E * (∫ z in Ω, ‖herglotzCoeff (Real.sqrt E) a 1 z‖ ^ 2) -
      6 * E * (∫ z in Ω, ‖herglotzCoeff (Real.sqrt E) a 0 z‖ ^ 2) -
      2 * E * (∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd (Real.sqrt E) a γ θ‖) ^ 2 ≤
      herglotzPrincipal Ω γ (Real.sqrt E) a := by
    unfold herglotzPrincipal
    rw [hk2]
    have hint : ∫ z in Ω, (‖herglotzCoeff (Real.sqrt E) a 1 z‖ ^ 2 +
        2 * ‖herglotzCoeff (Real.sqrt E) a (-1) z‖ ^ 2 -
        3 * ‖herglotzCoeff (Real.sqrt E) a 0 z‖ ^ 2) =
        (∫ z in Ω, ‖herglotzCoeff (Real.sqrt E) a 1 z‖ ^ 2) +
        2 * (∫ z in Ω, ‖herglotzCoeff (Real.sqrt E) a (-1) z‖ ^ 2) -
        3 * ∫ z in Ω, ‖herglotzCoeff (Real.sqrt E) a 0 z‖ ^ 2 := by
      have i1 := integrable_herglotzCoeff_sq hb hai (Real.sqrt E) 1
      have i2 : Integrable (fun z => 2 * ‖herglotzCoeff (Real.sqrt E) a (-1) z‖ ^ 2)
          (volume.restrict Ω) := (integrable_herglotzCoeff_sq hb hai _ _).const_mul 2
      have i3 : Integrable (fun z => 3 * ‖herglotzCoeff (Real.sqrt E) a 0 z‖ ^ 2)
          (volume.restrict Ω) := (integrable_herglotzCoeff_sq hb hai _ _).const_mul 3
      have i12 : Integrable (fun z => ‖herglotzCoeff (Real.sqrt E) a 1 z‖ ^ 2 +
          2 * ‖herglotzCoeff (Real.sqrt E) a (-1) z‖ ^ 2) (volume.restrict Ω) := i1.add i2
      rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul,
        integral_const_mul]
    rw [hint]
    have hQ := norm_integral_conj_herglotzQd_mul_le hai (Real.sqrt E) hKγ (γ := γ)
    have him := (Complex.im_le_norm (∫ θ in (0:ℝ)..(2 * π),
      conj (herglotzQd (Real.sqrt E) a γ θ) * herglotzQ (Real.sqrt E) a γ θ)).trans hQ
    have hIm1 : 0 ≤ ∫ z in Ω, ‖herglotzCoeff (Real.sqrt E) a (-1) z‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    nlinarith
  -- the Schur complement
  have hSchur := hS E hE hEδS W hW a ha hmean
    (Complex.I * herglotzCoeff (Real.sqrt E) a 0 (γ 0))
  have hlow := (abs_le.mp hSchur).1
  have hCS : CS * E * (∫ θ in (0:ℝ)..(2 * π), ‖(∫ s in (0:ℝ)..θ,
      herglotzConormal (Real.sqrt E) a γ s) -
        Complex.I * herglotzCoeff (Real.sqrt E) a 0 (γ 0)‖) ^ 2 ≤
      max CS 0 * E * (∫ θ in (0:ℝ)..(2 * π), ‖(∫ s in (0:ℝ)..θ,
        herglotzConormal (Real.sqrt E) a γ s) -
          Complex.I * herglotzCoeff (Real.sqrt E) a 0 (γ 0)‖) ^ 2 := by
    gcongr; exact le_max_left _ _
  have hnum := schur_numeric hE hE1 hC₁.le hCT0 hCS'0 (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity) hED hm0 (by linarith) hT0 hT1 hSq hGsq
  linarith

end PolyaNeumann
