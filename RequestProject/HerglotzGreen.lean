module

public import RequestProject.Herglotz
public import RequestProject.ReconGreen
public import RequestProject.ReconTrace

/-!
# Green's identity for Herglotz waves

For a bounded Lipschitz domain `Ω` with positively oriented boundary parametrization `γ`, the
complex Green formula `∮ F dz = 2i ∫_Ω ∂̄F` extends from compactly supported to bounded
Lipschitz functions (`integral_boundary_eq_dbar_of_bounded`). Applied to products of the
Herglotz coefficients `F_m` (with `∂F_m = -(ik/2) F_{m+1}`, `∂̄F_m = -(ik/2) F_{m-1}`) it gives
the energy identity for Herglotz waves

  `∫₀^{2π} conj(g_a) h_a dθ = (k²/2) ∫_Ω (|F₁|² + |F₋₁|² − 2|F₀|²)
                            = ∫_Ω (|∇u_a|² − k² |u_a|²)`

(`integral_conj_herglotzConormal_mul_wave`), where `h_a = u_a ∘ γ` and `g_a` is the conormal
trace.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- `∂̄F = β` when `DF(z) w = α w + β conj(w)`. -/
lemma dbar_eq_of_hasFDerivAt {F : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z α β : ℂ} (hF : HasFDerivAt F L z)
    (hL : ∀ w, L w = α * w + β * conj w) : dbar F z = β := by
  unfold dbar
  rw [hF.fderiv, hL, hL]
  simp only [map_one, mul_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Green's formula `∮ F dz = 2i ∫_Ω ∂̄F` for bounded Lipschitz `F`. -/
theorem integral_boundary_eq_dbar_of_bounded {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {F : ℂ → ℂ}
    {K : NNReal} (hF : LipschitzWith K F) {C : ℝ} (hC : ∀ z, ‖F z‖ ≤ C) :
    ∫ θ in (0 : ℝ)..(2 * π), F (γ θ) * deriv γ θ = 2 * Complex.I * ∫ z in Ω, dbar F z := by
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ closure Ω ⊆ ball (0 : ℂ) R := by
    obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : ℂ)
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  obtain ⟨χ, hχs, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  set χc : ℂ → ℂ := fun z => (χ z : ℂ) with hχc_def
  have hχcs : ContDiff ℝ (⊤ : ℕ∞) χc := Complex.ofRealCLM.contDiff.comp hχs
  have hχcc : HasCompactSupport χc := hχc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  obtain ⟨Kχ, hKχ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχcc hχcs (by simp)
  obtain ⟨Cχ, hCχ⟩ := hχcc.exists_bound_of_continuous hχcs.continuous
  obtain ⟨KG, hKG⟩ := lipschitzWith_mul_of_bounded hKχ hF hCχ hC
  set G : ℂ → ℂ := fun z => χc z * F z with hG
  have hGc : HasCompactSupport G := hχcc.mul_right
  have hgreen := integral_boundary_eq_dbar hb hL hγ hKG hGc
  have hone : ∀ z ∈ ball (0 : ℂ) R, G z = F z := fun z hz => by
    simp [hG, hχc_def, hχ1 z (ball_subset_closedBall hz)]
  have hbdry : ∀ θ ∈ Icc (0 : ℝ) (2 * π), G (γ θ) = F (γ θ) := fun θ hθ => by
    refine hone _ (hR ?_)
    have : γ θ ∈ frontier Ω := hγ.image ▸ mem_image_of_mem γ hθ
    exact frontier_subset_closure this
  have hint : ∀ z ∈ Ω, dbar G z = dbar F z := fun z hz => by
    have hev : G =ᶠ[𝓝 z] F :=
      eventually_of_mem (isOpen_ball.mem_nhds (hR (subset_closure hz))) hone
    simp only [dbar, hev.fderiv_eq]
  rw [← setIntegral_congr_fun hL.1.1.measurableSet hint, ← hgreen]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le (by positivity)] at hθ
  simp only [hbdry θ hθ]

/-- The derivative of a Herglotz coefficient in Wirtinger form. -/
lemma herglotzCoeff_hasFDerivAt' {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π))
    (k : ℝ) (m : ℤ) (z : ℂ) :
    HasFDerivAt (herglotzCoeff k a m) (fderiv ℝ (herglotzCoeff k a m) z) z ∧
      ∀ w, fderiv ℝ (herglotzCoeff k a m) z w =
        (-(Complex.I * k / 2) * herglotzCoeff k a (m + 1) z) * w +
          (-(Complex.I * k / 2) * herglotzCoeff k a (m - 1) z) * conj w := by
  refine ⟨(differentiable_herglotzCoeff ha k m z).hasFDerivAt, fun w => ?_⟩
  rw [fderiv_herglotzCoeff_apply ha]
  ring

/-- `∂̄` of `conj(F) G` for functions with Wirtinger derivatives. -/
lemma dbar_conj_mul {F G : ℂ → ℂ} {LF LG : ℂ →L[ℝ] ℂ} {z αF βF αG βG : ℂ}
    (hF : HasFDerivAt F LF z) (hFL : ∀ w, LF w = αF * w + βF * conj w)
    (hG : HasFDerivAt G LG z) (hGL : ∀ w, LG w = αG * w + βG * conj w) :
    dbar (fun x => conj (F x) * G x) z = conj (F z) * βG + G z * conj αF := by
  have hcF : HasFDerivAt (fun x => conj (F x))
      (Complex.conjCLE.toContinuousLinearMap.comp LF) z :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z hF
  have hP := hcF.mul hG
  refine dbar_eq_of_hasFDerivAt (α := conj (F z) * αG + G z * conj βF) hP fun w => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, hFL, hGL, smul_eq_mul]
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_add, map_mul,
    Complex.conj_conj]
  ring

/-- `∂̄` of `F conj(G)`. -/
lemma dbar_mul_conj {F G : ℂ → ℂ} {LF LG : ℂ →L[ℝ] ℂ} {z αF βF αG βG : ℂ}
    (hF : HasFDerivAt F LF z) (hFL : ∀ w, LF w = αF * w + βF * conj w)
    (hG : HasFDerivAt G LG z) (hGL : ∀ w, LG w = αG * w + βG * conj w) :
    dbar (fun x => F x * conj (G x)) z = F z * conj αG + conj (G z) * βF := by
  have h := dbar_conj_mul hG hGL hF hFL
  have e : (fun x => F x * conj (G x)) = fun x => conj (G x) * F x := by
    funext x; ring
  rw [e, h]; ring

/-- Bounded continuous functions are integrable on a bounded set. -/
lemma integrableOn_of_continuous_bounded {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) {f : ℂ → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ z, |f z| ≤ C) : IntegrableOn f Ω :=
  Measure.integrableOn_of_bounded (M := C) hb.measure_lt_top.ne
    hf.aestronglyMeasurable (Eventually.of_forall fun z => by simpa using hC z)

/-- `∂̄ (conj(F₋₁) F₀) = (ik/2)(|F₀|² − |F₋₁|²)`. -/
lemma dbar_herglotz_one {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    (z : ℂ) :
    dbar (fun x => conj (herglotzCoeff k a (-1) x) * herglotzCoeff k a 0 x) z =
      Complex.I * k / 2 *
        ((‖herglotzCoeff k a 0 z‖ ^ 2 - ‖herglotzCoeff k a (-1) z‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k (-1) z
  obtain ⟨h0, h0L⟩ := herglotzCoeff_hasFDerivAt' ha k 0 z
  rw [dbar_conj_mul h1 h1L h0 h0L]
  simp only [show (-1 : ℤ) + 1 = 0 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num]
  simp only [map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj']
  ring

/-- `∂̄ (F₁ conj(F₀)) = (ik/2)(|F₁|² − |F₀|²)`. -/
lemma dbar_herglotz_two {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    (z : ℂ) :
    dbar (fun x => herglotzCoeff k a 1 x * conj (herglotzCoeff k a 0 x)) z =
      Complex.I * k / 2 *
        ((‖herglotzCoeff k a 1 z‖ ^ 2 - ‖herglotzCoeff k a 0 z‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k 1 z
  obtain ⟨h0, h0L⟩ := herglotzCoeff_hasFDerivAt' ha k 0 z
  rw [dbar_mul_conj h1 h1L h0 h0L]
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num]
  simp only [map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj']
  ring

/-- **Energy identity for Herglotz waves.** With `F_m` the Herglotz coefficients
(`u_a = F₀`, `∂u_a = -(ik/2) F₁`, `∂̄u_a = -(ik/2) F₋₁`, so `|∇u_a|² = (k²/2)(|F₁|² + |F₋₁|²)`),

  `∫₀^{2π} conj(g_a) h_a = (k²/2) ∫_Ω (|F₁|² + |F₋₁|² − 2|F₀|²) = ∫_Ω (|∇u_a|² − k²|u_a|²)`. -/
theorem integral_conj_herglotzConormal_mul_wave {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {a : ℝ → ℂ}
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (herglotzConormal k a γ θ) * herglotzWave k a (γ θ) =
      ((k ^ 2 / 2 * ∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + ‖herglotzCoeff k a (-1) z‖ ^ 2 -
        2 * ‖herglotzCoeff k a 0 z‖ ^ 2) : ℝ) : ℂ) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  set F : ℤ → ℂ → ℂ := fun m => herglotzCoeff k a m with hF
  set A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ with hA
  have hFb : ∀ m z, ‖F m z‖ ≤ A := fun m z => norm_herglotzCoeff_le k m z
  have hFL : ∀ m, ∃ K : NNReal, LipschitzWith K (F m) := fun m => by
    obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k m
    exact ⟨C, hC⟩
  have hcF : ∀ m, ∃ K : NNReal, LipschitzWith K (fun z => conj (F m z)) := fun m => by
    obtain ⟨C, hC⟩ := hFL m
    exact ⟨1 * C, Complex.isometry_conj.lipschitz.comp hC⟩
  have hcFb : ∀ m z, ‖conj (F m z)‖ ≤ A := fun m z => by rw [Complex.norm_conj]; exact hFb m z
  obtain ⟨K1, hK1⟩ := lipschitzWith_mul_of_bounded (hcF (-1)).choose_spec (hFL 0).choose_spec
    (hcFb (-1)) (hFb 0)
  obtain ⟨K2, hK2⟩ := lipschitzWith_mul_of_bounded (hFL 1).choose_spec (hcF 0).choose_spec
    (hFb 1) (hcFb 0)
  set Φ₁ : ℂ → ℂ := fun z => conj (F (-1) z) * F 0 z with hΦ₁
  set Φ₂ : ℂ → ℂ := fun z => F 1 z * conj (F 0 z) with hΦ₂
  have hΦ₁b : ∀ z, ‖Φ₁ z‖ ≤ A * A := fun z => by
    simp only [hΦ₁, norm_mul]
    exact mul_le_mul (hcFb _ _) (hFb _ _) (norm_nonneg _) ((norm_nonneg _).trans (hFb 0 0))
  have hΦ₂b : ∀ z, ‖Φ₂ z‖ ≤ A * A := fun z => by
    simp only [hΦ₂, norm_mul]
    exact mul_le_mul (hFb _ _) (hcFb _ _) (norm_nonneg _) ((norm_nonneg _).trans (hFb 0 0))
  have g1 := integral_boundary_eq_dbar_of_bounded hb hL hγ hK1 hΦ₁b
  have g2 := integral_boundary_eq_dbar_of_bounded hb hL hγ hK2 hΦ₂b
  have hi1 := intervalIntegrable_comp_mul_deriv hKγ hK1.continuous
  have hi2 := intervalIntegrable_comp_mul_deriv hKγ hK2.continuous
  -- the boundary integrand
  have hpt : ∀ θ, conj (herglotzConormal k a γ θ) * herglotzWave k a (γ θ) =
      (k / 2 : ℂ) * (Φ₁ (γ θ) * deriv γ θ - conj (Φ₂ (γ θ) * deriv γ θ)) := fun θ => by
    rw [herglotzConormal_eq ha, herglotzWave_eq]
    simp only [hΦ₁, hΦ₂, hF, map_mul, map_sub, map_div₀, Complex.conj_ofReal, map_ofNat,
      Complex.conj_conj]
    ring
  have hconj : ∫ θ in (0 : ℝ)..(2 * π), conj (Φ₂ (γ θ) * deriv γ θ) =
      conj (∫ θ in (0 : ℝ)..(2 * π), Φ₂ (γ θ) * deriv γ θ) := by
    rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le
      (by positivity), integral_conj]
  have hi2c : IntervalIntegrable (fun θ => conj (Φ₂ (γ θ) * deriv γ θ)) volume 0 (2 * π) := by
    rw [intervalIntegrable_iff] at hi2 ⊢
    exact hi2.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      hi2.aestronglyMeasurable) (Eventually.of_forall fun θ => by simp)
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2c, hconj, g1, g2]
  -- the interior side
  have hd1 : ∀ z, dbar Φ₁ z = Complex.I * k / 2 *
      ((‖F 0 z‖ ^ 2 - ‖F (-1) z‖ ^ 2 : ℝ) : ℂ) := fun z => dbar_herglotz_one ha k z
  have hd2 : ∀ z, dbar Φ₂ z = Complex.I * k / 2 *
      ((‖F 1 z‖ ^ 2 - ‖F 0 z‖ ^ 2 : ℝ) : ℂ) := fun z => dbar_herglotz_two ha k z
  simp_rw [hd1, hd2]
  rw [integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  have hcont : ∀ m, Continuous fun z => ‖F m z‖ ^ 2 := fun m =>
    ((continuous_herglotzCoeff ha k m).norm).pow 2
  have hbd : ∀ m z, |‖F m z‖ ^ 2| ≤ A ^ 2 := fun m z => by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hFb m z) 2
  have hI : ∀ m, IntegrableOn (fun z => ‖F m z‖ ^ 2) Ω := fun m =>
    integrableOn_of_continuous_bounded hb (hcont m) (hbd m)
  have hR : ∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + ‖herglotzCoeff k a (-1) z‖ ^ 2 -
        2 * ‖herglotzCoeff k a 0 z‖ ^ 2) =
      (∫ z in Ω, ‖F 1 z‖ ^ 2) + (∫ z in Ω, ‖F (-1) z‖ ^ 2) - 2 * ∫ z in Ω, ‖F 0 z‖ ^ 2 := by
    change ∫ z in Ω, (‖F 1 z‖ ^ 2 + ‖F (-1) z‖ ^ 2 - 2 * ‖F 0 z‖ ^ 2) = _
    rw [integral_sub, integral_add, integral_const_mul]
    · exact hI 1
    · exact hI (-1)
    · exact (hI 1).add (hI (-1))
    · exact (hI 0).const_mul 2
  rw [integral_sub (hI 0) (hI (-1)), integral_sub (hI 1) (hI 0), hR]
  simp only [map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end PolyaNeumann

end
