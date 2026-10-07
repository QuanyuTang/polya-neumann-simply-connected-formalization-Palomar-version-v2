module

public import RequestProject.HerglotzGreen

/-!
# Boundary integrals of Herglotz coefficients

Consequences of the complex Green formula for the Herglotz coefficients `F_m` on a bounded
Lipschitz domain with positively oriented boundary parametrization `γ` (`c = -ik/2`,
`∂F_m = c F_{m+1}`, `∂̄F_m = c F_{m-1}`):

* `∫₀^{2π} conj(γ') F₋₁(γ) = -k ∫_Ω F₀` and `∫₀^{2π} γ' F₁(γ) = k ∫_Ω F₀`;
* the total conormal flux `∫₀^{2π} g_a = -k² ∫_Ω u_a`;
* `∫₀^{2π} conj(F₀(γ)) conj(γ') F₋₁(γ) = k ∫_Ω (|F₋₁|² − |F₀|²)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {a : ℝ → ℂ}

/-- `∂̄ conj(F) = conj α` when `DF(z) w = α w + β conj(w)`. -/
lemma dbar_conj_of_hasFDerivAt {F : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z α β : ℂ}
    (hF : HasFDerivAt F L z) (hL : ∀ w, L w = α * w + β * conj w) :
    dbar (fun x => conj (F x)) z = conj α := by
  have hcF : HasFDerivAt (fun x => conj (F x))
      (Complex.conjCLE.toContinuousLinearMap.comp L) z :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z hF
  refine dbar_eq_of_hasFDerivAt (α := conj β) hcF fun w => ?_
  simp only [ContinuousLinearMap.comp_apply, hL, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_add, map_mul, Complex.conj_conj]
  ring

/-- Herglotz coefficients are bounded Lipschitz functions. -/
lemma herglotzCoeff_bounded_lipschitz {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π))
    (k : ℝ) (m : ℤ) :
    (∃ K : NNReal, LipschitzWith K (herglotzCoeff k a m)) ∧
      ∀ z, ‖herglotzCoeff k a m z‖ ≤ (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ :=
  ⟨lipschitzWith_herglotzCoeff ha k m, fun z => norm_herglotzCoeff_le k m z⟩

lemma integrableOn_herglotzCoeff (hb : Bornology.IsBounded Ω) {a : ℝ → ℂ}
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ) :
    IntegrableOn (herglotzCoeff k a m) Ω :=
  Measure.integrableOn_of_bounded (M := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖)
    hb.measure_lt_top.ne (continuous_herglotzCoeff ha k m).aestronglyMeasurable
    (Eventually.of_forall fun z => norm_herglotzCoeff_le k m z)

/-- `∫₀^{2π} γ' F₁(γ) = k ∫_Ω F₀`. -/
lemma integral_herglotzCoeff_one_mul_deriv (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), herglotzCoeff k a 1 (γ θ) * deriv γ θ =
      (k : ℂ) * ∫ z in Ω, herglotzCoeff k a 0 z := by
  obtain ⟨⟨K, hK⟩, hB⟩ := herglotzCoeff_bounded_lipschitz ha k 1
  rw [integral_boundary_eq_dbar_of_bounded hb hL hγ hK hB]
  have hd : ∀ z, dbar (herglotzCoeff k a 1) z =
      -(Complex.I * k / 2) * herglotzCoeff k a 0 z := fun z => by
    obtain ⟨h1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k 1 z
    rw [dbar_eq_of_hasFDerivAt h1 h1L]
    norm_num
  simp_rw [hd]
  rw [integral_const_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `∫₀^{2π} conj(γ') F₋₁(γ) = -k ∫_Ω F₀`. -/
lemma integral_conj_deriv_mul_herglotzCoeff_neg_one (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) =
      -(k : ℂ) * ∫ z in Ω, herglotzCoeff k a 0 z := by
  obtain ⟨⟨K, hK⟩, hB⟩ := herglotzCoeff_bounded_lipschitz ha k (-1)
  have hK' : LipschitzWith (1 * K) (fun z => conj (herglotzCoeff k a (-1) z)) :=
    Complex.isometry_conj.lipschitz.comp hK
  have hB' : ∀ z, ‖conj (herglotzCoeff k a (-1) z)‖ ≤
      (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ := fun z => by
    rw [Complex.norm_conj]; exact hB z
  have hg := integral_boundary_eq_dbar_of_bounded hb hL hγ hK' hB'
  have hd : ∀ z, dbar (fun x => conj (herglotzCoeff k a (-1) x)) z =
      conj (-(Complex.I * k / 2) * herglotzCoeff k a 0 z) := fun z => by
    obtain ⟨h1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k (-1) z
    rw [dbar_conj_of_hasFDerivAt h1 h1L]
    norm_num
  simp_rw [hd] at hg
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have e : ∫ θ in (0 : ℝ)..(2 * π), conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) =
      conj (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzCoeff k a (-1) (γ θ)) * deriv γ θ) := by
    rw [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le h2π,
      ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [e, hg, integral_conj, map_mul, Complex.conj_conj, integral_const_mul]
  simp only [map_mul, map_ofNat, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Total conormal flux.** `∫₀^{2π} g_a = -k² ∫_Ω u_a`. -/
theorem integral_herglotzConormal (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), herglotzConormal k a γ θ =
      -((k : ℂ) ^ 2) * ∫ z in Ω, herglotzCoeff k a 0 z := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hi1 : IntervalIntegrable (fun θ => conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ))
      volume 0 (2 * π) := by
    have h := intervalIntegrable_comp_mul_deriv hKγ
      (Complex.continuous_conj.comp (continuous_herglotzCoeff ha k (-1)))
    rw [intervalIntegrable_iff] at h ⊢
    refine h.norm.mono' ?_ (Eventually.of_forall fun θ => by simp [mul_comm])
    refine (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable).congr ?_
    exact Eventually.of_forall fun θ => by simp [mul_comm]
  have hi2 := intervalIntegrable_comp_mul_deriv hKγ (continuous_herglotzCoeff ha k 1)
  have hpt : ∀ θ, herglotzConormal k a γ θ = (k / 2 : ℂ) *
      (conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) -
        herglotzCoeff k a 1 (γ θ) * deriv γ θ) := fun θ => by
    rw [herglotzConormal_eq ha]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2,
    integral_conj_deriv_mul_herglotzCoeff_neg_one hb hL hγ ha,
    integral_herglotzCoeff_one_mul_deriv hb hL hγ ha]
  ring

/-- `∫₀^{2π} conj(F₀(γ)) conj(γ') F₋₁(γ) = k ∫_Ω (|F₋₁|² − |F₀|²)`. -/
theorem integral_conj_wave_mul_herglotzQ' (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (herglotzCoeff k a 0 (γ θ)) *
        (conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ)) =
      ((k * ∫ z in Ω, (‖herglotzCoeff k a (-1) z‖ ^ 2 - ‖herglotzCoeff k a 0 z‖ ^ 2) : ℝ) :
        ℂ) := by
  set F : ℤ → ℂ → ℂ := fun m => herglotzCoeff k a m with hF
  set A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ with hA
  have hFb : ∀ m z, ‖F m z‖ ≤ A := fun m z => norm_herglotzCoeff_le k m z
  obtain ⟨K0, hK0⟩ := lipschitzWith_herglotzCoeff ha k 0
  obtain ⟨K1, hK1⟩ := lipschitzWith_herglotzCoeff ha k (-1)
  have hK1' : LipschitzWith (1 * K1) (fun z => conj (F (-1) z)) :=
    Complex.isometry_conj.lipschitz.comp hK1
  have hcb : ∀ z, ‖conj (F (-1) z)‖ ≤ A := fun z => by rw [Complex.norm_conj]; exact hFb _ _
  obtain ⟨KΦ, hKΦ⟩ := lipschitzWith_mul_of_bounded hK0 hK1' (hFb 0) hcb
  set Φ : ℂ → ℂ := fun z => F 0 z * conj (F (-1) z) with hΦ
  have hΦb : ∀ z, ‖Φ z‖ ≤ A * A := fun z => by
    simp only [hΦ, norm_mul]
    exact mul_le_mul (hFb _ _) (hcb _) (norm_nonneg _) ((norm_nonneg _).trans (hFb 0 0))
  have hg := integral_boundary_eq_dbar_of_bounded hb hL hγ hKΦ hΦb
  have hd : ∀ z, dbar Φ z = Complex.I * k / 2 *
      ((‖F 0 z‖ ^ 2 - ‖F (-1) z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    obtain ⟨h0, h0L⟩ := herglotzCoeff_hasFDerivAt' ha k 0 z
    obtain ⟨h1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k (-1) z
    rw [dbar_mul_conj h0 h0L h1 h1L]
    simp only [show (-1 : ℤ) + 1 = 0 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num]
    simp only [map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    push_cast
    rw [← Complex.mul_conj', ← Complex.mul_conj']
    ring
  simp_rw [hd] at hg
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have e : ∫ θ in (0 : ℝ)..(2 * π), conj (F 0 (γ θ)) * (conj (deriv γ θ) * F (-1) (γ θ)) =
      conj (∫ θ in (0 : ℝ)..(2 * π), Φ (γ θ) * deriv γ θ) := by
    rw [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le h2π,
      ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hΦ, map_mul, Complex.conj_conj]
    ring
  have hcont : ∀ m, Continuous fun z => ‖F m z‖ ^ 2 := fun m =>
    ((continuous_herglotzCoeff ha k m).norm).pow 2
  have hbd : ∀ m z, |‖F m z‖ ^ 2| ≤ A ^ 2 := fun m z => by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hFb m z) 2
  have hI : ∀ m, IntegrableOn (fun z => ‖F m z‖ ^ 2) Ω := fun m =>
    integrableOn_of_continuous_bounded hb (hcont m) (hbd m)
  change ∫ θ in (0 : ℝ)..(2 * π), conj (F 0 (γ θ)) * (conj (deriv γ θ) * F (-1) (γ θ)) = _
  rw [e, hg, integral_const_mul, integral_complex_ofReal, integral_sub (hI 0) (hI (-1)),
    integral_sub (hI (-1)) (hI 0)]
  simp only [map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end PolyaNeumann

end
