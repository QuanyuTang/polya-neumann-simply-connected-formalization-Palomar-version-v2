module

public import RequestProject.HerglotzSplit
public import RequestProject.SmallKernel

/-!
# The principal part of the Herglotz form

Write `T₀ g(θ) = ∫₀^θ g` for the Volterra operator with kernel `1` and `G = T₀ g_a` for the
primitive of the conormal trace. Along the boundary, `g_a = -i h_a' + k q`, where
`q = conj(γ') F₋₁(γ)` (so `k q = 2i ∂̄u_a(γ) conj(γ')`), hence `G = -i (h_a - h_a(0)) + k Q` with
`Q = ∫₀^θ q`. When `∫_Ω u_a = 0` (so that `G(L) = Q(L) = 0`), Green's formula gives the principal
part of the Herglotz form (`re_integral_herglotz_principal`):

  `Re ∫₀^L conj(g_a) (2 h_a + i (T₀ - T₀^*) g_a)
      = 2k² ∫_Ω (|F₁|² + 2|F₋₁|² − 3|F₀|²) − 2k² Im ∫₀^L conj(q) Q`,

that is `4 ∫_Ω |∇u_a|² + 8 ∫_Ω |∂̄u_a|² − 6k² ∫_Ω |u_a|²` up to the boundary term in `Q`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {a : ℝ → ℂ}

/-- The boundary density `q = conj(γ') F₋₁(γ)`. -/
def herglotzQd (k : ℝ) (a : ℝ → ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ)

/-- Its primitive `Q(θ) = ∫₀^θ q`. -/
def herglotzQ (k : ℝ) (a : ℝ → ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..θ, herglotzQd k a γ t

lemma herglotzQd_bounded (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) {K : NNReal}
    (hK : LipschitzWith K γ) :
    AEStronglyMeasurable (herglotzQd k a γ) volume ∧
      ∀ θ, ‖herglotzQd k a γ θ‖ ≤ K * ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖) := by
  refine ⟨?_, fun θ => ?_⟩
  · exact (Complex.continuous_conj.comp_aestronglyMeasurable
      (measurable_deriv γ).aestronglyMeasurable).mul
      ((continuous_herglotzCoeff ha k (-1)).comp hK.continuous).aestronglyMeasurable
  · rw [herglotzQd, norm_mul, Complex.norm_conj]
    exact mul_le_mul (norm_deriv_le_of_lipschitz hK) (norm_herglotzCoeff_le k _ _)
      (norm_nonneg _) K.2

/-- Along the boundary, `g_a = -i (u_a ∘ γ)' + k q` almost everywhere. -/
lemma herglotzConormal_ae_eq (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) :
    ∀ᵐ θ, herglotzConormal k a γ θ =
      -Complex.I * deriv (fun s => herglotzCoeff k a 0 (γ s)) θ + k * herglotzQd k a γ θ := by
  filter_upwards [hK.ae_differentiableAt] with θ hθ
  obtain ⟨h0, h0L⟩ := herglotzCoeff_hasFDerivAt' ha k 0 (γ θ)
  have hd : deriv (fun s => herglotzCoeff k a 0 (γ s)) θ =
      fderiv ℝ (herglotzCoeff k a 0) (γ θ) (deriv γ θ) :=
    (h0.comp_hasDerivAt θ hθ.hasDerivAt).deriv
  rw [hd, h0L, herglotzConormal_eq ha, herglotzQd]
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `G(θ) = ∫₀^θ g_a = -i (h_a(θ) - h_a(0)) + k Q(θ)`. -/
lemma primitive_herglotzConormal_eq (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) (θ : ℝ) :
    ∫ s in (0 : ℝ)..θ, herglotzConormal k a γ s =
      -Complex.I * (herglotzCoeff k a 0 (γ θ) - herglotzCoeff k a 0 (γ 0)) +
        k * herglotzQ k a γ θ := by
  obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k 0
  have hh : LipschitzWith (C * K) (fun s => herglotzCoeff k a 0 (γ s)) := hC.comp hK
  have hdi : IntervalIntegrable (deriv fun s => herglotzCoeff k a 0 (γ s)) volume 0 θ :=
    intervalIntegrable_of_norm_le (measurable_deriv _).aestronglyMeasurable
      (fun t => norm_deriv_le_of_lipschitz hh) 0 θ
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  have hqi : IntervalIntegrable (herglotzQd k a γ) volume 0 θ :=
    intervalIntegrable_of_norm_le hqm (fun t => hqB t) 0 θ
  rw [intervalIntegral.integral_congr_ae (g := fun s => -Complex.I *
      deriv (fun s => herglotzCoeff k a 0 (γ s)) s + k * herglotzQd k a γ s)
      ((herglotzConormal_ae_eq ha k hK).mono fun s hs _ => hs),
    intervalIntegral.integral_add (hdi.const_mul _) (hqi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_deriv_of_lipschitz hh, herglotzQ]

/-- Integration by parts against `Q`:
`∫₀^L conj(h') Q = conj(h(L)) Q(L) − ∫₀^L conj(h) q` for `h = u_a ∘ γ`. -/
lemma integral_conj_deriv_mul_herglotzQ (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (deriv (fun s => herglotzCoeff k a 0 (γ s)) θ) *
        herglotzQ k a γ θ =
      conj (herglotzCoeff k a 0 (γ (2 * π))) * herglotzQ k a γ (2 * π) -
        ∫ θ in (0 : ℝ)..(2 * π), conj (herglotzCoeff k a 0 (γ θ)) * herglotzQd k a γ θ := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k 0
  have hh : LipschitzWith (C * K) (fun s => herglotzCoeff k a 0 (γ s)) := hC.comp hK
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  set B := K * ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖)
  have hdm : AEStronglyMeasurable (fun θ => conj (deriv (fun s => herglotzCoeff k a 0 (γ s)) θ))
      (volume.restrict (Icc 0 (2 * π))) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (measurable_deriv _).aestronglyMeasurable)
  have key := integral_primitive_mul_eq h2π hqm.restrict hdm (Bf := B) (Bg := C * K)
    (fun t _ => hqB t) (fun t _ => by
      rw [Complex.norm_conj]; exact norm_deriv_le_of_lipschitz hh)
  have hin : ∀ t, ∫ s in t..(2 * π), conj (deriv (fun s => herglotzCoeff k a 0 (γ s)) s) =
      conj (herglotzCoeff k a 0 (γ (2 * π))) - conj (herglotzCoeff k a 0 (γ t)) := fun t => by
    rw [intervalIntegral_conj, integral_deriv_of_lipschitz hh, map_sub]
  have hl : ∫ θ in (0 : ℝ)..(2 * π), conj (deriv (fun s => herglotzCoeff k a 0 (γ s)) θ) *
        herglotzQ k a γ θ =
      ∫ s in (0 : ℝ)..(2 * π), (∫ t in (0 : ℝ)..s, herglotzQd k a γ t) *
        conj (deriv (fun s => herglotzCoeff k a 0 (γ s)) s) :=
    intervalIntegral.integral_congr fun θ _ => by rw [herglotzQ, mul_comm]
  have hqi : IntervalIntegrable (herglotzQd k a γ) volume 0 (2 * π) :=
    intervalIntegrable_of_norm_le hqm (fun t => hqB t) 0 (2 * π)
  have hci : IntervalIntegrable (fun t => herglotzQd k a γ t *
      conj (herglotzCoeff k a 0 (γ t))) volume 0 (2 * π) :=
    hqi.mul_continuousOn ((Complex.continuous_conj.comp
      ((continuous_herglotzCoeff ha k 0).comp hK.continuous)).continuousOn)
  rw [hl, key]
  simp_rw [hin, mul_sub]
  rw [intervalIntegral.integral_sub (hqi.mul_const _) hci, intervalIntegral.integral_mul_const,
    herglotzQ]
  congr 1
  · ring
  · exact intervalIntegral.integral_congr fun θ _ => by ring

/-- **Principal part of the Herglotz form.** If `∫_Ω u_a = 0`, then with `G = ∫₀^θ g_a`,

  `Re ∫₀^L conj(g_a) (2 h_a + 2i G) = 2k² ∫_Ω (|F₁|² + 2|F₋₁|² − 3|F₀|²) − 2k² Im ∫₀^L conj(q) Q`.

(Here `2G = (T₀ − T₀^*) g_a` since `∫₀^L g_a = 0`.) -/
theorem re_integral_herglotz_principal (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    (h0 : ∫ z in Ω, herglotzCoeff k a 0 z = 0) :
    (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzConormal k a γ θ) *
        (2 * herglotzWave k a (γ θ) +
          Complex.I * (2 * ∫ s in (0 : ℝ)..θ, herglotzConormal k a γ s))).re =
      2 * k ^ 2 * (∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + 2 * ‖herglotzCoeff k a (-1) z‖ ^ 2 -
        3 * ‖herglotzCoeff k a 0 z‖ ^ 2)) -
      2 * k ^ 2 * (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzQd k a γ θ) * herglotzQ k a γ θ).im := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  set g := herglotzConormal k a γ with hgdef
  set h : ℝ → ℂ := fun s => herglotzCoeff k a 0 (γ s) with hhdef
  set q := herglotzQd k a γ with hqdef
  set Q := herglotzQ k a γ with hQdef
  obtain ⟨hgm, Bg, hgB⟩ := herglotzConormal_bounded ha k hK
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  have hgi : IntervalIntegrable g volume 0 (2 * π) := intervalIntegrable_of_norm_le hgm hgB _ _
  have hcgi : IntervalIntegrable (fun θ => conj (g θ)) volume 0 (2 * π) :=
    intervalIntegrable_of_norm_le (Complex.continuous_conj.comp_aestronglyMeasurable hgm)
      (fun t => by rw [Complex.norm_conj]; exact hgB t) _ _
  have hhc : Continuous h := (continuous_herglotzCoeff ha k 0).comp hK.continuous
  have hQc : ContinuousOn Q (Icc 0 (2 * π)) :=
    continuousOn_primitive_of_bound h2π hqm.restrict (fun t _ => hqB t)
  -- vanishing of the endpoint values
  have hgint : ∫ θ in (0 : ℝ)..(2 * π), g θ = 0 := by
    rw [hgdef, integral_herglotzConormal hb hL hγ ha, h0, mul_zero]
  have hQL : Q (2 * π) = 0 := by
    rw [hQdef, herglotzQ]
    simp only [herglotzQd]
    rw [integral_conj_deriv_mul_herglotzCoeff_neg_one hb hL hγ ha, h0, mul_zero]
  have hG : ∀ θ, ∫ s in (0 : ℝ)..θ, g s = -Complex.I * (h θ - h 0) + k * Q θ := fun θ =>
    primitive_herglotzConormal_eq ha k hK θ
  -- the pieces
  have hR1 := integral_conj_herglotzConormal_mul_wave hb hL hγ ha k
  have hX : ∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * q θ =
      ((k * ∫ z in Ω, (‖herglotzCoeff k a (-1) z‖ ^ 2 - ‖herglotzCoeff k a 0 z‖ ^ 2) : ℝ) :
        ℂ) := integral_conj_wave_mul_herglotzQ' hb hL hγ ha k
  have hibp : ∫ θ in (0 : ℝ)..(2 * π), conj (deriv h θ) * Q θ =
      -∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * q θ := by
    rw [integral_conj_deriv_mul_herglotzQ ha k hK,
      show herglotzQ k a γ (2 * π) = 0 from hQL]
    ring
  have hcg0 : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) = 0 := by
    rw [intervalIntegral_conj, hgint, map_zero]
  -- `∫ conj(g) Q`
  have hgQ : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * Q θ =
      Complex.I * (∫ θ in (0 : ℝ)..(2 * π), conj (deriv h θ) * Q θ) +
        k * ∫ θ in (0 : ℝ)..(2 * π), conj (q θ) * Q θ := by
    obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k 0
    have hh : LipschitzWith (C * K) h := hC.comp hK
    have hdi : IntervalIntegrable (fun θ => conj (deriv h θ) * Q θ) volume 0 (2 * π) := by
      refine (intervalIntegrable_of_norm_le (B := C * K)
        (Complex.continuous_conj.comp_aestronglyMeasurable
        (measurable_deriv h).aestronglyMeasurable) (fun t => ?_) 0 (2 * π)).mul_continuousOn ?_
      · rw [Complex.norm_conj]; exact norm_deriv_le_of_lipschitz hh
      · rwa [uIcc_of_le h2π]
    have hqi : IntervalIntegrable (fun θ => conj (q θ) * Q θ) volume 0 (2 * π) := by
      refine (intervalIntegrable_of_norm_le
        (B := K * ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖))
        (Complex.continuous_conj.comp_aestronglyMeasurable
        hqm) (fun t => ?_) 0 (2 * π)).mul_continuousOn ?_
      · rw [Complex.norm_conj]; exact hqB t
      · rwa [uIcc_of_le h2π]
    have hae : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * Q θ = ∫ θ in (0 : ℝ)..(2 * π),
        (Complex.I * (conj (deriv h θ) * Q θ) + (k : ℂ) * (conj (q θ) * Q θ)) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [herglotzConormal_ae_eq ha k hK] with θ hθ _
      rw [hgdef, hθ, hhdef, hqdef]
      simp only [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hae, intervalIntegral.integral_add (hdi.const_mul _) (hqi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- the integrand
  have hpt : ∀ θ, conj (g θ) * (2 * herglotzWave k a (γ θ) +
      Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s)) =
      4 * (conj (g θ) * herglotzWave k a (γ θ)) - 2 * h 0 * conj (g θ) +
        2 * Complex.I * k * (conj (g θ) * Q θ) := fun θ => by
    rw [hG θ, herglotzWave_eq]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hi1 : IntervalIntegrable (fun θ => conj (g θ) * herglotzWave k a (γ θ)) volume 0
      (2 * π) := hcgi.mul_continuousOn
    (by
      have : herglotzWave k a = herglotzCoeff k a 0 := funext (herglotzWave_eq k a)
      rw [this]
      exact ((continuous_herglotzCoeff ha k 0).comp hK.continuous).continuousOn)
  have hi3 : IntervalIntegrable (fun θ => conj (g θ) * Q θ) volume 0 (2 * π) :=
    hcgi.mul_continuousOn (by rwa [uIcc_of_le h2π])
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((hi1.const_mul _).sub (hcgi.const_mul _))
      (hi3.const_mul _), intervalIntegral.integral_sub (hi1.const_mul _) (hcgi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcg0, hgQ, hibp, hR1, hX]
  -- the interior integrals
  set A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖
  have hFb : ∀ m z, ‖herglotzCoeff k a m z‖ ≤ A := fun m z => norm_herglotzCoeff_le k m z
  have hI : ∀ m, IntegrableOn (fun z => ‖herglotzCoeff k a m z‖ ^ 2) Ω := fun m =>
    integrableOn_of_continuous_bounded hb ((continuous_herglotzCoeff ha k m).norm.pow 2)
      (fun z => by
        rw [abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb m z) 2)
  have e1 : ∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + ‖herglotzCoeff k a (-1) z‖ ^ 2 -
      2 * ‖herglotzCoeff k a 0 z‖ ^ 2) = (∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2) +
      (∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2) - 2 * ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2 := by
    rw [integral_sub, integral_add, integral_const_mul]
    · exact hI 1
    · exact hI (-1)
    · exact (hI 1).add (hI (-1))
    · exact (hI 0).const_mul 2
  have e2 : ∫ z in Ω, (‖herglotzCoeff k a (-1) z‖ ^ 2 - ‖herglotzCoeff k a 0 z‖ ^ 2) =
      (∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2) - ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2 :=
    integral_sub (hI (-1)) (hI 0)
  have e3 : ∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + 2 * ‖herglotzCoeff k a (-1) z‖ ^ 2 -
      3 * ‖herglotzCoeff k a 0 z‖ ^ 2) = (∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2) +
      2 * (∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2) -
        3 * ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2 := by
    rw [integral_sub, integral_add, integral_const_mul, integral_const_mul]
    · exact hI 1
    · exact (hI (-1)).const_mul 2
    · exact (hI 1).add ((hI (-1)).const_mul 2)
    · exact (hI 0).const_mul 3
  rw [e1, e2, e3]
  set Y := ∫ θ in (0 : ℝ)..(2 * π), conj (q θ) * Q θ
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_im, Complex.zero_re,
    Complex.zero_im]
  ring

end PolyaNeumann

end
