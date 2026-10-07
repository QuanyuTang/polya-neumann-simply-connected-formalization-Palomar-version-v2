module

public import RequestProject.SchurKernel

/-!
# The Schur complement on Herglotz data: principal part plus an `O(E)` kernel term

Combining the Schur complement on Herglotz data (`imSchur_herglotzVec`), the splitting of the
Volterra part (`re_volterra_sub_schur_eq`), the principal part computed by Green's formula
(`re_integral_herglotz_principal`) and the kernel estimate (`norm_schurKernel_form_le`), we get,
for a density `a` whose Herglotz wave has zero mean over `Ω` and wave number `k = √E`:

  `C(v_a) = 2k² ∫_Ω (|F₁|² + 2|F₋₁|² − 3|F₀|²) − 2k² Im ∫₀^L conj(q) Q + R`,

with `|R| ≤ C E (∫₀^L |G − c|)²` for every constant `c`, uniformly for small `E > 0`
(`imSchur_herglotzVec_sub_principal_le`). Here `G = ∫₀^θ g_a` is the primitive of the conormal
trace.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace Interval

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- The principal part `2k² ∫_Ω (|F₁|² + 2|F₋₁|² − 3|F₀|²) − 2k² Im ∫₀^L conj(q) Q` of the Schur
complement on Herglotz data. -/
def herglotzPrincipal (Ω : Set ℂ) (γ : ℝ → ℂ) (k : ℝ) (a : ℝ → ℂ) : ℝ :=
  2 * k ^ 2 * (∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + 2 * ‖herglotzCoeff k a (-1) z‖ ^ 2 -
    3 * ‖herglotzCoeff k a 0 z‖ ^ 2)) -
  2 * k ^ 2 * (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzQd k a γ θ) * herglotzQ k a γ θ).im

/-- **Exact splitting.** If `∫_Ω u_a = 0` and `a_E ≠ 0`, the Schur complement on Herglotz data
is the principal part plus the corrected kernel form. -/
theorem imSchur_herglotzVec_eq (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (ha0 : smallA W ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a)
    (h0 : ∫ z in Ω, herglotzCoeff (Real.sqrt E) a 0 z = 0) :
    imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) =
      herglotzPrincipal Ω γ (Real.sqrt E) a +
        (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzConormal (Real.sqrt E) a γ θ) *
          ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s *
            herglotzConormal (Real.sqrt E) a γ s).re := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hai := ha.intervalIntegrable
  obtain ⟨hgm, Bg, hgB⟩ := herglotzConormal_bounded hai (Real.sqrt E) hK
  have hG : ∫ θ in (0 : ℝ)..(2 * π), herglotzConormal (Real.sqrt E) a γ θ = 0 := by
    rw [integral_herglotzConormal hb hL hγ hai, h0, mul_zero]
  have hgi : IntervalIntegrable (herglotzConormal (Real.sqrt E) a γ) volume 0 (2 * π) :=
    intervalIntegrable_of_norm_le hgm hgB _ _
  have hhc : ContinuousOn (fun θ => herglotzWave (Real.sqrt E) a (γ θ)) (uIcc 0 (2 * π)) := by
    have : (fun θ => herglotzWave (Real.sqrt E) a (γ θ)) =
        fun θ => herglotzCoeff (Real.sqrt E) a 0 (γ θ) := by
      funext θ; rw [herglotzWave_eq]
    rw [this]
    exact ((continuous_herglotzCoeff hai _ 0).comp hK.continuous).continuousOn
  have hh : IntervalIntegrable (fun θ => conj (herglotzConormal (Real.sqrt E) a γ θ) *
      herglotzWave (Real.sqrt E) a (γ θ)) volume 0 (2 * π) :=
    (intervalIntegrable_conj' hgi).mul_continuousOn hhc
  rw [imSchur_herglotzVec hK hclosed hW ha, herglotzForm,
    re_volterra_sub_schur_eq hK hE hW ha0 hgm hgB hG hh,
    re_integral_herglotz_principal hb hL hγ hai _ h0, herglotzPrincipal]

/-- Quantitative form of Lemma 8.2: `a_E ≤ -|Ω| E` for small `E > 0`. -/
theorem smallA_le_neg (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      smallA W ≤ -((volume Ω).toReal * E) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨C, hC0, hC⟩ := smallA_approx hK
  set v := (volume Ω).toReal with hv
  have hvpos : 0 < v := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  have harea : ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ = 2 * v := by
    rw [integral_areaDensity_eq hK hclosed]; exact hγ.area
  refine ⟨min 1 ((v / (C + 1)) ^ 2), lt_min one_pos (by positivity), min_le_left _ _,
    fun E hE hEδ W hW => ?_⟩
  have hE1 : E ≤ 1 := (hEδ.trans_le (min_le_left _ _)).le
  have hE2 : E < (v / (C + 1)) ^ 2 := hEδ.trans_le (min_le_right _ _)
  have hs : Real.sqrt E < v / (C + 1) := by
    rw [show v / (C + 1) = Real.sqrt ((v / (C + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt hE.le hE2
  have hs' : (C + 1) * Real.sqrt E < v := by
    rw [lt_div_iff₀ (by positivity)] at hs; linarith
  have h := hC E hE.le hE1 W hW
  rw [harea] at h
  have h2 := (abs_le.mp h).2
  have hsq := Real.sqrt_nonneg E
  nlinarith [mul_lt_mul_of_pos_left hs' hE]

/-- **The Schur complement on Herglotz data, up to `O(E)`.** For small `E > 0`, if the Herglotz
wave of `a` has zero mean over `Ω`, then for every constant `c`

  `|C(v_a) − herglotzPrincipal| ≤ C E (∫₀^L |G − c|)²`,

where `G(θ) = ∫₀^θ g_a` is the primitive of the conormal trace. -/
theorem imSchur_herglotzVec_sub_principal_le (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ a (ha : IsDirDensity a), ∫ z in Ω, herglotzCoeff (Real.sqrt E) a 0 z = 0 → ∀ c : ℂ,
        |imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) -
            herglotzPrincipal Ω γ (Real.sqrt E) a| ≤
          C * E * (∫ θ in (0 : ℝ)..(2 * π),
            ‖(∫ s in (0 : ℝ)..θ, herglotzConormal (Real.sqrt E) a γ s) - c‖) ^ 2 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨δ, hδ, hδ1, hA⟩ := smallA_le_neg hb hL hγ
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_smallBDer_le hK
  set v := (volume Ω).toReal with hv
  have hvpos : 0 < v := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  refine ⟨K * (shiftConst * K) + C₁ * C₁ / v, δ, hδ,
    fun E hE hEδ W hW a ha h0 c => ?_⟩
  have hE1 : E ≤ 1 := (hEδ.trans_le hδ1).le
  have hAE := hA E hE hEδ W hW
  have hApos : v * E ≤ |smallA W| := by
    rw [abs_of_neg (by nlinarith)]; linarith
  have ha0 : smallA W ≠ 0 := by intro h; rw [h] at hAE; nlinarith
  obtain ⟨hgm, Bg, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  have hG : ∫ θ in (0 : ℝ)..(2 * π), herglotzConormal (Real.sqrt E) a γ θ = 0 := by
    rw [integral_herglotzConormal hb hL hγ ha.intervalIntegrable, h0, mul_zero]
  rw [imSchur_herglotzVec_eq hb hL hγ hE.le hW ha0 ha h0, add_sub_cancel_left]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_schurKernel_form_le hK hE.le hW ha0 (hC₁ E hE.le hE1 W hW) hgm hgB hG c).trans ?_
  gcongr
  have hB : C₁ * E * (C₁ * E) / |smallA W| ≤ C₁ * C₁ / v * E := by
    rw [div_le_iff₀ (abs_pos.mpr ha0)]
    calc C₁ * E * (C₁ * E) = C₁ * C₁ / v * E * (v * E) := by field_simp
      _ ≤ C₁ * C₁ / v * E * |smallA W| := by gcongr
  nlinarith

end PolyaNeumann
