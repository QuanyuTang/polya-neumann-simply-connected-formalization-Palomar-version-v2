module

public import RequestProject.CurveContinuity

/-!
# Energy derivative of the monodromy (Lemma 4.7, curvature formula)

For a closed Lipschitz curve `γ` and `E > 0`, the endpoint `V_E = W_E(L)` of the transport is
differentiable in `E` (in operator norm), with
`V_E^* ∂_E V_E = -i Q_E`, `Q_E = (1/4) ∫₀^L b W_E^* D_N W_E dθ`,
where `b = Im(conj(γ - γ(0)) γ')` is the signed area density.

The proof uses the variation identity of `CurveContinuity.lean` for the same curve at two
energies `E, E'`: with `G = coeffOf 1 (γ - γ(0))` and `C₁ = coeffOf 1 γ'`,
`V_{E'}^* V_E - 1 = (√E - √E') ∫₀^L W_{E'}^* (√E' C₁ G - √E G C₁) W_E`,
together with the commutator identity `[C₁, G] = -(i/2) b D_N` (from Lemma 4.2).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- The signed area density `b(θ) = Im(conj(γ(θ) - γ(0)) γ'(θ))`; for a positively oriented
Jordan parametrization `∫₀^L b = 2|Ω|`. -/
def areaDensity (γ : ℝ → ℂ) (θ : ℝ) : ℝ := (conj (γ θ - γ 0) * deriv γ θ).im

/-- The curvature operator `Q_E = (1/4) ∫₀^L b W^* D_N W dθ`. -/
def curvatureOp (γ : ℝ → ℂ) (W : ℝ → Ell2 →L[ℂ] Ell2) : Ell2 →L[ℂ] Ell2 :=
  (1 / 4 : ℝ) • ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ • (star (W θ) * diagN * W θ)

lemma coeffOf_eq_sqrt_smul (E : ℝ) (z : ℂ) : coeffOf E z = Real.sqrt E • coeffOf 1 z := by
  unfold coeffOf
  rw [Real.sqrt_one, real_smul_eq_coe_smul_clm, smul_smul]
  congr 1
  push_cast
  ring

/-- The commutator identity `[C₁(a), C₁(b)] = -(i/2) Im(a conj b) D_N`. -/
lemma coeffOf_one_commutator (a b : ℂ) :
    coeffOf 1 a * coeffOf 1 b - coeffOf 1 b * coeffOf 1 a =
      (-(Complex.I / 2) * ((a * conj b).im : ℂ)) • diagN := by
  have hD := shift_commutator
  set S := shiftN
  set T := ContinuousLinearMap.adjoint shiftN
  have him : ((a * conj b).im : ℂ) = (a * conj b - conj a * b) / (2 * Complex.I) := by
    rw [Complex.im_eq_sub_conj]; simp [mul_comm]
  rw [him, ← hD]
  unfold coeffOf
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one, add_mul, mul_add,
    smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  match_scalars <;> field_simp <;> ring_nf <;> simp [Complex.I_sq]

lemma norm_transportCoeff_le_const {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (E s : ℝ) :
    ‖transportCoeff γ E s‖ ≤ Real.sqrt E * shiftConst * K := by
  rw [transportCoeff_eq_coeffOf]
  refine (norm_coeffOf_le E _).trans ?_
  have := norm_deriv_le_of_lipschitz hK (x₀ := s)
  have := shiftConst_nonneg
  gcongr

/-- Uniform continuity of the transport in the energy:
`‖W_{E'}(θ) - W_E(θ)‖ ≤ |√E - √E'| κ R (1 + L (√E' + √E) κ K)` on `[0, L]`. -/
lemma norm_transport_sub_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖W' θ - W θ‖ ≤ |Real.sqrt E - Real.sqrt E'| * shiftConst * R *
      (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K)) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have hκ := shiftConst_nonneg
  set ε := |Real.sqrt E - Real.sqrt E'| * shiftConst * R with hεdef
  set F : ℝ → Ell2 →L[ℂ] Ell2 := fun θ => coeffOf E (γ θ - γ 0) - coeffOf E' (γ θ - γ 0)
    with hF
  have hFL : LipschitzOnWith _ F (Icc 0 (2 * π)) :=
    ((lipschitzWith_coeffOf hK E (γ 0)).sub (lipschitzWith_coeffOf hK E' (γ 0))).lipschitzOnWith
  have hFd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) →
      HasDerivAt F (transportCoeff γ E θ - transportCoeff γ E' θ) θ := by
    filter_upwards [hK.ae_differentiableAt (μ := volume)] with θ h1 _
    exact (hasDerivAt_coeffOf h1.hasDerivAt E (γ 0)).sub
      (hasDerivAt_coeffOf h1.hasDerivAt E' (γ 0))
  have hF0 : F 0 = 0 := by simp [hF, coeffOf_zero]
  have hFb : ∀ s ∈ Icc 0 (2 * π), ‖F s‖ ≤ ε := by
    intro s hs
    refine (norm_coeffOf_sub_coeffOf_le E E' _).trans ?_
    rw [hεdef]
    gcongr
    exact hR s hs
  have hvar := volterra_variation_at (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2 (transportCoeff_aestronglyMeasurable γ E')
    (transportCoeff_norm_le γ E' hK) (transportCoeff_star γ E') hW'.1 hW'.2 hπ hFL hFd hF0 θ hθ
  have hsub : Icc 0 θ ⊆ Icc 0 (2 * π) := Icc_subset_Icc le_rfl hθ.2
  have hint := norm_volterra_variation_le (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_aestronglyMeasurable γ E')
    (transportCoeff_norm_le γ E' hK) hθ.1 (fun s hs => hFb s (hsub hs))
    (fun s hs => norm_le_one_of_mem_unitary (transport_mem_unitary hK hW (hsub hs)))
    (fun s hs => norm_le_one_of_mem_unitary
      (Unitary.star_mem (transport_mem_unitary hK hW' (hsub hs))))
  have hU := transport_mem_unitary hK hW hθ
  have hU' := transport_mem_unitary hK hW' hθ
  have hn1 : ‖W θ‖ ≤ 1 := norm_le_one_of_mem_unitary hU
  have hn1' : ‖W' θ‖ ≤ 1 := norm_le_one_of_mem_unitary hU'
  have hn1s : ‖star (W' θ)‖ ≤ 1 := norm_le_one_of_mem_unitary (Unitary.star_mem hU')
  have hcoef : ∫ s in (0 : ℝ)..θ,
      (‖transportCoeff γ E' s‖ + ‖transportCoeff γ E s‖) ≤
      2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K) := by
    calc ∫ s in (0 : ℝ)..θ, (‖transportCoeff γ E' s‖ + ‖transportCoeff γ E s‖)
        ≤ ∫ s in (0 : ℝ)..θ, ((Real.sqrt E' + Real.sqrt E) * shiftConst * K) := by
          refine intervalIntegral.integral_mono_on hθ.1 ?_ intervalIntegrable_const
            fun s _ => ?_
          · exact (intervalIntegrable_of_bounded (transportCoeff_aestronglyMeasurable _ _).norm
              (fun s => by rw [norm_norm]; exact transportCoeff_norm_le _ _ hK s) _ _).add
              (intervalIntegrable_of_bounded (transportCoeff_aestronglyMeasurable _ _).norm
              (fun s => by rw [norm_norm]; exact transportCoeff_norm_le _ _ hK s) _ _)
          · have := norm_transportCoeff_le_const hK E' s
            have := norm_transportCoeff_le_const hK E s
            linarith
      _ = θ * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K) := by
          rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      _ ≤ _ := by
          gcongr
          exact hθ.2
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hFb 0 ⟨le_rfl, hπ⟩)
  have hkey : ‖star (W' θ) * W θ - 1‖ ≤
      ε * (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K)) := by
    rw [hvar]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖star (W' θ) * F θ * W θ‖ ≤ ε := by
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      have := hFb θ hθ
      calc ‖star (W' θ)‖ * ‖F θ‖ * ‖W θ‖ ≤ 1 * ε * 1 := by gcongr
        _ = ε := by ring
    have h2 := mul_le_mul_of_nonneg_left hcoef hε0
    nlinarith
  have heq : W' θ - W θ = -(W' θ * (star (W' θ) * W θ - 1)) := by
    rw [mul_sub, ← mul_assoc, (Unitary.mem_iff.mp hU').2, one_mul, mul_one, neg_sub]
  rw [heq, norm_neg]
  refine (norm_mul_le _ _).trans ?_
  calc ‖W' θ‖ * ‖star (W' θ) * W θ - 1‖ ≤ 1 * ‖star (W' θ) * W θ - 1‖ := by gcongr
    _ ≤ _ := by rw [one_mul]; exact hkey

/-- The integrand `W'^* (√E' C₁ G - √E G C₁) W` of the energy variation identity, with
`C₁ = coeffOf 1 γ'` and `G = coeffOf 1 (γ - γ(0))`. -/
def energyIntegrand (γ : ℝ → ℂ) (E E' : ℝ) (W W' : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) :
    Ell2 →L[ℂ] Ell2 :=
  star (W' θ) * (Real.sqrt E' • (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)) -
    Real.sqrt E • (coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ))) * W θ

/-- The energy variation identity for a closed curve:
`V_{E'}^* V_E - 1 = (√E - √E') ∫₀^L W_{E'}^* (√E' C₁ G - √E G C₁) W_E`. -/
lemma energy_variation {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') :
    star (W' (2 * π)) * W (2 * π) - 1 =
      (Real.sqrt E - Real.sqrt E') •
        ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' W W' θ := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  set F : ℝ → Ell2 →L[ℂ] Ell2 := fun θ => coeffOf E (γ θ - γ 0) - coeffOf E' (γ θ - γ 0)
    with hF
  have hFL : LipschitzOnWith _ F (Icc 0 (2 * π)) :=
    ((lipschitzWith_coeffOf hK E (γ 0)).sub (lipschitzWith_coeffOf hK E' (γ 0))).lipschitzOnWith
  have hFd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) →
      HasDerivAt F (transportCoeff γ E θ - transportCoeff γ E' θ) θ := by
    filter_upwards [hK.ae_differentiableAt (μ := volume)] with θ h1 _
    exact (hasDerivAt_coeffOf h1.hasDerivAt E (γ 0)).sub
      (hasDerivAt_coeffOf h1.hasDerivAt E' (γ 0))
  have hF0 : F 0 = 0 := by simp [hF, coeffOf_zero]
  have hF2 : F (2 * π) = 0 := by simp [hF, hclosed, coeffOf_zero]
  rw [volterra_variation (transportCoeff_aestronglyMeasurable γ E) (transportCoeff_norm_le γ E hK)
    hW.1 hW.2 (transportCoeff_aestronglyMeasurable γ E') (transportCoeff_norm_le γ E' hK)
    (transportCoeff_star γ E') hW'.1 hW'.2 hπ hFL hFd hF0 hF2,
    ← intervalIntegral.integral_smul]
  congr 1
  funext s
  simp only [hF, energyIntegrand, transportCoeff_eq_coeffOf]
  rw [coeffOf_eq_sqrt_smul E (γ s - γ 0), coeffOf_eq_sqrt_smul E' (γ s - γ 0),
    coeffOf_eq_sqrt_smul E (deriv γ s), coeffOf_eq_sqrt_smul E' (deriv γ s), ← sub_smul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, mul_sub, sub_mul]
  congr 1; congr 1; ring

lemma norm_coeffOf_one_mul_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)‖ ≤ shiftConst * K * (shiftConst * R) ∧
      ‖coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ)‖ ≤ shiftConst * K * (shiftConst * R) := by
  have hκ := shiftConst_nonneg
  have hC1 : ‖coeffOf 1 (deriv γ θ)‖ ≤ shiftConst * K := by
    refine (norm_coeffOf_le 1 _).trans ?_
    rw [Real.sqrt_one, one_mul]
    exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hK) hκ
  have hG : ‖coeffOf 1 (γ θ - γ 0)‖ ≤ shiftConst * R := by
    refine (norm_coeffOf_le 1 _).trans ?_
    rw [Real.sqrt_one, one_mul]
    exact mul_le_mul_of_nonneg_left (hR θ hθ) hκ
  have hGn := norm_nonneg (coeffOf 1 (γ θ - γ 0))
  have hCn := norm_nonneg (coeffOf 1 (deriv γ θ))
  refine ⟨(norm_mul_le _ _).trans (mul_le_mul hC1 hG hGn (by positivity)), ?_⟩
  rw [mul_comm (shiftConst * K)]
  exact (norm_mul_le _ _).trans (mul_le_mul hG hC1 hCn ((norm_nonneg _).trans hG))

lemma norm_energyCore_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) (E E' : ℝ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖Real.sqrt E' • (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)) -
      Real.sqrt E • (coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ))‖ ≤
      (Real.sqrt E' + Real.sqrt E) * (shiftConst * K * (shiftConst * R)) := by
  obtain ⟨h1, h2⟩ := norm_coeffOf_one_mul_le hK hR hθ
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), add_mul]
  gcongr

lemma norm_energyIntegrand_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖energyIntegrand γ E E' W W' θ‖ ≤
      (Real.sqrt E' + Real.sqrt E) * (shiftConst * K * (shiftConst * R)) := by
  have hn1 : ‖W θ‖ ≤ 1 := norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hθ)
  have hn1s : ‖star (W' θ)‖ ≤ 1 :=
    norm_le_one_of_mem_unitary (Unitary.star_mem (transport_mem_unitary hK hW' hθ))
  unfold energyIntegrand
  refine (norm_mul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
  have hX := norm_energyCore_le hK hR E E' hθ
  have h0 := (norm_nonneg _).trans hX
  calc _ ≤ 1 * ((Real.sqrt E' + Real.sqrt E) * (shiftConst * K * (shiftConst * R))) * 1 := by
        gcongr
    _ = _ := by ring

lemma aestronglyMeasurable_energy_aux {μ : Measure ℝ} {W W' C G : ℝ → Ell2 →L[ℂ] Ell2}
    (h4 : AEStronglyMeasurable (fun θ => star (W' θ)) μ) (hC : AEStronglyMeasurable C μ)
    (hG : AEStronglyMeasurable G μ) (hW : AEStronglyMeasurable W μ) (a b : ℝ) :
    AEStronglyMeasurable (fun θ => star (W' θ) * (a • (C θ * G θ) - b • (G θ * C θ)) * W θ) μ :=
  (h4.mul (((hC.mul hG).const_smul a).sub ((hG.mul hC).const_smul b))).mul hW

lemma intervalIntegrable_energyIntegrand {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') :
    IntervalIntegrable (energyIntegrand γ E E' W W') volume 0 (2 * π) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hπ]
  have hG : Continuous fun θ => coeffOf 1 (γ θ - γ 0) :=
    (lipschitzWith_coeffOf hK 1 (γ 0)).continuous
  haveI : SecondCountableTopologyEither ℝ (Ell2 →L[ℂ] Ell2) :=
    secondCountableTopologyEither_of_left _ _
  have hC1 : AEStronglyMeasurable (fun θ => coeffOf 1 (deriv γ θ))
      (volume.restrict (Icc 0 (2 * π))) := (transportCoeff_aestronglyMeasurable γ 1).restrict
  have hGm : AEStronglyMeasurable (fun θ => coeffOf 1 (γ θ - γ 0))
      (volume.restrict (Icc 0 (2 * π))) := hG.continuousOn.aestronglyMeasurable measurableSet_Icc
  have h4 : AEStronglyMeasurable (fun θ => star (W' θ)) (volume.restrict (Icc 0 (2 * π))) :=
    hW'.1.star.aestronglyMeasurable measurableSet_Icc
  have hm : AEStronglyMeasurable (energyIntegrand γ E E' W W')
      (volume.restrict (Icc 0 (2 * π))) :=
    aestronglyMeasurable_energy_aux h4 hC1 hGm (hW.1.aestronglyMeasurable measurableSet_Icc) _ _
  exact Integrable.of_bound hm _ ((ae_restrict_iff' measurableSet_Icc).mpr
    (Eventually.of_forall fun θ hθ => norm_energyIntegrand_le hK hR hW hW' hθ))

/-- The integral in the energy variation identity is continuous in the second energy. -/
lemma norm_integral_energyIntegrand_sub_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {R : ℝ} (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {E E' : ℝ}
    {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') :
    ‖(∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' W W' θ) -
        ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E W W θ‖ ≤
      |Real.sqrt E - Real.sqrt E'| * (shiftConst * K * (shiftConst * R)) *
        ((Real.sqrt E' + Real.sqrt E) * (shiftConst * R *
          (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K))) + 1) * (2 * π) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  rw [← intervalIntegral.integral_sub (intervalIntegrable_energyIntegrand hK hW hW')
    (intervalIntegrable_energyIntegrand hK hW hW)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_).trans
    (by rw [sub_zero, abs_of_nonneg hπ])
  have hθ' : θ ∈ Icc 0 (2 * π) := by
    rw [uIoc_of_le hπ] at hθ; exact Ioc_subset_Icc_self hθ
  set a := shiftConst * K * (shiftConst * R)
  set X' := Real.sqrt E' • (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)) -
      Real.sqrt E • (coeffOf 1 (γ θ - γ 0) * coeffOf 1 (deriv γ θ))
  have hX' : ‖X'‖ ≤ (Real.sqrt E' + Real.sqrt E) * a := norm_energyCore_le hK hR E E' hθ'
  have hXX : energyIntegrand γ E E' W W' θ - energyIntegrand γ E E W W θ =
      (star (W' θ) - star (W θ)) * X' * W θ +
        star (W θ) * ((Real.sqrt E' - Real.sqrt E) •
          (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0))) * W θ := by
    simp only [energyIntegrand, X', sub_smul, smul_sub, mul_sub, sub_mul, smul_mul_assoc,
      mul_smul_comm]
    abel
  rw [hXX]
  have hd := norm_transport_sub_le hK hR hW hW' hθ'
  have hn1 : ‖W θ‖ ≤ 1 := norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hθ')
  have hn1s : ‖star (W θ)‖ ≤ 1 :=
    norm_le_one_of_mem_unitary (Unitary.star_mem (transport_mem_unitary hK hW hθ'))
  have ha := (norm_coeffOf_one_mul_le hK hR hθ').1
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  refine (norm_add_le _ _).trans ?_
  have e1 : ‖(star (W' θ) - star (W θ)) * X' * W θ‖ ≤ |Real.sqrt E - Real.sqrt E'| * shiftConst * R *
      (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K)) *
        ((Real.sqrt E' + Real.sqrt E) * a) := by
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
    rw [← star_sub, norm_star]
    calc ‖W' θ - W θ‖ * ‖X'‖ * ‖W θ‖ ≤ ‖W' θ - W θ‖ * ‖X'‖ * 1 := by gcongr
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul hd hX' (norm_nonneg _) ((norm_nonneg _).trans hd)
  have e2 : ‖star (W θ) * ((Real.sqrt E' - Real.sqrt E) •
      (coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0))) * W θ‖ ≤
      |Real.sqrt E - Real.sqrt E'| * a := by
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
    calc ‖star (W θ)‖ * (|Real.sqrt E - Real.sqrt E'| *
          ‖coeffOf 1 (deriv γ θ) * coeffOf 1 (γ θ - γ 0)‖) * ‖W θ‖
        ≤ 1 * (|Real.sqrt E - Real.sqrt E'| * a) * 1 := by gcongr
      _ = _ := by ring
  calc _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

/-- Continuity of the transport in the energy, uniformly on `[0, L]`. -/
lemma tendsto_transport_energy {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) : Tendsto (fun E' => Ws E' θ) (𝓝 E) (𝓝 (Ws E θ)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun E' => |Real.sqrt E - Real.sqrt E'| * shiftConst * R *
      (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K))) := by fun_prop
  have hb := hc.tendsto E
  simp only [sub_self, abs_zero, zero_mul] at hb
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun E' => norm_transport_sub_le hK hR (hWs E) (hWs E') hθ) hb

/-- Continuity of the integral of the energy variation identity in the second energy. -/
lemma tendsto_integral_energyIntegrand {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ) :
    Tendsto (fun E' => ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' (Ws E) (Ws E') θ) (𝓝 E)
      (𝓝 (∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E (Ws E) (Ws E) θ)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun E' => |Real.sqrt E - Real.sqrt E'| *
      (shiftConst * K * (shiftConst * R)) * ((Real.sqrt E' + Real.sqrt E) * (shiftConst * R *
        (1 + 2 * π * ((Real.sqrt E' + Real.sqrt E) * shiftConst * K))) + 1) * (2 * π)) := by
    fun_prop
  have hb := hc.tendsto E
  simp only [sub_self, abs_zero, zero_mul] at hb
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun E' => norm_integral_energyIntegrand_sub_le hK hR (hWs E) (hWs E')) hb

/-- **Lemma 4.7 (curvature formula).** For a closed Lipschitz curve and `E > 0`, the endpoint
`V_E = W_E(L)` of the transport is differentiable in the energy (in operator norm), with
`∂_E V_E = -i V_E Q_E`, `Q_E = (1/4) ∫₀^L b W_E^* D_N W_E dθ`. -/
theorem hasDerivAt_transport_energy {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) :
    HasDerivAt (fun E => Ws E (2 * π))
      (-(Complex.I • (Ws E (2 * π) * curvatureOp γ (Ws E)))) E := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have h2π : (2 * π) ∈ Icc 0 (2 * π) := ⟨hπ, le_rfl⟩
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  set s := Real.sqrt E with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hE
  set V : ℝ → Ell2 →L[ℂ] Ell2 := fun E' => Ws E' (2 * π) with hVdef
  set I : ℝ → Ell2 →L[ℂ] Ell2 :=
    fun E' => ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' (Ws E) (Ws E') θ with hIdef
  have hslope : ∀ E', 0 < E' → E' ≠ E →
      slope V E E' = (Real.sqrt E' + s)⁻¹ • (V E' * I E') := by
    intro E' hpos hne
    simp only [hVdef, hIdef]
    have hvar := energy_variation hK hclosed (hWs E) (hWs E')
    have hU := transport_mem_unitary hK (hWs E') h2π
    have hVV : Ws E' (2 * π) * star (Ws E' (2 * π)) = 1 := (Unitary.mem_iff.mp hU).2
    have hdiff : Ws E' (2 * π) - Ws E (2 * π) = (Real.sqrt E' - s) •
        (Ws E' (2 * π) * ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E' (Ws E) (Ws E') θ) := by
      have : Ws E' (2 * π) - Ws E (2 * π) =
          -(Ws E' (2 * π) * (star (Ws E' (2 * π)) * Ws E (2 * π) - 1)) := by
        rw [mul_sub, ← mul_assoc, hVV, one_mul, mul_one, neg_sub]
      rw [this, hvar, mul_smul_comm, ← neg_smul, neg_sub]
    rw [slope_def_module, hdiff, smul_smul]
    congr 1
    have hne' : Real.sqrt E' - s ≠ 0 := by
      intro h
      apply hne
      have h2 := congrArg (· ^ 2) (sub_eq_zero.mp h)
      simp only [hsdef, Real.sq_sqrt hpos.le, Real.sq_sqrt hE.le] at h2
      exact h2
    have hsum : Real.sqrt E' + s ≠ 0 := by positivity
    have hEE : E' - E = (Real.sqrt E' - s) * (Real.sqrt E' + s) := by
      rw [hsdef]
      ring_nf
      rw [Real.sq_sqrt hpos.le, Real.sq_sqrt hE.le]
    rw [hEE]
    field_simp
  have hV : Tendsto V (𝓝 E) (𝓝 (V E)) := tendsto_transport_energy hK hWs E h2π
  have hI : Tendsto I (𝓝 E) (𝓝 (I E)) := tendsto_integral_energyIntegrand hK hWs E
  have hsq : Tendsto (fun E' => (Real.sqrt E' + s)⁻¹) (𝓝 E) (𝓝 ((s + s)⁻¹)) :=
    ((Real.continuous_sqrt.tendsto E).add_const s).inv₀ (by positivity)
  have hval : (s + s)⁻¹ • (V E * I E) = -(Complex.I • (Ws E (2 * π) * curvatureOp γ (Ws E))) := by
    simp only [hVdef, hIdef]
    have hIE : ∫ θ in (0 : ℝ)..(2 * π), energyIntegrand γ E E (Ws E) (Ws E) θ =
        ((s : ℂ) * (-(Complex.I / 2))) •
          ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ • (star (Ws E θ) * diagN * Ws E θ) := by
      rw [← intervalIntegral.integral_smul]
      congr 1
      funext θ
      simp only [energyIntegrand]
      rw [← smul_sub, coeffOf_one_commutator, areaDensity, mul_comm (conj _) (deriv γ θ)]
      simp only [smul_mul_assoc, mul_smul_comm, real_smul_eq_coe_smul_clm, smul_smul]
      congr 1
      ring
    rw [hIE, curvatureOp]
    simp only [mul_smul_comm, real_smul_eq_coe_smul_clm, smul_smul, ← neg_smul]
    congr 1
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
    ring
  rw [hasDerivAt_iff_tendsto_slope, ← hval]
  refine ((hsq.smul (hV.mul hI)).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hE)] with E' hne hpos
  exact (hslope E' hpos hne).symm

/-- `D_N` is self-adjoint. -/
lemma star_diagN : star diagN = diagN := by
  rw [← shift_commutator, star_sub, star_mul, star_mul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

lemma areaDensity_aestronglyMeasurable {γ : ℝ → ℂ} (hγ : Continuous γ) :
    AEStronglyMeasurable (areaDensity γ) volume := by
  have h1 : AEStronglyMeasurable (fun θ => conj (γ θ - γ 0)) volume :=
    (Complex.continuous_conj.comp (hγ.sub continuous_const)).aestronglyMeasurable
  exact Complex.continuous_im.comp_aestronglyMeasurable
    (h1.mul (measurable_deriv γ).aestronglyMeasurable)

lemma abs_areaDensity_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    |areaDensity γ θ| ≤ R * K := by
  unfold areaDensity
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hR θ hθ) (norm_deriv_le_of_lipschitz hK) (norm_nonneg _)
    ((norm_nonneg _).trans (hR θ hθ))

/-- Integrability of `θ ↦ b(θ) U(θ)^* D_N U(θ)` for a continuous unitary family `U` and a
bounded measurable weight `b`. -/
lemma intervalIntegrable_conj_diagN {U : ℝ → Ell2 →L[ℂ] Ell2}
    (hU : ContinuousOn U (Icc 0 (2 * π)))
    (hunit : ∀ θ ∈ Icc 0 (2 * π), U θ ∈ unitary (Ell2 →L[ℂ] Ell2))
    {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) :
    IntervalIntegrable (fun θ => b θ • (star (U θ) * diagN * U θ)) volume 0 (2 * π) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hπ]
  haveI : SecondCountableTopologyEither ℝ (Ell2 →L[ℂ] Ell2) :=
    secondCountableTopologyEither_of_left _ _
  have hm : AEStronglyMeasurable (fun θ => b θ • (star (U θ) * diagN * U θ))
      (volume.restrict (Icc 0 (2 * π))) :=
    hb.restrict.smul (((hU.star.aestronglyMeasurable measurableSet_Icc).mul_const _).mul
      (hU.aestronglyMeasurable measurableSet_Icc))
  refine Integrable.of_bound hm (B * ‖diagN‖) ((ae_restrict_iff' measurableSet_Icc).mpr
    (Eventually.of_forall fun θ hθ => ?_))
  have h1 : ‖U θ‖ ≤ 1 := norm_le_one_of_mem_unitary (hunit θ hθ)
  have h2 : ‖star (U θ)‖ ≤ 1 := norm_le_one_of_mem_unitary (Unitary.star_mem (hunit θ hθ))
  rw [norm_smul, Real.norm_eq_abs]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hbB θ hθ)
  gcongr
  · exact hbB θ hθ
  · calc ‖star (U θ) * diagN * U θ‖ ≤ ‖star (U θ)‖ * ‖diagN‖ * ‖U θ‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖diagN‖ * 1 := by gcongr
      _ = ‖diagN‖ := by ring

/-- The curvature operator `Q_E` is self-adjoint. -/
theorem curvatureOp_star {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    star (curvatureOp γ W) = curvatureOp γ W := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  have hint := intervalIntegrable_conj_diagN hW.1 (fun θ hθ => transport_mem_unitary hK hW hθ)
    (areaDensity_aestronglyMeasurable hK.continuous) (fun θ hθ => abs_areaDensity_le hK hR hθ)
  unfold curvatureOp
  rw [star_smul, star_trivial]
  congr 1
  have := (starL' ℝ (A := Ell2 →L[ℂ] Ell2)).toContinuousLinearMap.intervalIntegral_comp_comm hint
  simp only [ContinuousLinearEquiv.coe_coe, starL'_apply] at this
  rw [← this]
  congr 1
  funext θ
  rw [star_smul, star_trivial, star_mul, star_mul, star_star, star_diagN, mul_assoc]

/-- Lemma 4.7, curvature formula in the form `V_E^* ∂_E V_E = -i Q_E`. -/
theorem transport_adjoint_mul_deriv_energy {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) :
    star (Ws E (2 * π)) * deriv (fun E => Ws E (2 * π)) E =
      -(Complex.I • curvatureOp γ (Ws E)) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  rw [(hasDerivAt_transport_energy hK hclosed hWs hE).deriv, mul_neg, mul_smul_comm, ← mul_assoc,
    (Unitary.mem_iff.mp (transport_mem_unitary hK (hWs E) ⟨hπ, le_rfl⟩)).1, one_mul]

/-- Lemma 4.7: the monodromy `U_E = V_E^*` is differentiable in `E > 0` (in operator norm),
with `∂_E U_E = i Q_E U_E`. -/
theorem hasDerivAt_monodromy_energy {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) :
    HasDerivAt (fun E => monodromy (Ws E))
      (Complex.I • (curvatureOp γ (Ws E) * monodromy (Ws E))) E := by
  have h := (hasDerivAt_transport_energy hK hclosed hWs hE).star
  simp only [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
  convert h using 1
  rw [star_neg, star_smul, star_mul, curvatureOp_star hK (hWs E), Complex.star_def,
    Complex.conj_I, neg_smul, neg_neg]

/-- Lemma 4.7: `L_E = -i U_E^* ∂_E U_E = V_E Q_E V_E^*`. -/
theorem monodromy_logDeriv_energy {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) :
    -(Complex.I • (star (monodromy (Ws E)) * deriv (fun E => monodromy (Ws E)) E)) =
      Ws E (2 * π) * curvatureOp γ (Ws E) * star (Ws E (2 * π)) := by
  rw [(hasDerivAt_monodromy_energy hK hclosed hWs hE).deriv, monodromy,
    ← ContinuousLinearMap.star_eq_adjoint, star_star, mul_smul_comm, smul_smul, Complex.I_mul_I,
    neg_one_smul, neg_neg, mul_assoc]

end PolyaNeumann

end
