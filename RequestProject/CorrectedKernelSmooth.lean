module

public import RequestProject.FractionalKernel
public import RequestProject.CorrectedKernel
public import RequestProject.SmallTransport

/-!
# `H^{1+δ}` regularity of the corrected kernel (Lemma 6.6, fractional part)

For a closed curve `γ` whose derivative is Lipschitz on `[0, L]` (`L = 2π`), the transport is
`C¹` there, with `W' = C_E W` (`hasDerivWithinAt_transport`). The corrected kernel
`r_E(θ, t) = i sgn(θ - t)(w_E(θ, t) - 1) + i(θ - t)/π + ⟨e₀, W(θ) B_E W(t)^* e₀⟩` is then, for
every fixed `t`, differentiable in `θ` on `[0, L]` with a Lipschitz derivative, uniformly in `t`:
the jump of `sgn(θ - t)` is compensated by `w_E(t, t) = 1` and `∂_θ w_E(t, t) = ⟨e₀, C_E(t) e₀⟩ = 0`,
as in the proof of Lemma 6.6. Only the cut at `θ = 0 ≡ L` remains, where the derivative may jump.
By `summable_kernelCoeff_three_halves`, the double Fourier coefficients satisfy

  `∑_{n, m} |m|^{2+2δ} |r_{n m}|² < ∞`  for `0 ≤ δ < 1/2`
  (`summable_rpow_mul_correctedKernelCoeff`),

i.e. `r_E ∈ H^{1+δ}` in the first variable.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-- **Second differences of a function with Lipschitz derivative.** If `f` is differentiable on
`[0, 2π]` (within the interval) with an `M`-Lipschitz derivative, then
`|f(θ+2h) - 2f(θ+h) + f(θ)| ≤ M h²` whenever `[θ, θ + 2h] ⊆ [0, 2π]`. -/
lemma norm_secondDiff_le_of_lipschitz_deriv {f f' : ℝ → ℂ} {M : ℝ}
    (hderiv : ∀ x ∈ Set.Icc 0 (2 * π), HasDerivWithinAt f (f' x) (Set.Icc 0 (2 * π)) x)
    (hM : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π), ‖f' x - f' y‖ ≤ M * |x - y|)
    {h θ : ℝ} (hh : 0 < h) (hθ : θ ∈ Set.Icc 0 (2 * π - 2 * h)) :
    ‖secondDiff f h θ‖ ≤ M * h ^ 2 := by
  obtain ⟨hθ0, hθa⟩ := hθ
  set g : ℝ → ℂ := fun u => f (θ + h + u) - f (θ + u) with hgdef
  have hmaps1 : Set.MapsTo (fun u : ℝ => θ + h + u) (Set.Icc 0 h) (Set.Icc 0 (2 * π)) := by
    intro u hu; obtain ⟨hu0, hu1⟩ := hu; constructor <;> linarith
  have hmaps2 : Set.MapsTo (fun u : ℝ => θ + u) (Set.Icc 0 h) (Set.Icc 0 (2 * π)) := by
    intro u hu; obtain ⟨hu0, hu1⟩ := hu; constructor <;> linarith
  have hgd : ∀ u ∈ Set.Icc 0 h, HasDerivWithinAt g
      (f' (θ + h + u) - f' (θ + u)) (Set.Icc 0 h) u := by
    intro u hu
    have h1 : HasDerivWithinAt (fun u : ℝ => θ + h + u) 1 (Set.Icc 0 h) u :=
      (hasDerivAt_id u).const_add (θ + h) |>.hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun u : ℝ => θ + u) 1 (Set.Icc 0 h) u :=
      (hasDerivAt_id u).const_add θ |>.hasDerivWithinAt
    have e1 := (hderiv _ (hmaps1 hu)).scomp u h1 hmaps1
    have e2 := (hderiv _ (hmaps2 hu)).scomp u h2 hmaps2
    simp only [one_smul] at e1 e2
    exact e1.sub e2
  have hbd : ∀ u ∈ Set.Ico 0 h, ‖f' (θ + h + u) - f' (θ + u)‖ ≤ M * h := by
    intro u hu
    have := hM _ (hmaps1 (Set.Ico_subset_Icc_self hu)) _ (hmaps2 (Set.Ico_subset_Icc_self hu))
    rwa [show θ + h + u - (θ + u) = h by ring, abs_of_pos hh] at this
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hgd hbd h ⟨hh.le, le_rfl⟩
  have hval : g h - g 0 = secondDiff f h θ := by
    simp only [hgdef, secondDiff, add_zero, show θ + h + h = θ + 2 * h by ring]
  rw [hval, sub_zero] at key
  nlinarith

variable {γ : ℝ → ℂ} {K K' : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

/-- The transport is differentiable on `[0, L]` with `W' = C_E W` when `γ'` is continuous
there. -/
lemma hasDerivWithinAt_transport
    (hγ' : ContinuousOn (deriv γ) (Set.Icc 0 (2 * π))) (hW : IsTransport γ E W) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    HasDerivWithinAt W (transportCoeff γ E θ * W θ) (Set.Icc 0 (2 * π)) θ := by
  have hco : Continuous (coeffOf E) := by
    unfold coeffOf
    fun_prop
  have hC : ContinuousOn (transportCoeff γ E) (Set.Icc 0 (2 * π)) := hco.comp_continuousOn hγ'
  set F : ℝ → Ell2 →L[ℂ] Ell2 := fun s => transportCoeff γ E s * W s with hFdef
  have hF : ContinuousOn F (Set.Icc 0 (2 * π)) := hC.mul hW.1
  have hsub : Set.uIcc 0 θ ⊆ Set.Icc 0 (2 * π) := by
    rw [Set.uIcc_of_le hθ.1]; exact Set.Icc_subset_Icc le_rfl hθ.2
  haveI : Fact (θ ∈ Set.Icc 0 (2 * π)) := ⟨hθ⟩
  haveI : SecondCountableTopologyEither ℝ (Ell2 →L[ℂ] Ell2) :=
    secondCountableTopologyEither_of_left _ _
  have hint : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, F s) (F θ) (Set.Icc 0 (2 * π)) θ :=
    intervalIntegral.integral_hasDerivWithinAt_right ((hF.mono hsub).intervalIntegrable)
      (hF.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc θ) (hF θ hθ)
  exact (hint.const_add 1).congr_of_mem (fun u hu => hW.2 u hu) hθ

/-- Derivative of a matrix entry `⟨e₀, W(θ) y⟩` of the transport. -/
lemma hasDerivWithinAt_inner_transport
    (hγ' : ContinuousOn (deriv γ) (Set.Icc 0 (2 * π))) (hW : IsTransport γ E W) (y : Ell2)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    HasDerivWithinAt (fun u => ⟪basisVec 0, W u y⟫_ℂ)
      ⟪basisVec 0, (transportCoeff γ E θ * W θ) y⟫_ℂ (Set.Icc 0 (2 * π)) θ := by
  have hΦ := (((innerSL ℂ (basisVec 0)).comp (ContinuousLinearMap.apply ℂ Ell2 y)).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivWithinAt θ (hasDerivWithinAt_transport hγ' hW hθ)
  exact hΦ

/-- The derivative `⟨e₀, C_E(θ) W(θ) y⟩` is Lipschitz on `[0, L]` when `γ'` is. -/
lemma norm_inner_transportCoeff_mul_sub_le (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) (y : Ell2) {θ θ' : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π))
    (hθ' : θ' ∈ Set.Icc 0 (2 * π)) :
    ‖⟪basisVec 0, (transportCoeff γ E θ * W θ) y⟫_ℂ -
        ⟪basisVec 0, (transportCoeff γ E θ' * W θ') y⟫_ℂ‖ ≤
      (Real.sqrt E * shiftConst * K' + (Real.sqrt E * shiftConst * K) ^ 2) * ‖y‖ *
        |θ - θ'| := by
  have hκ := shiftConst_nonneg
  have hC : ‖transportCoeff γ E θ - transportCoeff γ E θ'‖ ≤
      Real.sqrt E * shiftConst * K' * |θ - θ'| := by
    rw [transportCoeff_eq_coeffOf, transportCoeff_eq_coeffOf, coeffOf_sub]
    refine (norm_coeffOf_le E _).trans ?_
    rw [mul_assoc (Real.sqrt E * shiftConst)]
    gcongr
    exact hγ' θ hθ θ' hθ'
  have hW1 := norm_transport_le_one hK hW hθ
  have hC' := norm_transportCoeff_le_const hK E θ'
  have hWl := norm_transport_sub_le_lip hK hW hθ hθ'
  have hop : ‖transportCoeff γ E θ * W θ - transportCoeff γ E θ' * W θ'‖ ≤
      (Real.sqrt E * shiftConst * K' + (Real.sqrt E * shiftConst * K) ^ 2) * |θ - θ'| := by
    have e : transportCoeff γ E θ * W θ - transportCoeff γ E θ' * W θ' =
        (transportCoeff γ E θ - transportCoeff γ E θ') * W θ +
          transportCoeff γ E θ' * (W θ - W θ') := by
      rw [sub_mul, mul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)).trans ?_
    have h1 : ‖transportCoeff γ E θ - transportCoeff γ E θ'‖ * ‖W θ‖ ≤
        Real.sqrt E * shiftConst * K' * |θ - θ'| * 1 :=
      mul_le_mul hC hW1 (norm_nonneg _) (by positivity)
    have h2 : ‖transportCoeff γ E θ'‖ * ‖W θ - W θ'‖ ≤
        (Real.sqrt E * shiftConst * K) * (Real.sqrt E * shiftConst * K * |θ - θ'|) :=
      mul_le_mul hC' hWl (norm_nonneg _) (by positivity)
    nlinarith
  rw [← inner_sub_right, ← ContinuousLinearMap.sub_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [norm_basisVec_zero, one_mul]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  calc _ ≤ (Real.sqrt E * shiftConst * K' + (Real.sqrt E * shiftConst * K) ^ 2) * |θ - θ'| *
        ‖y‖ := by gcongr
    _ = _ := by ring

/-- The transport coefficient has zero `e₀, e₀` entry. -/
lemma inner_basisVec_transportCoeff_basisVec (E s : ℝ) :
    ⟪basisVec 0, transportCoeff γ E s (basisVec 0)⟫_ℂ = 0 := by
  rw [inner_basisVec, transportCoeff_coord_zero, basisVec_coord]
  simp

/-- Derivative of `sgn(θ - t) g(θ)` when `g(t) = g'(t) = 0`. -/
lemma hasDerivWithinAt_sign_mul {g g' : ℝ → ℂ} {t : ℝ}
    (hg : ∀ x ∈ Set.Icc 0 (2 * π), HasDerivWithinAt g (g' x) (Set.Icc 0 (2 * π)) x)
    (ht : t ∈ Set.Icc 0 (2 * π)) (hgt : g t = 0) (hg't : g' t = 0) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (2 * π)) :
    HasDerivWithinAt (fun u => (Real.sign (u - t) : ℂ) * g u)
      ((Real.sign (x - t) : ℂ) * g' x) (Set.Icc 0 (2 * π)) x := by
  rcases lt_trichotomy x t with hxt | hxt | hxt
  · have hev : (fun u => (Real.sign (u - t) : ℂ) * g u) =ᶠ[nhdsWithin x (Set.Icc 0 (2 * π))]
        fun u => (Real.sign (x - t) : ℂ) * g u := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxt)] with u hu
      rw [Real.sign_of_neg (sub_neg.2 hu), Real.sign_of_neg (sub_neg.2 hxt)]
    exact ((hg x hx).const_mul _).congr_of_eventuallyEq hev rfl
  · subst hxt
    rw [sub_self, Real.sign_zero, Complex.ofReal_zero, zero_mul]
    have h0 := hg x hx
    rw [hg't, hasDerivWithinAt_iff_isLittleO] at h0
    rw [hasDerivWithinAt_iff_isLittleO]
    refine (Asymptotics.isBigO_of_le _ fun u => ?_).trans_isLittleO h0
    simp only [sub_self, Real.sign_zero, Complex.ofReal_zero, zero_mul, smul_zero, sub_zero, hgt]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_real_sign_le _)
  · have hev : (fun u => (Real.sign (u - t) : ℂ) * g u) =ᶠ[nhdsWithin x (Set.Icc 0 (2 * π))]
        fun u => (Real.sign (x - t) : ℂ) * g u := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hxt)] with u hu
      rw [Real.sign_of_pos (sub_pos.2 hu), Real.sign_of_pos (sub_pos.2 hxt)]
    exact ((hg x hx).const_mul _).congr_of_eventuallyEq hev rfl

/-- The `θ`-derivative of the corrected kernel. -/
def correctedKernelDeriv (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  Complex.I * Real.sign (θ - t) *
      ⟪basisVec 0, (transportCoeff γ E θ * W θ) (ContinuousLinearMap.adjoint (W t) (basisVec 0))⟫_ℂ +
    Complex.I * (1 / π) +
    ⟪basisVec 0, (transportCoeff γ E θ * W θ)
      (cutBE W (ContinuousLinearMap.adjoint (W t) (basisVec 0)))⟫_ℂ

/-- For fixed `t ∈ [0, L]`, `θ ↦ r_E(θ, t)` is differentiable on `[0, L]`. -/
lemma hasDerivWithinAt_correctedKernel (hK : LipschitzWith K γ)
    (hγ' : ContinuousOn (deriv γ) (Set.Icc 0 (2 * π))) (hW : IsTransport γ E W) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (2 * π)) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    HasDerivWithinAt (fun u => correctedKernel W u t) (correctedKernelDeriv γ E W θ t)
      (Set.Icc 0 (2 * π)) θ := by
  set x := ContinuousLinearMap.adjoint (W t) (basisVec 0) with hx
  set g : ℝ → ℂ := fun u => ⟪basisVec 0, W u x⟫_ℂ - 1 with hgdef
  set g' : ℝ → ℂ := fun u => ⟪basisVec 0, (transportCoeff γ E u * W u) x⟫_ℂ with hg'def
  have hg : ∀ u ∈ Set.Icc 0 (2 * π), HasDerivWithinAt g (g' u) (Set.Icc 0 (2 * π)) u :=
    fun u hu => (hasDerivWithinAt_inner_transport hγ' hW x hu).sub_const 1
  have hgt : g t = 0 := by
    have := volterraKernel_self hK hW ht
    unfold volterraKernel at this
    simp only [hgdef]
    rw [hx, this, sub_self]
  have hg't : g' t = 0 := by
    simp only [hg'def, hx, ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.mul_apply (W t), transport_mul_adjoint hK hW ht,
      ContinuousLinearMap.one_apply, inner_basisVec_transportCoeff_basisVec]
  have h1 := (hasDerivWithinAt_sign_mul hg ht hgt hg't hθ).const_mul Complex.I
  have hlinR : HasDerivAt (fun u : ℝ => (u - t) / π) (1 / π) θ :=
    ((hasDerivAt_id θ).sub_const t).div_const π
  have h2 := (hlinR.ofReal_comp.const_mul Complex.I).hasDerivWithinAt (s := Set.Icc 0 (2 * π))
  have h3 := hasDerivWithinAt_inner_transport hγ' hW (cutBE W x) hθ
  have hsum := (h1.add h2).add h3
  convert hsum using 1
  · funext u
    simp only [correctedKernel, volterraKernel, hgdef, hx, Pi.add_apply]
    push_cast
    ring
  · simp only [correctedKernelDeriv, hg'def, hx]
    push_cast
    ring

/-- The `θ`-derivative of the corrected kernel is Lipschitz on `[0, L]`, uniformly in `t`. -/
lemma norm_correctedKernelDeriv_sub_le (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * π)) {θ θ' : ℝ}
    (hθ : θ ∈ Set.Icc 0 (2 * π)) (hθ' : θ' ∈ Set.Icc 0 (2 * π)) :
    ‖correctedKernelDeriv γ E W θ t - correctedKernelDeriv γ E W θ' t‖ ≤
      (Real.sqrt E * shiftConst * K' + (Real.sqrt E * shiftConst * K) ^ 2) *
        (1 + ‖cutBE W‖) * |θ - θ'| := by
  set L0 := Real.sqrt E * shiftConst * K' + (Real.sqrt E * shiftConst * K) ^ 2 with hL0
  have hκ := shiftConst_nonneg
  have hL0nn : 0 ≤ L0 := by positivity
  set x := ContinuousLinearMap.adjoint (W t) (basisVec 0) with hx
  have hx1 : ‖x‖ ≤ 1 := norm_adjoint_transport_e0_le hK hW ht
  set a : ℝ → ℂ := fun u => ⟪basisVec 0, (transportCoeff γ E u * W u) x⟫_ℂ with hadef
  have ha : ∀ u ∈ Set.Icc 0 (2 * π), ∀ u' ∈ Set.Icc 0 (2 * π),
      ‖a u - a u'‖ ≤ L0 * |u - u'| := by
    intro u hu u' hu'
    refine (norm_inner_transportCoeff_mul_sub_le hK hγ' hW x hu hu').trans ?_
    calc L0 * ‖x‖ * |u - u'| ≤ L0 * 1 * |u - u'| := by gcongr
      _ = _ := by ring
  have hat : a t = 0 := by
    simp only [hadef, hx, ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.mul_apply (W t), transport_mul_adjoint hK hW ht,
      ContinuousLinearMap.one_apply, inner_basisVec_transportCoeff_basisVec]
  have ha0 : ∀ u ∈ Set.Icc 0 (2 * π), ‖a u‖ ≤ L0 * |u - t| := fun u hu => by
    simpa [hat] using ha u hu t ht
  have h1 : ‖(Real.sign (θ - t) : ℂ) * a θ - (Real.sign (θ' - t) : ℂ) * a θ'‖ ≤
      L0 * |θ - θ'| :=
    norm_sign_mul_sub_le (ha θ hθ θ' hθ') (ha0 θ hθ) (ha0 θ' hθ')
  have h2 : ‖⟪basisVec 0, (transportCoeff γ E θ * W θ) (cutBE W x)⟫_ℂ -
      ⟪basisVec 0, (transportCoeff γ E θ' * W θ') (cutBE W x)⟫_ℂ‖ ≤
      L0 * ‖cutBE W‖ * |θ - θ'| := by
    refine (norm_inner_transportCoeff_mul_sub_le hK hγ' hW _ hθ hθ').trans ?_
    gcongr
    calc ‖cutBE W x‖ ≤ ‖cutBE W‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖cutBE W‖ * 1 := by gcongr
      _ = _ := mul_one _
  have e : correctedKernelDeriv γ E W θ t - correctedKernelDeriv γ E W θ' t =
      Complex.I * ((Real.sign (θ - t) : ℂ) * a θ - (Real.sign (θ' - t) : ℂ) * a θ') +
      (⟪basisVec 0, (transportCoeff γ E θ * W θ) (cutBE W x)⟫_ℂ -
        ⟪basisVec 0, (transportCoeff γ E θ' * W θ') (cutBE W x)⟫_ℂ) := by
    simp only [correctedKernelDeriv, hadef, hx]
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  have : 0 ≤ L0 * |θ - θ'| := by positivity
  nlinarith

/-- **Lemma 6.6 (fractional part, Fourier form).** For a transport `W` of a closed curve whose
derivative `γ'` is Lipschitz on `[0, L]`, with `c_E ≠ 0`, the double Fourier coefficients on
`[0, L]²` of the corrected Volterra kernel `r_E` satisfy `∑_{n,m} |m|^{2+2δ} |r_{n m}|² < ∞`
for every `0 ≤ δ < 1/2`: `r_E ∈ H^{1+δ}` in the first variable. -/
theorem summable_rpow_mul_correctedKernelCoeff (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ' : δ < 1 / 2) :
    Summable fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) * ‖fourierCoeffOn two_pi_pos
      (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) p.1) p.2‖ ^ 2 := by
  have hγc : ContinuousOn (deriv γ) (Set.Icc 0 (2 * π)) :=
    (LipschitzOnWith.of_dist_le_mul (K := K') fun x hx y hy => by
      rw [dist_eq_norm, Real.dist_eq]; exact hγ' x hx y hy).continuousOn
  set C : NNReal := ⟨Real.sqrt E * shiftConst * K * (2 + ‖cutBE W‖) + 1 / π, by
    have := shiftConst_nonneg; have := pi_pos; positivity⟩ with hCdef
  set A : ℝ := (Real.sqrt E * shiftConst * K' + (Real.sqrt E * shiftConst * K) ^ 2) *
    (1 + ‖cutBE W‖) with hAdef
  have hA : 0 ≤ A := by have := shiftConst_nonneg; positivity
  set k : ℝ → ℝ → ℂ := fun θ t => periodize (fun θ' => correctedKernel W θ' (clampTwoPi t)) θ
  have hlipIcc : ∀ t, ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π),
      ‖correctedKernel W x (clampTwoPi t) - correctedKernel W y (clampTwoPi t)‖ ≤ C * |x - y| :=
    fun t x hx y hy => norm_correctedKernel_sub_le hK hW hx hy (clampTwoPi_mem t)
  have hend : ∀ t, correctedKernel W (2 * π) (clampTwoPi t) = correctedKernel W 0 (clampTwoPi t) :=
    fun t => correctedKernel_endpoint hK hW hc (clampTwoPi_mem t)
  have hmeas : ∀ θ, Measurable (k θ) := fun θ =>
    measurable_correctedKernel_clamp hW (toIcoMod two_pi_pos 0 θ)
  have hrep : ∀ θ, toIcoMod two_pi_pos 0 θ ∈ Set.Icc 0 (2 * π) := fun θ => by
    have := toIcoMod_mem_Ico two_pi_pos 0 θ
    simp only [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  have hbd : ∀ θ t, ‖k θ t‖ ≤ 4 + ‖cutBE W‖ := fun θ t =>
    norm_correctedKernel_le hK hW (hrep θ) (clampTwoPi_mem t)
  have hlip : ∀ θ θ' t, t ∈ Set.Ico 0 (2 * π) → ‖k θ t - k θ' t‖ ≤ C * |θ - θ'| := by
    intro θ θ' t _
    have hL := lipschitzWith_periodize (hlipIcc t) (hend t)
    have := hL.dist_le_mul θ θ'
    rwa [dist_eq_norm, Real.dist_eq] at this
  have hper : ∀ θ t, t ∈ Set.Ico 0 (2 * π) → k (θ + 2 * π) t = k θ t := fun θ t _ =>
    periodic_periodize _ θ
  have hsecond : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h),
      ∀ t ∈ Set.Ico 0 (2 * π), ‖secondDiff (fun θ => k θ t) h θ‖ ≤ A * h ^ 2 := by
    intro h hh _ θ hθ t _
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hm : ∀ c, 0 ≤ c → c ≤ 2 * h → θ + c ∈ Set.Icc 0 (2 * π) := fun c hc0 hc1 =>
      ⟨by linarith, by linarith⟩
    have heq : secondDiff (fun θ => k θ t) h θ =
        secondDiff (fun θ => correctedKernel W θ (clampTwoPi t)) h θ := by
      simp only [secondDiff, k]
      rw [periodize_eqOn_Icc (hend t) (hm (2 * h) (by linarith) le_rfl),
        periodize_eqOn_Icc (hend t) (hm h hh.le (by linarith)),
        periodize_eqOn_Icc (hend t) (by simpa using hm 0 le_rfl (by linarith))]
    rw [heq]
    exact norm_secondDiff_le_of_lipschitz_deriv
      (fun x hx => hasDerivWithinAt_correctedKernel hK hγc hW (clampTwoPi_mem t) hx)
      (fun x hx y hy => norm_correctedKernelDeriv_sub_le hK hγ' hW (clampTwoPi_mem t) hx hy)
      hh ⟨hθ0, hθ1⟩
  have h := summable_kernelCoeff_three_halves hmeas hbd hA hlip hper hsecond hδ hδ'
  refine h.congr fun p => ?_
  congr 3
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [Set.uIcc_of_le two_pi_pos.le] at hθ
  congr 1
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le two_pi_pos.le] at ht
  simp only [k]
  rw [periodize_eqOn_Icc (hend t) hθ, clampTwoPi_of_mem ht]

end PolyaNeumann
