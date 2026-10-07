module

public import RequestProject.HerglotzSchur

/-!
# The kernel part of the small-energy Schur complement (Lemma 8.4, kernel estimate)

Let `w(θ, s) = ⟨e₀, W(θ) W(s)^* e₀⟩` be the Volterra kernel of the transport, `b_E` the function
`smallB`, `β_E = b_E - 2` and `a_E = smallA W`. The kernel

  `r(θ, s) = i sgn(θ - s) (w(θ, s) - 1) - a_E⁻¹ β_E(θ) conj(β_E(s))`

(`schurKernel`) is periodic in both variables on `[0, L]²` (`L = 2π`) and absolutely continuous in
`s`, with an `s`-derivative `ρ` (`schurRho`) that is Lipschitz in `θ` with constant `O(E)` once
`|a_E| ≳ E`. For a bounded measurable `g` with `∫₀^L g = 0` and primitive `G`,

  `Re ∫ conj(g) i (T_E - T_E^*) g - |∫ conj(b_E) g|² / a_E
      = Re ∫ conj(g) 2i G + Re ∫ conj(g(θ)) ∫ r(θ, s) g(s) ds dθ`   (`re_volterra_sub_schur_eq`),

and the last term is bounded by `C E (∫₀^L |G - c|)²` for every constant `c`
(`norm_schurKernel_form_le`, from the double integration by parts `norm_kernel_form_le`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace Interval

noncomputable section

namespace PolyaNeumann

/-- `β_E = b_E - 2`. -/
def schurBeta (W : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) : ℂ := smallB W θ - 2

/-- The jump part `i sgn(θ - s) (w(θ, s) - 1)` of the kernel. -/
def schurKernel0 (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) : ℂ :=
  if s ≤ θ then Complex.I * (volterraKernel W θ s - 1) else -(Complex.I * (volterraKernel W θ s - 1))

/-- The corrected periodic kernel `r(θ, s) = i sgn(θ - s)(w(θ, s) - 1) - a⁻¹ β(θ) conj(β(s))`. -/
def schurKernel (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) : ℂ :=
  schurKernel0 W θ s - schurBeta W θ * conj (schurBeta W s) / (smallA W : ℂ)

/-- The `s`-derivative of the jump part. -/
def schurRho0 (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  if t ≤ θ then Complex.I * kernelRho γ E W θ t else -(Complex.I * kernelRho γ E W θ t)

/-- The `s`-derivative of the corrected kernel. -/
def schurRho (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  schurRho0 γ E W θ t - schurBeta W θ * conj (smallBDer γ E W t) / (smallA W : ℂ)

variable {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

lemma volterraKernel_diag (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) : volterraKernel W θ θ = 1 := by
  have hu := transport_mem_unitary hK hW hθ
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  rw [volterraKernel, ← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  simp [basisVec]

lemma conj_volterraKernel (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) :
    conj (volterraKernel W s θ) = volterraKernel W θ s := by
  rw [volterraKernel, volterraKernel, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left]

lemma volterraKernel_add_end (hW : IsTransport γ E W) (θ : ℝ) :
    volterraKernel W θ (2 * π) + volterraKernel W θ 0 = smallB W θ := by
  rw [volterraKernel, volterraKernel, transport_zero_eq hW, smallB, ← inner_basisVec,
    ← inner_add_right, ← map_add, radialVec, ← ContinuousLinearMap.star_eq_adjoint (1 : Ell2 →L[ℂ] Ell2),
    star_one, ContinuousLinearMap.one_apply, add_comm]

lemma volterraKernel_end_add (hW : IsTransport γ E W) (s : ℝ) :
    volterraKernel W (2 * π) s + volterraKernel W 0 s = conj (smallB W s) := by
  rw [← conj_volterraKernel W (2 * π) s, ← conj_volterraKernel W 0 s, ← map_add,
    volterraKernel_add_end hW]

lemma smallB_end_sub (hK : LipschitzWith K γ) (hW : IsTransport γ E W) :
    smallB W (2 * π) - smallB W 0 = Complex.I * smallA W := by
  have hu := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  have h1 : W (2 * π) (ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0)) = basisVec 0 := by
    rw [← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  have h2 : (ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0) : ℕ → ℂ) 0 =
      conj ((W (2 * π) (basisVec 0) : ℕ → ℂ) 0) := by
    rw [← inner_basisVec, ← inner_basisVec, ContinuousLinearMap.adjoint_inner_right,
      inner_conj_symm]
  unfold smallB radialVec smallA
  rw [transport_zero_eq hW, ContinuousLinearMap.one_apply, map_add, h1]
  simp only [lp.coeFn_add, Pi.add_apply, h2, basisVec_coord]
  apply Complex.ext <;> simp <;> ring

lemma intervalIntegrable_conj' {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => conj (f t)) volume a b :=
  ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.1,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.2⟩

lemma kernelRho_intervalIntegrable (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (θ : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) : IntervalIntegrable (kernelRho γ E W θ) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW
    (ContinuousLinearMap.adjoint (W θ) (basisVec 0)) 0 ht
  simp only [transportCoeff_coord_zero] at this
  exact intervalIntegrable_conj' this

lemma smallBDer_intervalIntegrable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) : IntervalIntegrable (smallBDer γ E W) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW (radialVec W) 0 ht
  simp only [transportCoeff_coord_zero] at this
  exact this

lemma schurKernel0_eq_integral (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ s : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    schurKernel0 W θ s = schurKernel0 W θ 0 + ∫ t in (0 : ℝ)..s, schurRho0 γ E W θ t := by
  have h0 : schurKernel0 W θ 0 = Complex.I * (volterraKernel W θ 0 - 1) := if_pos hθ.1
  rw [h0]
  rcases le_or_gt s θ with hsθ | hθs
  · have hc : ∫ t in (0 : ℝ)..s, schurRho0 γ E W θ t =
        ∫ t in (0 : ℝ)..s, Complex.I * kernelRho γ E W θ t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hs.1] at ht
      exact if_pos (ht.2.trans hsθ)
    rw [schurKernel0, if_pos hsθ, hc, intervalIntegral.integral_const_mul,
      volterraKernel_eq_integral hK hW θ hs]
    ring
  · have hθs' : θ ∈ Icc 0 (2 * π) := hθ
    have hi : IntervalIntegrable (kernelRho γ E W θ) volume 0 s :=
      kernelRho_intervalIntegrable hK hW θ hs
    have hiθ : IntervalIntegrable (kernelRho γ E W θ) volume 0 θ :=
      kernelRho_intervalIntegrable hK hW θ hθ
    have hiθs : IntervalIntegrable (kernelRho γ E W θ) volume θ s :=
      (hiθ.symm.trans hi)
    have i1 : IntervalIntegrable (schurRho0 γ E W θ) volume 0 θ := by
      refine (hiθ.const_mul Complex.I).congr fun t ht => ?_
      rw [uIoc_of_le hθ.1] at ht
      exact (if_pos ht.2).symm
    have i2 : IntervalIntegrable (schurRho0 γ E W θ) volume θ s := by
      refine (hiθs.const_mul Complex.I).neg.congr fun t ht => ?_
      rw [uIoc_of_le hθs.le] at ht
      exact (if_neg (not_le.mpr ht.1)).symm
    have c1 : ∫ t in (0 : ℝ)..θ, schurRho0 γ E W θ t =
        ∫ t in (0 : ℝ)..θ, Complex.I * kernelRho γ E W θ t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hθ.1] at ht
      exact if_pos ht.2
    have c2 : ∫ t in θ..s, schurRho0 γ E W θ t =
        ∫ t in θ..s, -(Complex.I * kernelRho γ E W θ t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hθs.le] at ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; simp [schurRho0, kernelRho_diag hK hW hθ]
      · exact if_neg (not_le.mpr h)
    have hdiag := volterraKernel_diag hK hW hθ
    have e1 := volterraKernel_eq_integral hK hW θ hs
    have e2 := volterraKernel_eq_integral hK hW θ hθ
    rw [hdiag] at e2
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, c1, c2,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, schurKernel0, if_neg (not_le.mpr hθs),
      ← intervalIntegral.integral_interval_sub_left hi hiθ, e1]
    linear_combination (2 * Complex.I) * e2

lemma schurBeta_eq (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {s : ℝ}
    (hs : s ∈ Icc 0 (2 * π)) :
    schurBeta W s = schurBeta W 0 + ∫ t in (0 : ℝ)..s, smallBDer γ E W t := by
  rw [schurBeta, schurBeta, smallB_eq hK hW hs]
  ring

lemma schurRho0_intervalIntegrable (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ s : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (schurRho0 γ E W θ) volume 0 s := by
  have hi : IntervalIntegrable (kernelRho γ E W θ) volume 0 s :=
    kernelRho_intervalIntegrable hK hW θ hs
  rcases le_or_gt s θ with hsθ | hθs
  · refine (hi.const_mul Complex.I).congr fun t ht => ?_
    rw [uIoc_of_le hs.1] at ht
    exact (if_pos (ht.2.trans hsθ)).symm
  · have hiθ : IntervalIntegrable (kernelRho γ E W θ) volume 0 θ :=
      kernelRho_intervalIntegrable hK hW θ hθ
    have i1 : IntervalIntegrable (schurRho0 γ E W θ) volume 0 θ := by
      refine (hiθ.const_mul Complex.I).congr fun t ht => ?_
      rw [uIoc_of_le hθ.1] at ht
      exact (if_pos ht.2).symm
    have i2 : IntervalIntegrable (schurRho0 γ E W θ) volume θ s := by
      refine ((hiθ.symm.trans hi).const_mul Complex.I).neg.congr fun t ht => ?_
      rw [uIoc_of_le hθs.le] at ht
      exact (if_neg (not_le.mpr ht.1)).symm
    exact i1.trans i2

lemma schurKernel_eq_integral (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ s : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    schurKernel W θ s = schurKernel W θ 0 + ∫ t in (0 : ℝ)..s, schurRho γ E W θ t := by
  have hi0 := schurRho0_intervalIntegrable hK hW hθ hs
  have hb := smallBDer_intervalIntegrable hK hW hs
  have hi1 : IntervalIntegrable (fun t => schurBeta W θ * conj (smallBDer γ E W t) /
      (smallA W : ℂ)) volume 0 s := ((intervalIntegrable_conj' hb).const_mul _).div_const _
  have hint : ∫ t in (0 : ℝ)..s, schurRho γ E W θ t =
      (∫ t in (0 : ℝ)..s, schurRho0 γ E W θ t) -
        schurBeta W θ * conj (∫ t in (0 : ℝ)..s, smallBDer γ E W t) / (smallA W : ℂ) := by
    unfold schurRho
    rw [intervalIntegral.integral_sub hi0 hi1, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, intervalIntegral_conj]
  rw [hint, schurKernel, schurKernel, schurKernel0_eq_integral hK hW hθ hs,
    schurBeta_eq hK hW hs, map_add]
  ring

lemma schurKernel0_of_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ s : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) (hθs : θ ≤ s) :
    schurKernel0 W θ s = -(Complex.I * (volterraKernel W θ s - 1)) := by
  unfold schurKernel0
  split_ifs with h
  · have : s = θ := le_antisymm h hθs
    subst this
    rw [volterraKernel_diag hK hW hθ]; ring
  · rfl

lemma schurKernel_end_right (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (ha : smallA W ≠ 0) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    schurKernel W θ (2 * π) = schurKernel W θ 0 := by
  have ha' : (smallA W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hb := smallB_end_sub hK hW
  have hk := volterraKernel_add_end hW θ
  have hcb : conj (schurBeta W (2 * π)) = conj (schurBeta W 0) - Complex.I * smallA W := by
    have : schurBeta W (2 * π) = schurBeta W 0 + Complex.I * smallA W := by
      unfold schurBeta; linear_combination hb
    rw [this, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  unfold schurKernel
  rw [schurKernel0_of_le hK hW hθ hθ.2, show schurKernel0 W θ 0 =
    Complex.I * (volterraKernel W θ 0 - 1) from if_pos hθ.1, hcb]
  field_simp
  unfold schurBeta
  linear_combination (-(Complex.I * smallA W)) * hk

lemma schurKernel_end_left (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (ha : smallA W ≠ 0) {s : ℝ} (hs : s ∈ Icc 0 (2 * π)) :
    schurKernel W (2 * π) s = schurKernel W 0 s := by
  have ha' : (smallA W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hb := smallB_end_sub hK hW
  have hk := volterraKernel_end_add hW s
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, by positivity⟩
  unfold schurKernel
  rw [schurKernel0_of_le hK hW h0 hs.1, show schurKernel0 W (2 * π) s =
    Complex.I * (volterraKernel W (2 * π) s - 1) from if_pos hs.2]
  field_simp
  unfold schurBeta
  rw [map_sub, map_ofNat]
  linear_combination (Complex.I * smallA W) * hk - (conj (smallB W s) - 2) * hb

lemma norm_schurBeta_sub_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {B : ℝ}
    (hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B) {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π)) :
    ‖schurBeta W θ₁ - schurBeta W θ₂‖ ≤ B * |θ₁ - θ₂| := by
  rw [schurBeta_eq hK hW h₁, schurBeta_eq hK hW h₂, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (smallBDer_intervalIntegrable hK hW h₁)
      (smallBDer_intervalIntegrable hK hW h₂)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hB t ?_
  have := uIoc_subset_uIcc ht
  rw [mem_uIcc] at this
  rcases this with h | h
  · exact ⟨h₂.1.trans h.1, h.2.trans h₁.2⟩
  · exact ⟨h₁.1.trans h.1, h.2.trans h₂.2⟩

lemma norm_schurRho0_sub_le (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W)
    {θ₁ θ₂ t : ℝ} (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π))
    (ht : t ∈ Icc 0 (2 * π)) :
    ‖schurRho0 γ E W θ₁ t - schurRho0 γ E W θ₂ t‖ ≤ K * (shiftConst * K) * E * |θ₁ - θ₂| := by
  set M := (K : ℝ) * (shiftConst * K) * E with hM
  have hd : ∀ θ ∈ Icc 0 (2 * π), ‖kernelRho γ E W θ t‖ ≤ M * |θ - t| := by
    intro θ hθ
    have := norm_kernelRho_sub_le hK hE hW hθ ht ht
    rwa [kernelRho_diag hK hW ht, sub_zero] at this
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  unfold schurRho0
  split_ifs with ha hb hb
  · rw [← mul_sub, norm_mul, hI, one_mul]; exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht
  · push_neg at hb
    calc ‖Complex.I * kernelRho γ E W θ₁ t - -(Complex.I * kernelRho γ E W θ₂ t)‖
        ≤ ‖kernelRho γ E W θ₁ t‖ + ‖kernelRho γ E W θ₂ t‖ := by
          rw [sub_neg_eq_add, ← mul_add, norm_mul, hI, one_mul]; exact norm_add_le _ _
      _ ≤ M * |θ₁ - t| + M * |θ₂ - t| := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
      _ = M * |θ₁ - θ₂| := by
          rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith),
            abs_of_nonneg (by linarith)]; ring
  · push_neg at ha
    calc ‖-(Complex.I * kernelRho γ E W θ₁ t) - Complex.I * kernelRho γ E W θ₂ t‖
        ≤ ‖kernelRho γ E W θ₁ t‖ + ‖kernelRho γ E W θ₂ t‖ := by
          rw [← neg_add', ← mul_add, norm_neg, norm_mul, hI, one_mul]; exact norm_add_le _ _
      _ ≤ M * |θ₁ - t| + M * |θ₂ - t| := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
      _ = M * |θ₁ - θ₂| := by
          rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith),
            abs_of_neg (by linarith)]; ring
  · rw [neg_sub_neg, ← mul_sub, norm_mul, hI, one_mul, norm_sub_rev]
    exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht

lemma norm_schurRho_sub_le (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W)
    {B : ℝ} (hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B)
    {θ₁ θ₂ t : ℝ} (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π))
    (ht : t ∈ Icc 0 (2 * π)) :
    ‖schurRho γ E W θ₁ t - schurRho γ E W θ₂ t‖ ≤
      (K * (shiftConst * K) * E + B * B / |smallA W|) * |θ₁ - θ₂| := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
  have e : schurRho γ E W θ₁ t - schurRho γ E W θ₂ t =
      (schurRho0 γ E W θ₁ t - schurRho0 γ E W θ₂ t) -
        (schurBeta W θ₁ - schurBeta W θ₂) * conj (smallBDer γ E W t) / (smallA W : ℂ) := by
    unfold schurRho; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h2 : ‖(schurBeta W θ₁ - schurBeta W θ₂) * conj (smallBDer γ E W t) / (smallA W : ℂ)‖ ≤
      B * B / |smallA W| * |θ₁ - θ₂| := by
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rcases eq_or_ne (smallA W) 0 with h0 | h0
    · simp [h0]
    · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (abs_pos.mpr h0)]
      calc ‖schurBeta W θ₁ - schurBeta W θ₂‖ * ‖smallBDer γ E W t‖ ≤ (B * |θ₁ - θ₂|) * B :=
            mul_le_mul (norm_schurBeta_sub_le hK hW hB h₁ h₂) (hB t ht) (norm_nonneg _)
              (by positivity)
        _ = B * B * |θ₁ - θ₂| := by ring
  linarith [norm_schurRho0_sub_le hK hE hW h₁ h₂ ht]

lemma norm_schurRho_le (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W)
    {B : ℝ} (hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B)
    {θ t : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) (ht : t ∈ Icc 0 (2 * π)) :
    ‖schurRho γ E W θ t‖ ≤ K * (shiftConst * K) * E * (2 * π) +
      (‖schurBeta W 0‖ + B * (2 * π)) * B / |smallA W| := by
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, by positivity⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
  have hdist : |θ - t| ≤ 2 * π := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, ht.1, ht.2]
  have hk : ‖kernelRho γ E W θ t‖ ≤ K * (shiftConst * K) * E * (2 * π) := by
    have := norm_kernelRho_sub_le hK hE hW hθ ht ht
    rw [kernelRho_diag hK hW ht, sub_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_left hdist ?_)
    have := shiftConst_nonneg; positivity
  have h0' : ‖schurRho0 γ E W θ t‖ ≤ K * (shiftConst * K) * E * (2 * π) := by
    unfold schurRho0
    split_ifs <;> simpa [norm_mul, Complex.norm_I] using hk
  have hβ : ‖schurBeta W θ‖ ≤ ‖schurBeta W 0‖ + B * (2 * π) := by
    have := norm_schurBeta_sub_le hK hW hB hθ h0
    rw [sub_zero, abs_of_nonneg hθ.1] at this
    have h3 : ‖schurBeta W θ‖ ≤ ‖schurBeta W 0‖ + ‖schurBeta W θ - schurBeta W 0‖ := by
      have := norm_add_le (schurBeta W 0) (schurBeta W θ - schurBeta W 0)
      rwa [add_sub_cancel] at this
    nlinarith [hθ.2]
  have h1 : ‖schurBeta W θ * conj (smallBDer γ E W t) / (smallA W : ℂ)‖ ≤
      (‖schurBeta W 0‖ + B * (2 * π)) * B / |smallA W| := by
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (mul_le_mul hβ (hB t ht) (norm_nonneg _)
      (by positivity)) (abs_nonneg _)
  unfold schurRho
  exact (norm_sub_le _ _).trans (add_le_add h0' h1)

lemma schurRho_aestronglyMeasurable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    AEStronglyMeasurable (schurRho γ E W θ) (volume.restrict (Icc 0 (2 * π))) := by
  have hL : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hi : IntervalIntegrable (schurRho γ E W θ) volume 0 (2 * π) :=
    (schurRho0_intervalIntegrable hK hW hθ hL).sub
      (((intervalIntegrable_conj' (smallBDer_intervalIntegrable hK hW hL)).const_mul _).div_const _)
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp hi).aestronglyMeasurable

/-- **Kernel estimate.** For a bounded measurable `g` with `∫₀^L g = 0`, primitive `G`, and any
constant `c`, the corrected kernel form is bounded by `M (∫₀^L |G - c|)²` with
`M = K (κ K) E + B² / |a_E|`, where `B` bounds `|b'_E|`. -/
theorem norm_schurKernel_form_le (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W)
    (ha : smallA W ≠ 0) {B : ℝ} (hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B)
    {g : ℝ → ℂ} {Bg : ℝ} (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ t in (0 : ℝ)..(2 * π), g t = 0) (c : ℂ) :
    ‖∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s‖ ≤
      (K * (shiftConst * K) * E + B * B / |smallA W|) *
        (∫ t in (0 : ℝ)..(2 * π), ‖(∫ u in (0 : ℝ)..t, g u) - c‖) ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, by positivity⟩)
  have hM : 0 ≤ (K : ℝ) * (shiftConst * K) * E + B * B / |smallA W| := by
    have := shiftConst_nonneg; positivity
  exact norm_kernel_form_le (by positivity) hM hg hgB
    (fun θ hθ => schurRho_aestronglyMeasurable hK hW hθ)
    (fun θ hθ t ht => norm_schurRho_le hK hE hW hB hθ ht)
    (fun θ hθ s hs => schurKernel_eq_integral hK hW hθ hs)
    (fun θ₁ h₁ θ₂ h₂ t ht => norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht)
    (fun θ hθ => schurKernel_end_right hK hW ha hθ)
    (fun s hs => schurKernel_end_left hK hW ha hs) hG c

lemma volterraKernel_continuousOn (hW : IsTransport γ E W) (θ : ℝ) :
    ContinuousOn (volterraKernel W θ) (Icc 0 (2 * π)) := by
  have h1 : ContinuousOn (fun s => ContinuousLinearMap.adjoint (W s)) (Icc 0 (2 * π)) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.comp_continuousOn hW.1
  have h2 : ContinuousOn (fun s => W θ (ContinuousLinearMap.adjoint (W s) (basisVec 0)))
      (Icc 0 (2 * π)) := (W θ).continuous.comp_continuousOn (h1.clm_apply continuousOn_const)
  exact continuousOn_const.inner h2

lemma smallB_continuousOn (hW : IsTransport γ E W) :
    ContinuousOn (smallB W) (Icc 0 (2 * π)) := by
  have h : ContinuousOn (fun s => ⟪basisVec 0, W s (radialVec W)⟫_ℂ) (Icc 0 (2 * π)) :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  refine h.congr fun s _ => ?_
  beta_reduce
  rw [smallB, inner_basisVec]

/-- The kernel `r` acting on `g`, in terms of the Volterra operators. -/
lemma integral_schurKernel_mul_eq (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {g : ℝ → ℂ} (hgi : IntervalIntegrable g volume 0 (2 * π))
    (hG : ∫ t in (0 : ℝ)..(2 * π), g t = 0) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s =
      Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) - 2 * Complex.I * (∫ s in (0 : ℝ)..θ, g s) -
        schurBeta W θ * (∫ s in (0 : ℝ)..(2 * π), conj (smallB W s) * g s) / (smallA W : ℂ) := by
  have hL : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hsub1 : uIcc 0 θ ⊆ uIcc 0 (2 * π) := by
    rw [uIcc_of_le hθ.1, uIcc_of_le hL.1]; exact Icc_subset_Icc le_rfl hθ.2
  have hsub2 : uIcc θ (2 * π) ⊆ uIcc 0 (2 * π) := by
    rw [uIcc_of_le hθ.2, uIcc_of_le hL.1]; exact Icc_subset_Icc hθ.1 le_rfl
  have hwc := volterraKernel_continuousOn hW θ
  rw [← uIcc_of_le hL.1] at hwc
  have hg1 : IntervalIntegrable g volume 0 θ := hgi.mono_set hsub1
  have hg2 : IntervalIntegrable g volume θ (2 * π) := hgi.mono_set hsub2
  have hw1 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume 0 θ :=
    hg1.continuousOn_mul (hwc.mono hsub1)
  have hw2 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume θ (2 * π) :=
    hg2.continuousOn_mul (hwc.mono hsub2)
  have A1 : IntervalIntegrable (fun s => schurKernel0 W θ s * g s) volume 0 θ := by
    refine ((hw1.sub hg1).const_mul Complex.I).congr fun s hs => ?_
    rw [uIoc_of_le hθ.1] at hs
    simp only [schurKernel0, if_pos hs.2]; ring
  have A2 : IntervalIntegrable (fun s => schurKernel0 W θ s * g s) volume θ (2 * π) := by
    refine ((hw2.sub hg2).const_mul Complex.I).neg.congr fun s hs => ?_
    rw [uIoc_of_le hθ.2] at hs
    simp only [schurKernel0, if_neg (not_le.mpr hs.1), Pi.neg_apply]; ring
  have I1 : ∫ s in (0 : ℝ)..θ, schurKernel0 W θ s * g s =
      Complex.I * (volterraOp W g θ - ∫ s in (0 : ℝ)..θ, g s) := by
    rw [intervalIntegral.integral_congr (g := fun s => Complex.I *
      (volterraKernel W θ s * g s - g s)) (fun s hs => by
        rw [uIcc_of_le hθ.1] at hs
        simp only [schurKernel0, if_pos hs.2]; ring),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hw1 hg1]
    rfl
  have hadj : volterraOpAdj W g θ = ∫ s in θ..(2 * π), volterraKernel W θ s * g s := by
    unfold volterraOpAdj
    simp only [conj_volterraKernel]
  have I2 : ∫ s in θ..(2 * π), schurKernel0 W θ s * g s =
      -(Complex.I * (volterraOpAdj W g θ - ∫ s in θ..(2 * π), g s)) := by
    rw [intervalIntegral.integral_congr (g := fun s => -(Complex.I *
      (volterraKernel W θ s * g s - g s))) (fun s hs => by
        rw [uIcc_of_le hθ.2] at hs
        simp only [schurKernel0_of_le hK hW hθ hs.1]; ring),
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hw2 hg2, hadj]
  have hsplit : ∫ s in θ..(2 * π), g s = -∫ s in (0 : ℝ)..θ, g s := by
    have := intervalIntegral.integral_add_adjacent_intervals hg1 hg2
    rw [hG] at this
    linear_combination this
  have hbc : ContinuousOn (fun s => conj (smallB W s)) (uIcc 0 (2 * π)) := by
    rw [uIcc_of_le hL.1]
    exact Complex.continuous_conj.comp_continuousOn (smallB_continuousOn hW)
  have hB1 : IntervalIntegrable (fun s => conj (smallB W s) * g s) volume 0 (2 * π) :=
    hgi.continuousOn_mul hbc
  have hB2 : IntervalIntegrable (fun s => schurBeta W θ * (conj (schurBeta W s) * g s) /
      (smallA W : ℂ)) volume 0 (2 * π) := by
    refine (((hB1.sub (hgi.const_mul 2)).const_mul (schurBeta W θ)).div_const
      (smallA W : ℂ)).congr fun s _ => ?_
    simp only [schurBeta, map_sub, map_ofNat]; ring
  have hrk : ∫ s in (0 : ℝ)..(2 * π), schurBeta W θ * (conj (schurBeta W s) * g s) /
      (smallA W : ℂ) = schurBeta W θ *
        (∫ s in (0 : ℝ)..(2 * π), conj (smallB W s) * g s) / (smallA W : ℂ) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    congr 2
    rw [intervalIntegral.integral_congr (g := fun s => conj (smallB W s) * g s - 2 * g s)
      (fun s _ => by simp only [schurBeta, map_sub, map_ofNat]; ring),
      intervalIntegral.integral_sub hB1 (hgi.const_mul 2), intervalIntegral.integral_const_mul,
      hG, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr (g := fun s => schurKernel0 W θ s * g s -
      schurBeta W θ * (conj (schurBeta W s) * g s) / (smallA W : ℂ))
      (fun s _ => by simp only [schurKernel]; ring),
    intervalIntegral.integral_sub (A1.trans A2) hB2, hrk,
    ← intervalIntegral.integral_add_adjacent_intervals A1 A2, I1, I2, hsplit]
  ring

lemma norm_smallBDer_le_sqrt (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * π)) : ‖smallBDer γ E W t‖ ≤ Real.sqrt E * K * 2 := by
  refine (norm_coeffTerm_le (norm_deriv_le_of_lipschitz hK)).trans ?_
  have h1 : ‖(W t (radialVec W) : ℕ → ℂ) 1‖ ≤ 2 :=
    (norm_coord_le _ _).trans (((W t).le_opNorm _).trans
      ((mul_le_mul (norm_transport_le_one hK hW ht) (norm_radialVec_le hK hW) (norm_nonneg _)
        zero_le_one).trans (by norm_num)))
  gcongr

/-- `θ ↦ ∫₀^L r(θ, s) g(s) ds` is continuous on `[0, L]`. -/
lemma continuousOn_integral_schurKernel_mul (hK : LipschitzWith K γ) (hE : 0 ≤ E)
    (hW : IsTransport γ E W) (ha : smallA W ≠ 0) {g : ℝ → ℂ} {Bg : ℝ}
    (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ t in (0 : ℝ)..(2 * π), g t = 0) :
    ContinuousOn (fun θ => ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s) (Icc 0 (2 * π)) := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, hL⟩
  have hL' : (2 * π) ∈ Icc 0 (2 * π) := ⟨hL, le_rfl⟩
  set B := Real.sqrt E * K * 2 with hBdef
  have hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B := fun t ht =>
    norm_smallBDer_le_sqrt hK hW ht
  set M := (K : ℝ) * (shiftConst * K) * E + B * B / |smallA W| with hM
  set Bρ := (K : ℝ) * (shiftConst * K) * E * (2 * π) +
      (‖schurBeta W 0‖ + B * (2 * π)) * B / |smallA W|
  have hgr : AEStronglyMeasurable g (volume.restrict (Icc 0 (2 * π))) := hg.restrict
  have hgBr : ∀ t ∈ Icc 0 (2 * π), ‖g t‖ ≤ Bg := fun t _ => hgB t
  have hGc := continuousOn_primitive_of_bound hL hgr hgBr
  have hrep : ∀ θ ∈ Icc 0 (2 * π), ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s =
      -∫ t in (0 : ℝ)..(2 * π), schurRho γ E W θ t * ((∫ u in (0 : ℝ)..t, g u) - 0) :=
    fun θ hθ => kernel_integral_eq hL hgr hgBr (schurRho_aestronglyMeasurable hK hW hθ)
      (fun t ht => norm_schurRho_le hK hE hW hB hθ ht)
      (fun s hs => schurKernel_eq_integral hK hW hθ hs) (schurKernel_end_right hK hW ha hθ) hG 0
  have hint : ∀ θ ∈ Icc 0 (2 * π), IntervalIntegrable
      (fun t => schurRho γ E W θ t * ((∫ u in (0 : ℝ)..t, g u) - 0)) volume 0 (2 * π) := by
    intro θ hθ
    refine intervalIntegrable_of_restrict_bound
      ((schurRho_aestronglyMeasurable hK hW hθ).mul
        ((hGc.sub continuousOn_const).aestronglyMeasurable measurableSet_Icc))
      (B := Bρ * (Bg * (2 * π))) (fun t ht => ?_) h0 hL'
    simp only [Pi.mul_apply, Pi.sub_apply, sub_zero]
    rw [norm_mul]
    exact mul_le_mul (norm_schurRho_le hK hE hW hB hθ ht) (norm_primitive_le hgBr ht)
      (norm_nonneg _) ((norm_nonneg _).trans (norm_schurRho_le hK hE hW hB hθ ht))
  have hBg : 0 ≤ Bg := (norm_nonneg _).trans (hgB 0)
  have hM0 : 0 ≤ M := by have := shiftConst_nonneg; positivity
  refine (LipschitzOnWith.of_dist_le_mul (K := (M * (Bg * (2 * π)) * (2 * π)).toNNReal)
    fun θ₁ h₁ θ₂ h₂ => ?_).continuousOn
  rw [hrep θ₁ h₁, hrep θ₂ h₂, dist_eq_norm, Real.dist_eq,
    Real.coe_toNNReal _ (by positivity), neg_sub_neg,
    ← intervalIntegral.integral_sub (hint θ₂ h₂) (hint θ₁ h₁)]
  have hb : ∀ t ∈ Ι (0 : ℝ) (2 * π), ‖schurRho γ E W θ₂ t * ((∫ u in (0 : ℝ)..t, g u) - 0) -
      schurRho γ E W θ₁ t * ((∫ u in (0 : ℝ)..t, g u) - 0)‖ ≤ M * |θ₁ - θ₂| * (Bg * (2 * π)) := by
    intro t ht
    rw [uIoc_of_le hL] at ht
    have ht' : t ∈ Icc 0 (2 * π) := ⟨ht.1.le, ht.2⟩
    rw [← sub_mul, norm_mul, sub_zero, norm_sub_rev]
    exact mul_le_mul (norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht') (norm_primitive_le hgBr ht')
      (norm_nonneg _) (by positivity)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg hL]; ring

/-- **Splitting of the Schur complement.** For a bounded measurable `g` with `∫₀^L g = 0` and
any `h` with `conj(g) h` integrable,

  `Re ∫ conj(g)(2h + i(T_E - T_E^*) g) - |∫ conj(b_E) g|² / a_E
      = Re ∫ conj(g)(2h + 2i G) + Re ∫ conj(g(θ)) ∫ r(θ, s) g(s) ds dθ`. -/
theorem re_volterra_sub_schur_eq (hK : LipschitzWith K γ) (hE : 0 ≤ E)
    (hW : IsTransport γ E W) (ha : smallA W ≠ 0) {g : ℝ → ℂ} {Bg : ℝ}
    (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ t in (0 : ℝ)..(2 * π), g t = 0) {h : ℝ → ℂ}
    (hh : IntervalIntegrable (fun θ => conj (g θ) * h θ) volume 0 (2 * π)) :
    (∫ θ in (0 : ℝ)..(2 * π), conj (g θ) *
        (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ))).re -
      ‖∫ θ in (0 : ℝ)..(2 * π), conj (smallB W θ) * g θ‖ ^ 2 / smallA W =
    (∫ θ in (0 : ℝ)..(2 * π), conj (g θ) *
        (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s))).re +
      (∫ θ in (0 : ℝ)..(2 * π), conj (g θ) *
        ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s).re := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hgi : IntervalIntegrable g volume 0 (2 * π) := intervalIntegrable_of_norm_le hg hgB _ _
  have hcg : IntervalIntegrable (fun θ => conj (g θ)) volume 0 (2 * π) :=
    intervalIntegrable_conj' hgi
  set Y := ∫ θ in (0 : ℝ)..(2 * π), conj (smallB W θ) * g θ with hY
  set Φ := fun θ => ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s with hΦ
  have hΦc : ContinuousOn Φ (uIcc 0 (2 * π)) := by
    rw [uIcc_of_le hL]; exact continuousOn_integral_schurKernel_mul hK hE hW ha hg hgB hG
  have hGc : ContinuousOn (fun θ => ∫ s in (0 : ℝ)..θ, g s) (uIcc 0 (2 * π)) := by
    rw [uIcc_of_le hL]
    exact continuousOn_primitive_of_bound hL hg.restrict (fun t _ => hgB t)
  have hβc : ContinuousOn (schurBeta W) (uIcc 0 (2 * π)) := by
    rw [uIcc_of_le hL]; exact (smallB_continuousOn hW).sub continuousOn_const
  have i1 : IntervalIntegrable (fun θ => conj (g θ) *
      (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s))) volume 0 (2 * π) := by
    refine ((hh.const_mul 2).add (hcg.mul_continuousOn
      ((hGc.const_smul (2 : ℂ)).const_smul Complex.I))).congr fun θ _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  have i2 : IntervalIntegrable (fun θ => conj (g θ) * Φ θ) volume 0 (2 * π) :=
    hcg.mul_continuousOn hΦc
  have i3 : IntervalIntegrable (fun θ => conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ))
      volume 0 (2 * π) := ((hcg.mul_continuousOn hβc).mul_const Y).div_const _
  have hpt : ∀ θ ∈ uIcc 0 (2 * π), conj (g θ) *
      (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ)) =
      conj (g θ) * (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s)) + conj (g θ) * Φ θ +
        conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ) := by
    intro θ hθ
    rw [uIcc_of_le hL] at hθ
    simp only [hΦ, integral_schurKernel_mul_eq hK hW hgi hG hθ, hY]
    ring
  have h3 : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ) =
      conj Y * Y / (smallA W : ℂ) := by
    have hbc : ContinuousOn (fun s => conj (smallB W s)) (uIcc 0 (2 * π)) := by
      rw [uIcc_of_le hL]
      exact Complex.continuous_conj.comp_continuousOn (smallB_continuousOn hW)
    have hB1 : IntervalIntegrable (fun s => conj (smallB W s) * g s) volume 0 (2 * π) :=
      hgi.continuousOn_mul hbc
    rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const]
    congr 2
    rw [intervalIntegral.integral_congr (g := fun θ => conj (conj (smallB W θ) * g θ) -
        2 * conj (g θ)) (fun θ _ => by simp only [schurBeta, map_mul, Complex.conj_conj]; ring),
      intervalIntegral.integral_sub (intervalIntegrable_conj' hB1) (hcg.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral_conj, intervalIntegral_conj, hG,
      map_zero, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (i1.add i2) i3,
    intervalIntegral.integral_add i1 i2, h3, Complex.conj_mul', Complex.add_re, Complex.add_re,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  ring

end PolyaNeumann