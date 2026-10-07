module

public import RequestProject.ReconBessel
public import RequestProject.ReconBasic

/-!
# Angular Fourier modes of smooth functions and Bessel's equation

For a `C²` function `v` on `ℂ`, a centre `x₀` and `n ∈ ℤ`, the angular mode
`m(r) = ∫₀^{2π} e^{-inθ} v(x₀ + r e^{iθ}) dθ` is `C²` in `r`, and
`m'' + m'/r - n² m / r² = ∫₀^{2π} e^{-inθ} Δv(x₀ + r e^{iθ}) dθ` (`angMode_lap`). In particular
if `(Δ + E) v = 0` on the circle of radius `r ≠ 0`, the mode satisfies Bessel's equation there.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace PolyaNeumann

/-! ### Differentiation under the integral sign -/

lemma hasDerivAt_intervalIntegral_param {F F' : ℝ → ℝ → ℂ}
    (hF : ∀ r θ, HasDerivAt (fun r => F r θ) (F' r θ) r)
    (hFc : Continuous (Function.uncurry F)) (hF'c : Continuous (Function.uncurry F'))
    (a b r₀ : ℝ) :
    HasDerivAt (fun r => ∫ θ in a..b, F r θ) (∫ θ in a..b, F' r₀ θ) r₀ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc :
    IsCompact (Icc (r₀ - 1) (r₀ + 1) ×ˢ uIcc a b)).exists_bound_of_continuousOn hF'c.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (s := Ioo (r₀ - 1) (r₀ + 1)) (Ioo_mem_nhds (by linarith) (by linarith)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_).2
  · exact Eventually.of_forall fun r =>
      (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hFc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun θ hθ r hr =>
      hC (r, θ) ⟨⟨hr.1.le, hr.2.le⟩, uIoc_subset_uIcc hθ⟩
  · exact Eventually.of_forall fun θ _ r _ => hF r θ

/-! ### The modes -/

/-- `e(θ) = e^{iθ}`. -/
def eI (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

lemma continuous_eI : Continuous eI := by unfold eI; fun_prop

lemma hasDerivAt_eI (θ : ℝ) : HasDerivAt eI (Complex.I * eI θ) θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp
  convert h using 1
  · funext x; simp [eI]
  · simp [eI]; ring

lemma eI_two_pi : eI (2 * π) = eI 0 := by
  simp [eI]

/-- The angular character `e^{-inθ}`. -/
def angChar (n : ℤ) (θ : ℝ) : ℂ := Complex.exp (-(n * θ * Complex.I))

lemma continuous_angChar (n : ℤ) : Continuous (angChar n) := by unfold angChar; fun_prop

lemma hasDerivAt_angChar (n : ℤ) (θ : ℝ) :
    HasDerivAt (angChar n) (-(n * Complex.I) * angChar n θ) θ := by
  have h := (((hasDerivAt_id θ).ofReal_comp.const_mul (n : ℂ)).mul_const Complex.I).neg.cexp
  convert h using 1
  · funext x; simp [angChar]
  · simp only [angChar, Pi.neg_apply, id, Complex.ofReal_one]; ring

lemma angChar_two_pi (n : ℤ) : angChar n (2 * π) = angChar n 0 := by
  simp only [angChar, Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero]
  rw [Complex.exp_eq_one_iff]
  exact ⟨-n, by push_cast; ring⟩

/-- The point `x₀ + r e^{iθ}`. -/
def circPt (x₀ : ℂ) (r θ : ℝ) : ℂ := x₀ + r * eI θ

lemma continuous_circPt (x₀ : ℂ) : Continuous (Function.uncurry (circPt x₀)) := by
  unfold circPt; exact continuous_const.add
    ((Complex.continuous_ofReal.comp continuous_fst).mul (continuous_eI.comp continuous_snd))

lemma hasDerivAt_circPt_r (x₀ : ℂ) (r θ : ℝ) :
    HasDerivAt (fun r => circPt x₀ r θ) (eI θ) r := by
  have h := ((hasDerivAt_id r).ofReal_comp.mul_const (eI θ)).const_add x₀
  simpa [circPt] using h

lemma hasDerivAt_circPt_θ (x₀ : ℂ) (r θ : ℝ) :
    HasDerivAt (fun θ => circPt x₀ r θ) (r * (Complex.I * eI θ)) θ := by
  have h := ((hasDerivAt_eI θ).const_mul (r : ℂ)).const_add x₀
  simpa [circPt] using h

/-- The angular mode `m(r) = ∫₀^{2π} e^{-inθ} v(x₀ + r e^{iθ}) dθ`. -/
def angMode (v : ℂ → ℂ) (x₀ : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * π, angChar n θ * v (circPt x₀ r θ)

/-- The radial derivative of the mode. -/
def angMode1 (v : ℂ → ℂ) (x₀ : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * π, angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ)

/-- The second radial derivative of the mode. -/
def angMode2 (v : ℂ → ℂ) (x₀ : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * π, angChar n θ * fderiv ℝ (fderiv ℝ v) (circPt x₀ r θ) (eI θ) (eI θ)

section Smooth

variable {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) (x₀ : ℂ) (n : ℤ)
include hv

lemma contDiff_fderiv_of_two : ContDiff ℝ 1 (fderiv ℝ v) :=
  hv.fderiv_right (m := 1) (by norm_num)

lemma continuous_fderiv_fderiv_of_two : Continuous (fderiv ℝ (fderiv ℝ v)) :=
  (contDiff_fderiv_of_two hv).continuous_fderiv one_ne_zero

lemma hasDerivAt_angMode (r : ℝ) : HasDerivAt (angMode v x₀ n) (angMode1 v x₀ n r) r := by
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  refine hasDerivAt_intervalIntegral_param (F := fun r θ => angChar n θ * v (circPt x₀ r θ))
    (F' := fun r θ => angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ)) (fun r θ => ?_) ?_ ?_ _ _ r
  · exact ((hd _).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_circPt_r x₀ r θ)).const_mul _
  · exact ((continuous_angChar n).comp continuous_snd).mul (hv.continuous.comp (continuous_circPt x₀))
  · exact ((continuous_angChar n).comp continuous_snd).mul
      (((hv.continuous_fderiv (by norm_num)).comp (continuous_circPt x₀)).clm_apply
        (continuous_eI.comp continuous_snd))

lemma hasDerivAt_angMode1 (r : ℝ) : HasDerivAt (angMode1 v x₀ n) (angMode2 v x₀ n r) r := by
  have hd : Differentiable ℝ (fderiv ℝ v) := (contDiff_fderiv_of_two hv).differentiable one_ne_zero
  refine hasDerivAt_intervalIntegral_param
    (F := fun r θ => angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ))
    (F' := fun r θ => angChar n θ * fderiv ℝ (fderiv ℝ v) (circPt x₀ r θ) (eI θ) (eI θ))
    (fun r θ => ?_) ?_ ?_ _ _ r
  · have h1 := (hd _).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_circPt_r x₀ r θ)
    have h2 := h1.clm_apply (hasDerivAt_const r (eI θ))
    simp only [ContinuousLinearMap.map_zero, add_zero] at h2
    exact h2.const_mul _
  · exact ((continuous_angChar n).comp continuous_snd).mul
      (((hv.continuous_fderiv (by norm_num)).comp (continuous_circPt x₀)).clm_apply
        (continuous_eI.comp continuous_snd))
  · exact ((continuous_angChar n).comp continuous_snd).mul
      ((((continuous_fderiv_fderiv_of_two hv).comp (continuous_circPt x₀)).clm_apply
        (continuous_eI.comp continuous_snd)).clm_apply (continuous_eI.comp continuous_snd))

/-- `Δv = D²v(1,1) + D²v(i,i)`. -/
lemma lap_eq_fderiv_fderiv (p : ℂ) :
    lap v p = fderiv ℝ (fderiv ℝ v) p 1 1 + fderiv ℝ (fderiv ℝ v) p Complex.I Complex.I := by
  have hd : Differentiable ℝ (fderiv ℝ v) := (contDiff_fderiv_of_two hv).differentiable one_ne_zero
  have key : ∀ w : ℂ, dirD (dirD v w) w p = fderiv ℝ (fderiv ℝ v) p w w := fun w => by
    unfold dirD
    rw [fderiv_clm_apply (hd p) (differentiableAt_const w)]
    simp
  rw [lap, key, key]

omit hv in
/-- Rotation invariance of the Laplacian: `D²v(e,e) + D²v(ie,ie) = D²v(1,1) + D²v(i,i)` for
`e = e^{iθ}`. -/
lemma fderiv_fderiv_rot (p : ℂ) (θ : ℝ) :
    fderiv ℝ (fderiv ℝ v) p (eI θ) (eI θ) +
      fderiv ℝ (fderiv ℝ v) p (Complex.I * eI θ) (Complex.I * eI θ) =
    fderiv ℝ (fderiv ℝ v) p 1 1 + fderiv ℝ (fderiv ℝ v) p Complex.I Complex.I := by
  set D := fderiv ℝ (fderiv ℝ v) p
  have he : eI θ = (Real.cos θ) • (1 : ℂ) + (Real.sin θ) • Complex.I := by
    simp only [eI, Complex.exp_mul_I, Complex.real_smul, mul_one, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have hie : Complex.I * eI θ = (-Real.sin θ) • (1 : ℂ) + (Real.cos θ) • Complex.I := by
    rw [he]
    simp only [Complex.real_smul, mul_one, Complex.ofReal_neg]
    ring_nf
    rw [Complex.I_sq]; ring
  rw [hie, he]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [Complex.real_smul, Complex.ofReal_neg]
  have h1 : ((Real.cos θ : ℂ)) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  linear_combination (D 1 1 + D Complex.I Complex.I) * h1

omit hv in
/-- Periodic integration by parts against the angular character. -/
lemma integral_angChar_mul_deriv {h h' : ℝ → ℂ} (hh : ∀ θ, HasDerivAt h (h' θ) θ)
    (hh'c : Continuous h') (hper : h (2 * π) = h 0) :
    ∫ θ in (0 : ℝ)..2 * π, angChar n θ * h' θ =
      (n * Complex.I) * ∫ θ in (0 : ℝ)..2 * π, angChar n θ * h θ := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * π)
    (u := angChar n) (u' := fun θ => -(n * Complex.I) * angChar n θ) (v := h) (v' := h')
    (fun θ _ => hasDerivAt_angChar n θ) (fun θ _ => hh θ)
    ((continuous_const.mul (continuous_angChar n)).intervalIntegrable _ _)
    (hh'c.intervalIntegrable _ _)
  rw [hibp, angChar_two_pi, hper, sub_self, zero_sub, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_neg]
  congr 1; funext θ; ring

omit hv in
lemma continuous_angChar_mul {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous fun θ => angChar n θ * f θ := (continuous_angChar n).mul hf

/-- The polar form of the Laplacian on the angular modes:
`m'' + m'/r - n² m / r² = ∫₀^{2π} e^{-inθ} Δv(x₀ + r e^{iθ}) dθ` for `r ≠ 0`. -/
theorem angMode_lap {r : ℝ} (hr : r ≠ 0) :
    angMode2 v x₀ n r + angMode1 v x₀ n r / r - ((n : ℂ) ^ 2 / (r : ℂ) ^ 2) * angMode v x₀ n r =
      ∫ θ in (0 : ℝ)..2 * π, angChar n θ * lap v (circPt x₀ r θ) := by
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ v) := (contDiff_fderiv_of_two hv).differentiable one_ne_zero
  have hc1 : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ v)) := continuous_fderiv_fderiv_of_two hv
  have hcp : Continuous fun θ => circPt x₀ r θ :=
    (continuous_circPt x₀).comp (continuous_const.prodMk continuous_id)
  set D := fderiv ℝ (fderiv ℝ v)
  set g : ℝ → ℂ := fun θ => v (circPt x₀ r θ)
  set g1 : ℝ → ℂ := fun θ => fderiv ℝ v (circPt x₀ r θ) (r * (Complex.I * eI θ))
  set g2 : ℝ → ℂ := fun θ => D (circPt x₀ r θ) (r * (Complex.I * eI θ)) (r * (Complex.I * eI θ)) +
    fderiv ℝ v (circPt x₀ r θ) (r * (Complex.I * (Complex.I * eI θ)))
  have hg : ∀ θ, HasDerivAt g (g1 θ) θ := fun θ =>
    (hd _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circPt_θ x₀ r θ)
  have hg1 : ∀ θ, HasDerivAt g1 (g2 θ) θ := fun θ => by
    have h1 := (hd1 _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circPt_θ x₀ r θ)
    have h2 : HasDerivAt (fun θ => (r : ℂ) * (Complex.I * eI θ))
        (r * (Complex.I * (Complex.I * eI θ))) θ :=
      ((hasDerivAt_eI θ).const_mul Complex.I).const_mul (r : ℂ)
    have h3 := h1.clm_apply h2
    convert h3 using 1 <;> rfl
  have hg1c : Continuous g1 :=
    (hc1.comp hcp).clm_apply (continuous_const.mul (continuous_const.mul continuous_eI))
  have hg2c : Continuous g2 :=
    (((hc2.comp hcp).clm_apply (continuous_const.mul (continuous_const.mul continuous_eI))).clm_apply
      (continuous_const.mul (continuous_const.mul continuous_eI))).add
      ((hc1.comp hcp).clm_apply (continuous_const.mul (continuous_const.mul
        (continuous_const.mul continuous_eI))))
  have hper : ∀ f : ℂ → ℂ, (fun θ => f (circPt x₀ r θ)) (2 * π) =
      (fun θ => f (circPt x₀ r θ)) 0 := fun f => by simp only [circPt, eI_two_pi]
  have hg1per : g1 (2 * π) = g1 0 := by simp only [g1, circPt, eI_two_pi]
  -- two periodic integrations by parts
  have hI2 : ∫ θ in (0 : ℝ)..2 * π, angChar n θ * g2 θ =
      -((n : ℂ) ^ 2) * angMode v x₀ n r := by
    rw [integral_angChar_mul_deriv n hg1 hg2c hg1per,
      integral_angChar_mul_deriv n hg hg1c (hper v)]
    simp only [angMode]
    ring_nf
    rw [Complex.I_sq]; ring
  -- the pointwise identity
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hpt : ∀ θ, angChar n θ * lap v (circPt x₀ r θ) =
      angChar n θ * D (circPt x₀ r θ) (eI θ) (eI θ) +
        (angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ)) / r +
        (angChar n θ * g2 θ) / (r : ℂ) ^ 2 := fun θ => by
    rw [lap_eq_fderiv_fderiv hv, ← fderiv_fderiv_rot _ θ]
    have hsm : ∀ (L : ℂ →L[ℝ] ℂ) (w : ℂ), L ((r : ℂ) * w) = (r : ℂ) * L w := fun L w => by
      rw [← Complex.real_smul, map_smul, Complex.real_smul]
    have hsm2 : ∀ (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (w z : ℂ), B ((r : ℂ) * w) z = (r : ℂ) * B w z :=
      fun B w z => by
        rw [← Complex.real_smul, map_smul, ContinuousLinearMap.smul_apply, Complex.real_smul]
    have hII : Complex.I * (Complex.I * eI θ) = -eI θ := by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    simp only [g2, D]
    rw [hsm2, hsm, hsm, hII, map_neg]
    field_simp
    ring
  -- integrate
  have hi1 : IntervalIntegrable (fun θ => angChar n θ * D (circPt x₀ r θ) (eI θ) (eI θ))
      volume 0 (2 * π) :=
    (continuous_angChar_mul n (((hc2.comp hcp).clm_apply continuous_eI).clm_apply
      continuous_eI)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => (angChar n θ * fderiv ℝ v (circPt x₀ r θ) (eI θ)) / r)
      volume 0 (2 * π) :=
    ((continuous_angChar_mul n ((hc1.comp hcp).clm_apply continuous_eI)).div_const _).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun θ => (angChar n θ * g2 θ) / (r : ℂ) ^ 2) volume 0 (2 * π) :=
    ((continuous_angChar_mul n hg2c).div_const _).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_add
    (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_div,
    intervalIntegral.integral_div, hI2]
  simp only [angMode2, angMode1, D]
  field_simp
  ring

/-- Bessel's equation for the modes of a solution of `(Δ + E) v = 0` on a circle. -/
theorem angMode_bessel {E r : ℝ} (hr : r ≠ 0)
    (hhelm : ∀ θ, lap v (circPt x₀ r θ) + E * v (circPt x₀ r θ) = 0) :
    angMode2 v x₀ n r = -(angMode1 v x₀ n r / r) -
      ((E - (n : ℝ) ^ 2 / r ^ 2 : ℝ) : ℂ) * angMode v x₀ n r := by
  have h := angMode_lap hv x₀ n hr
  have h2 : ∫ θ in (0 : ℝ)..2 * π, angChar n θ * lap v (circPt x₀ r θ) =
      -(E : ℂ) * angMode v x₀ n r := by
    simp only [angMode]
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext θ
    have := hhelm θ
    linear_combination angChar n θ * this
  rw [h2] at h
  push_cast
  linear_combination h

end Smooth

end PolyaNeumann
