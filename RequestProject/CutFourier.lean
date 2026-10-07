module

public import RequestProject.CutPhase
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries

/-!
# A smooth periodic version of the cut argument and its Fourier series

Fix a cut direction `e^{iε}` (`0 < ε < 2π`) and a radius `r > 0`. We construct a smooth
`2π`-periodic function `h` with `h(t) = argCut ε (e^{it})` and `h'(t) = 1` whenever `e^{it}` is at
distance at least `r` from `e^{iε}`, and expand it in an absolutely convergent Fourier series
`h(t) = ∑ₖ cₖ e^{ikt}` with `∑ₖ |k| |cₖ| < ∞`. In real form (`c_{-k} = conj cₖ`), for such
`z = e^{it}`: `argCut ε z = ∑_{n ≥ 1} 2 Re(cₙ (zⁿ - 1))` and `1 = ∑_{n ≥ 1} 2 Re(i n cₙ zⁿ)`.
-/

@[expose] public section

open MeasureTheory Set Filter AddCircle
open scoped Real Topology ComplexConjugate

noncomputable section

namespace PolyaNeumann

lemma two_pi_pos' : (0 : ℝ) < 2 * π := by positivity

lemma norm_fourier_coe (n : ℤ) (x : ℝ) : ‖fourier (T := 2 * π) n (x : AddCircle (2 * π))‖ = 1 := by
  rw [fourier_coe_apply]
  have : (2 * (π : ℂ) * Complex.I * n * x / (2 * π : ℝ)) = ((n * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma fourier_coe_two_pi (n : ℤ) (x : ℝ) :
    fourier (T := 2 * π) n (x : AddCircle (2 * π)) = Complex.exp (n * x * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- Bound for Fourier coefficients on `[0, 2π]`. -/
lemma norm_fourierCoeffOn_le {f : ℝ → ℂ} {M : ℝ} (hf : ∀ x ∈ Icc 0 (2 * π), ‖f x‖ ≤ M) (k : ℤ) :
    ‖fourierCoeffOn two_pi_pos' f k‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have h2 : ‖∫ x in (0 : ℝ)..(2 * π), fourier (T := 2 * π) (-k) (x : AddCircle (2 * π)) • f x‖ ≤
      M * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    rw [uIoc_of_le two_pi_pos'.le] at hx
    rw [norm_smul, norm_fourier_coe, one_mul]
    exact hf x ⟨hx.1.le, hx.2⟩
  rw [sub_zero, abs_of_pos two_pi_pos'] at h2
  rw [sub_zero, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (2 * π) * ‖_‖ ≤ 1 / (2 * π) * (M * (2 * π)) := by gcongr
    _ = M := by field_simp

/-- Integration by parts for Fourier coefficients of a periodic function. -/
lemma fourierCoeffOn_deriv {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hper : f 0 = f (2 * π)) (k : ℤ) :
    fourierCoeffOn two_pi_pos' f' k = (Complex.I * k) * fourierCoeffOn two_pi_pos' f k := by
  by_cases hk : k = 0
  · subst hk
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, Int.cast_zero, mul_zero, zero_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
      (hf'.intervalIntegrable _ _), ← hper, sub_self, smul_zero]
  · rw [fourierCoeffOn_of_hasDerivAt two_pi_pos' hk (fun x _ => hf x) (hf'.intervalIntegrable _ _),
      ← hper, sub_self, mul_zero, zero_sub]
    have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring_nf

/-- Pointwise convergence of an absolutely summable Fourier series on `[0, 2π)`. -/
lemma hasSum_fourierCoeffOn {f : ℝ → ℂ} (hc : Continuous f) (hper : f 0 = f (2 * π))
    (hs : Summable (fourierCoeffOn two_pi_pos' f)) {t : ℝ} (ht : t ∈ Ico 0 (2 * π)) :
    HasSum (fun k : ℤ => fourierCoeffOn two_pi_pos' f k * Complex.exp (k * t * Complex.I))
      (f t) := by
  haveI : Fact (0 < 2 * π) := ⟨two_pi_pos'⟩
  have hper' : f 0 = f (0 + 2 * π) := by rw [zero_add]; exact hper
  set F : C(AddCircle (2 * π), ℂ) :=
    ⟨AddCircle.liftIco (2 * π) 0 f, AddCircle.liftIco_continuous hper' hc.continuousOn⟩ with hF
  have hcoef : fourierCoeff F = fourierCoeffOn two_pi_pos' f := by
    funext k
    have key : ∀ (b : ℝ) (hb : 0 < b), b = 2 * π →
        fourierCoeffOn hb f k = fourierCoeffOn two_pi_pos' f k := by
      rintro b hb rfl; rfl
    rw [hF, ContinuousMap.coe_mk, fourierCoeff_liftIco_eq]
    exact key _ _ (zero_add _)
  have h := has_pointwise_sum_fourier_series_of_summable (f := F) (by rw [hcoef]; exact hs)
    (t : AddCircle (2 * π))
  rw [hcoef] at h
  have hFt : F (t : AddCircle (2 * π)) = f t := by
    rw [hF, ContinuousMap.coe_mk]
    exact AddCircle.liftIco_coe_apply (by rwa [zero_add])
  rw [hFt] at h
  simpa only [smul_eq_mul, fourier_coe_two_pi] using h

/-- Fourier coefficients of a real-valued function: `c_{-k} = conj c_k`. -/
lemma fourierCoeffOn_neg_of_real (g : ℝ → ℝ) (k : ℤ) :
    fourierCoeffOn two_pi_pos' (fun t => (g t : ℂ)) (-k) =
      conj (fourierCoeffOn two_pi_pos' (fun t => (g t : ℂ)) k) := by
  simp only [fourierCoeffOn_eq_integral, neg_neg, intervalIntegral.integral_of_le two_pi_pos'.le,
    Complex.real_smul, map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 2
  funext x
  rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal, fourier_neg, Complex.conj_conj]

/-- Absolute summability of the Fourier coefficients of the derivative of a periodic function with
three continuous derivatives (periodic up to order two). -/
lemma summable_norm_fourierCoeffOn_deriv {f f1 f2 f3 : ℝ → ℂ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (h3 : ∀ x, HasDerivAt f2 (f3 x) x) (hc3 : Continuous f3)
    (p0 : f 0 = f (2 * π)) (p1 : f1 0 = f1 (2 * π)) (p2 : f2 0 = f2 (2 * π)) :
    Summable (fun k => ‖fourierCoeffOn two_pi_pos' f1 k‖) := by
  have hc1 : Continuous f1 := continuous_iff_continuousAt.mpr fun x => (h2 x).continuousAt
  have hc2 : Continuous f2 := continuous_iff_continuousAt.mpr fun x => (h3 x).continuousAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π)) hc3.continuousOn
  have hb : ∀ k : ℤ, ‖fourierCoeffOn two_pi_pos' f1 k‖ ≤ M * (1 / (k : ℝ) ^ 2) := by
    intro k
    have e1 := fourierCoeffOn_deriv h1 hc1 p0 k
    have e2 := fourierCoeffOn_deriv h2 hc2 p1 k
    have e3 := fourierCoeffOn_deriv h3 hc3 p2 k
    by_cases hk : k = 0
    · subst hk
      rw [e1]; simp
    · have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      have hb3 := norm_fourierCoeffOn_le hM k
      rw [e3, e2] at hb3
      simp only [norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul] at hb3
      have hpos : 0 < |(k : ℝ)| := abs_pos.mpr hk'
      rw [one_div, ← div_eq_mul_inv, le_div_iff₀ (by positivity), ← sq_abs]
      have : ‖fourierCoeffOn two_pi_pos' f1 k‖ * |(k : ℝ)| ^ 2 =
          |(k : ℝ)| * (|(k : ℝ)| * ‖fourierCoeffOn two_pi_pos' f1 k‖) := by ring
      linarith
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ?_
  exact ((Real.summable_one_div_int_pow (p := 2)).mpr one_lt_two).mul_left M

/-- A smooth bump `ρ ≥ 0` supported in `(ε - δ, ε + δ) ⊂ (0, 2π)` with `∫₀^{2π} ρ = 1`. -/
lemma exists_cut_bump {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hεδ : ε + δ < 2 * π) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ t, δ ≤ |t - ε| → ρ t = 0) ∧
      (∫ t in (0 : ℝ)..(2 * π), ρ t) = 1 ∧ ρ =ᶠ[𝓝 0] 0 ∧ ρ =ᶠ[𝓝 (2 * π)] 0 := by
  let f : ContDiffBump ε := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨f.normed volume, f.contDiff_normed, fun t ht => ?_, ?_, ?_, ?_⟩
  · rw [← Function.notMem_support, f.support_normed_eq]
    simpa [Metric.mem_ball, Real.dist_eq] using ht
  · rw [intervalIntegral.integral_of_le two_pi_pos'.le,
      setIntegral_eq_integral_of_forall_compl_eq_zero, f.integral_normed (μ := volume)]
    intro t ht
    rw [← Function.notMem_support, f.support_normed_eq]
    intro hb
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hb
    exact ht ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · rw [← notMem_tsupport_iff_eventuallyEq, f.tsupport_normed_eq]
    simp only [Metric.mem_closedBall, Real.dist_eq, zero_sub, abs_neg, not_le]
    show f.rOut < |ε|
    rw [abs_of_pos (by linarith)]
    exact hδε
  · rw [← notMem_tsupport_iff_eventuallyEq, f.tsupport_normed_eq]
    simp only [Metric.mem_closedBall, Real.dist_eq, not_le]
    show f.rOut < |2 * π - ε|
    rw [abs_of_pos (by linarith)]
    linarith

/-- `e^{it}` is within `|t - ε|` of `e^{iε}`. -/
lemma norm_exp_sub_exp_le (t ε : ℝ) :
    ‖Complex.exp (t * Complex.I) - Complex.exp (ε * Complex.I)‖ ≤ |t - ε| := by
  have h : Complex.exp (t * Complex.I) - Complex.exp (ε * Complex.I) =
      Complex.exp (ε * Complex.I) * (Complex.exp (Complex.I * ((t - ε : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t - ε)
  rwa [Real.norm_eq_abs] at this

/-- **Fourier expansion of the cut argument.** For `0 < ε < 2π` and `r > 0` there are
coefficients `cₙ` with `∑ n |cₙ| < ∞` such that every unimodular `z` with `|z - e^{iε}| ≥ r`
satisfies `argCut ε z = ∑_{n ≥ 1} 2 Re(cₙ (zⁿ - 1))` and `1 = ∑_{n ≥ 1} 2 Re(i n cₙ zⁿ)`. -/
theorem exists_cutFourier {ε r : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) (hr : 0 < r) :
    ∃ c : ℕ → ℂ, Summable (fun n : ℕ => (n : ℝ) * ‖c n‖) ∧
      ∀ z : ℂ, ‖z‖ = 1 → r ≤ ‖z - Complex.exp (ε * Complex.I)‖ →
        HasSum (fun n : ℕ => 2 * (c n * (z ^ n - 1)).re) (argCut ε z) ∧
        HasSum (fun n : ℕ => 2 * (Complex.I * n * c n * z ^ n).re) 1 := by
  set δ := min (r / 2) (min ε (2 * π - ε) / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by have := lt_min hε0 (sub_pos.mpr hε); linarith)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ2 : δ ≤ min ε (2 * π - ε) / 2 := min_le_right _ _
  have hδε : δ < ε := by
    have := min_le_left ε (2 * π - ε); have := lt_min hε0 (sub_pos.mpr hε); linarith
  have hεδ : ε + δ < 2 * π := by
    have := min_le_right ε (2 * π - ε); have := lt_min hε0 (sub_pos.mpr hε); linarith
  obtain ⟨ρ, hρ, hρ0, hρint, hρe0, hρe2⟩ := exists_cut_bump hδ hδε hεδ
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hρ' : ContDiff ℝ (⊤ : ℕ∞) (deriv ρ) := (contDiff_infty_iff_deriv.mp hρ).2
  have hρd' : Differentiable ℝ (deriv ρ) := hρ'.differentiable (by simp)
  have hρc'' : Continuous (deriv (deriv ρ)) := (contDiff_infty_iff_deriv.mp hρ').2.continuous
  set h : ℝ → ℝ := fun t => t - 2 * π * ∫ s in (0 : ℝ)..t, ρ s with hh
  set F : ℝ → ℂ := fun t => (h t : ℂ) with hF
  set F1 : ℝ → ℂ := fun t => ((1 - 2 * π * ρ t : ℝ) : ℂ) with hF1
  set F2 : ℝ → ℂ := fun t => ((-(2 * π * deriv ρ t) : ℝ) : ℂ) with hF2
  set F3 : ℝ → ℂ := fun t => ((-(2 * π * deriv (deriv ρ) t) : ℝ) : ℂ) with hF3
  have d1 : ∀ x, HasDerivAt F (F1 x) x := fun x =>
    ((hasDerivAt_id x).sub (((hρ.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul
      (2 * π))).ofReal_comp
  have d2 : ∀ x, HasDerivAt F1 (F2 x) x := fun x =>
    ((((hρd x).hasDerivAt).const_mul (2 * π)).const_sub 1).ofReal_comp
  have d3 : ∀ x, HasDerivAt F2 (F3 x) x := fun x =>
    (((hρd' x).hasDerivAt).const_mul (2 * π)).neg.ofReal_comp
  have hc1 : Continuous F1 := continuous_iff_continuousAt.mpr fun x => (d2 x).continuousAt
  have hc3 : Continuous F3 := by rw [hF3]; fun_prop
  have hdρ0 : deriv ρ 0 = 0 := by rw [hρe0.deriv_eq]; simp
  have hdρ2 : deriv ρ (2 * π) = 0 := by rw [hρe2.deriv_eq]; simp
  have p0 : F 0 = F (2 * π) := by
    simp only [hF, hh, intervalIntegral.integral_same, hρint]; push_cast; ring
  have p1 : F1 0 = F1 (2 * π) := by
    simp only [hF1, hρe0.eq_of_nhds, hρe2.eq_of_nhds, Pi.zero_apply]
  have p2 : F2 0 = F2 (2 * π) := by simp only [hF2, hdρ0, hdρ2]
  have hs1 := summable_norm_fourierCoeffOn_deriv d1 d2 d3 hc3 p0 p1 p2
  set C : ℤ → ℂ := fourierCoeffOn two_pi_pos' F with hC
  have hC1 : ∀ k : ℤ, fourierCoeffOn two_pi_pos' F1 k = (Complex.I * k) * C k :=
    fourierCoeffOn_deriv d1 hc1 p0
  have hCneg : ∀ k : ℤ, C (-k) = conj (C k) := fun k => fourierCoeffOn_neg_of_real h k
  have hsC : Summable C := by
    refine Summable.of_norm ?_
    refine (hs1.add ((hasSum_ite_eq (0 : ℤ) ‖C 0‖).summable)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun k => ?_)
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg hk, add_zero, hC1, norm_mul, Complex.norm_mul, Complex.norm_I, one_mul,
        Complex.norm_intCast]
      have : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]; exact Int.one_le_abs hk
      nlinarith [norm_nonneg (C k)]
  refine ⟨fun n => C n, ?_, fun z hz hzr => ?_⟩
  · have := hs1.comp_injective Nat.cast_injective
    refine this.congr (fun n => ?_)
    simp only [Function.comp, hC1, norm_mul, Complex.norm_I, one_mul]
    rw [Int.cast_natCast, Complex.norm_natCast]
  -- the angle of `z`
  set t := argNeg z + 2 * π with ht
  have hz_exp : Complex.exp (t * Complex.I) = z := by
    rw [ht]; push_cast
    rw [add_mul, Complex.exp_add, exp_argNeg hz, Complex.exp_two_pi_mul_I, mul_one]
  have ht_mem : t ∈ Ico 0 (2 * π) := by
    rw [ht, argNeg]
    have hlo := Complex.neg_pi_lt_arg z
    have hhi := Complex.arg_le_pi z
    split_ifs with h0
    · constructor <;> linarith
    · constructor <;> linarith [not_lt.mp h0]
  have htε : δ ≤ |t - ε| := by
    by_contra hlt
    push_neg at hlt
    have := norm_exp_sub_exp_le t ε
    rw [hz_exp] at this
    linarith
  -- values of `h` and `h'` at `t`
  have hρt : ρ t = 0 := hρ0 t htε
  have hF1t : F1 t = 1 := by simp [hF1, hρt]
  have hFt : F t = (argCut ε z : ℂ) := by
    simp only [hF]
    congr 1
    rw [argCut, ← ht]
    split_ifs with hlt
    · have hle : t ≤ ε - δ := by
        rcases le_abs'.mp htε with h1 | h1 <;> linarith
      have : ∫ s in (0 : ℝ)..t, ρ s = 0 := by
        refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun s hs => ?_)
        rw [uIoc_of_le ht_mem.1] at hs
        exact hρ0 s (by rw [abs_sub_comm, abs_of_pos (by linarith [hs.2])]; linarith [hs.2])
      rw [hh]; simp only [this, mul_zero, sub_zero]
    · have hge : ε + δ ≤ t := by
        rcases le_abs'.mp htε with h1 | h1
        · exfalso; linarith
        · linarith
      have h2 : ∫ s in t..(2 * π), ρ s = 0 := by
        refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun s hs => ?_)
        rw [uIoc_of_le ht_mem.2.le] at hs
        exact hρ0 s (by rw [abs_of_pos (by linarith [hs.1])]; linarith [hs.1])
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hρ.continuous.intervalIntegrable (μ := volume) 0 t)
        (hρ.continuous.intervalIntegrable (μ := volume) t (2 * π))
      rw [hρint, h2, add_zero] at hsplit
      rw [hh]; simp only [hsplit, mul_one]
      rw [ht]; ring
  -- Fourier series
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun x => (d1 x).continuousAt
  have hpow : ∀ n : ℕ, Complex.exp (((n : ℤ) : ℂ) * t * Complex.I) = z ^ n := by
    intro n
    rw [← hz_exp, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hpowneg : ∀ n : ℕ, Complex.exp (((-(n : ℤ) : ℤ) : ℂ) * t * Complex.I) = conj (z ^ n) := by
    intro n
    rw [← hpow, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Int.cast_neg, Int.cast_natCast,
      Complex.conj_natCast]
    ring
  have hpow0 : ∀ n : ℕ, Complex.exp (((n : ℤ) : ℂ) * (0 : ℝ) * Complex.I) = 1 := by
    intro n; simp
  have hpowneg0 : ∀ n : ℕ, Complex.exp (((-(n : ℤ) : ℤ) : ℂ) * (0 : ℝ) * Complex.I) = 1 := by
    intro n; simp
  have hA := (hasSum_fourierCoeffOn hcF p0 hsC ht_mem).nat_add_neg
  have hB := (hasSum_fourierCoeffOn hcF p0 hsC ⟨le_rfl, two_pi_pos'⟩).nat_add_neg
  rw [← hC] at hA hB
  simp only [hpow, hpowneg, hCneg] at hA
  simp only [hpow0, hpowneg0, hCneg, mul_one] at hB
  have hF0 : F 0 = 0 := by simp [hF, hh]
  refine ⟨?_, ?_⟩
  · have hD := hA.sub hB
    rw [hFt, hF0] at hD
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, mul_one, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero] at hD
    rw [add_sub_add_right_eq_sub, sub_zero] at hD
    refine Complex.hasSum_ofReal.mp ?_
    convert hD using 1
    funext n
    rw [← map_mul, Complex.add_conj, Complex.add_conj]
    push_cast
    simp only [mul_sub, mul_one, Complex.sub_re]
    push_cast
    ring
  · have hsC1 : Summable (fourierCoeffOn two_pi_pos' F1) := hs1.of_norm
    have hE := (hasSum_fourierCoeffOn hc1 p1 hsC1 ht_mem).nat_add_neg
    simp only [hpow, hpowneg, hC1, hCneg, hF1t] at hE
    simp only [Int.cast_zero, mul_zero, zero_mul, add_zero] at hE
    refine Complex.hasSum_ofReal.mp ?_
    convert hE using 1
    · funext n
      have : Complex.I * (((-(n : ℤ) : ℤ) : ℂ)) * conj (C n) * conj (z ^ n) =
          conj (Complex.I * n * C n * z ^ n) := by
        simp only [map_mul, Complex.conj_I, Complex.conj_natCast, Int.cast_neg, Int.cast_natCast]
        ring
      rw [this, Int.cast_natCast, Complex.add_conj]

end PolyaNeumann

end
