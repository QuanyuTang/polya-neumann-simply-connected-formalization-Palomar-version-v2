module

public import RequestProject.Poincare
public import RequestProject.Herglotz

/-!
# Poincaré inequalities for Herglotz coefficients

* `poincare_C1`: on a bounded Lipschitz domain, a `C¹` function `f` on `ℂ` with bounded value
  and bounded derivative and `∫_Ω f = 0` satisfies `∫_Ω |f|² ≤ C ∫_Ω (|∂ₓf|² + |∂ᵧf|²)`.
* `poincare_C1_ball`: the same with the normalization `∫_B f = 0` on a ball `B ⊆ Ω`.
* For the Herglotz coefficients, `|∂ₓF_m|² + |∂ᵧF_m|² = (k²/2)(|F_{m+1}|² + |F_{m-1}|²)`
  (`sum_sq_fderiv_herglotzCoeff`), which gives `poincare_herglotzCoeff` and
  `poincare_herglotzCoeff_ball`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ}

/-- The classical gradient of a `C¹` function is its weak gradient. -/
lemma isWeakGradient_of_contDiff_one {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hu : MemLp f 2 (volume.restrict Ω))
    (hg : ∀ i, MemLp (fun w => fderiv ℝ f w (coordDir i)) 2 (volume.restrict Ω)) :
    IsWeakGradient Ω (hu.toLp f) (fun i => (hg i).toLp _) := by
  intro φ hφ i
  obtain ⟨hs, hφc, hsupp⟩ := hφ
  have e1' : (fun w => ((hu.toLp f : L2 Ω) : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i))
      =ᵐ[volume.restrict Ω] fun w => f w * fderiv ℝ φ w (coordDir i) := by
    filter_upwards [hu.coeFn_toLp] with w hw; rw [hw]
  have e2' : (fun w => (((hg i).toLp _ : L2 Ω) : ℂ → ℂ) w * φ w)
      =ᵐ[volume.restrict Ω] fun w => fderiv ℝ f w (coordDir i) * φ w := by
    filter_upwards [(hg i).coeFn_toLp] with w hw; rw [hw]
  rw [integral_congr_ae e1', integral_congr_ae e2']
  have hout : ∀ w ∉ Ω, w ∉ tsupport φ := fun w hw h => hw (hsupp h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) (hout w hw)]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
      simp [image_eq_zero_of_notMem_tsupport (hout w hw)])]
  have hfd : Continuous fun w => fderiv ℝ f w (coordDir i) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφd : Continuous fun w => fderiv ℝ φ w (coordDir i) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hfd.mul hs.continuous).integrable_of_hasCompactSupport (hφc.mul_left))
    ((hf.continuous.mul hφd).integrable_of_hasCompactSupport
      ((hφc.fderiv_apply (𝕜 := ℝ) _).mul_left))
    ((hf.continuous.mul hs.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    (fun x _ => (hf.differentiable (by simp)) x) (fun x _ => (hs.differentiable (by simp)) x)

lemma integral_norm_sq_toLp (u : L2 Ω) :
    ∫ w in Ω, ‖(u : ℂ → ℂ) w‖ ^ 2 = ‖u‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) u u)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner u u)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  exact h.symm

/-- The squared gradient `|∂ₓf|² + |∂ᵧf|²`. -/
def gradSq (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2

lemma memLp_of_continuous_bounded (hb : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    MemLp f 2 (volume.restrict Ω) := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact MemLp.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)

/-- **Poincaré–Wirtinger for `C¹` functions.** -/
theorem poincare_C1 (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → (∃ B, ∀ z, ‖f z‖ ≤ B) →
      (∃ B, ∀ z, ‖fderiv ℝ f z‖ ≤ B) → ∫ z in Ω, f z = 0 →
        ∫ z in Ω, ‖f z‖ ^ 2 ≤ C * ∫ z in Ω, gradSq f z := by
  obtain ⟨C, hC, hP⟩ := poincare_wirtinger hb hL
  refine ⟨C, hC, fun f hf ⟨B, hB⟩ ⟨B', hB'⟩ h0 => ?_⟩
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hu : MemLp f 2 (volume.restrict Ω) := memLp_of_continuous_bounded hb hf.continuous hB
  have hdc : ∀ v : ℂ, Continuous fun w => fderiv ℝ f w v := fun v =>
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdB : ∀ v : ℂ, ∀ w, ‖fderiv ℝ f w v‖ ≤ B' * ‖v‖ := fun v w =>
    ((fderiv ℝ f w).le_opNorm v).trans (by gcongr; exact hB' w)
  have hg : ∀ i, MemLp (fun w => fderiv ℝ f w (coordDir i)) 2 (volume.restrict Ω) := fun i =>
    memLp_of_continuous_bounded hb (hdc _) (hdB _)
  have hW := isWeakGradient_of_contDiff_one hf hu hg
  have hmean : ∫ w in Ω, (hu.toLp f : L2 Ω) w = 0 := by
    rw [integral_congr_ae hu.coeFn_toLp]; exact h0
  have key := hP _ _ hW hmean
  have hn : ∀ (g : ℂ → ℂ) (hg : MemLp g 2 (volume.restrict Ω)),
      ‖hg.toLp g‖ ^ 2 = ∫ z in Ω, ‖g z‖ ^ 2 := by
    intro g hg
    rw [← integral_norm_sq_toLp]
    exact integral_congr_ae (by filter_upwards [hg.coeFn_toLp] with z hz; rw [hz])
  rw [hn, Fin.sum_univ_two, hn, hn] at key
  have hi : ∀ v : ℂ, Integrable (fun z => ‖fderiv ℝ f z v‖ ^ 2) (volume.restrict Ω) := by
    intro v
    exact Integrable.of_bound ((hdc v).norm.pow 2).aestronglyMeasurable ((B' * ‖v‖) ^ 2)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdB v z) 2)
  unfold gradSq
  rw [integral_add (hi 1) (hi Complex.I)]
  simpa [coordDir] using key

/-- Cauchy–Schwarz: `(∫_s |g|)² ≤ |s| ∫_s |g|²` for bounded continuous `g`. -/
lemma sq_integral_norm_le {s : Set ℂ} (hs : volume s < ⊤) {g : ℂ → ℂ} (hgc : Continuous g)
    {B : ℝ} (hB : ∀ z, ‖g z‖ ≤ B) :
    (∫ z in s, ‖g z‖) ^ 2 ≤ (volume s).toReal * ∫ z in s, ‖g z‖ ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs.ne
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have i1 : Integrable (fun z => ‖g z‖) (volume.restrict s) :=
    Integrable.of_bound hgc.norm.aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [norm_norm]; exact hB z)
  have i2 : Integrable (fun z => ‖g z‖ ^ 2) (volume.restrict s) :=
    Integrable.of_bound (hgc.norm.pow 2).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB z) 2)
  set X := ∫ z in s, ‖g z‖ with hX
  set S := ∫ z in s, ‖g z‖ ^ 2 with hS
  set V := (volume s).toReal with hV
  have hX0 : 0 ≤ X := integral_nonneg fun _ => norm_nonneg _
  have hS0 : 0 ≤ S := integral_nonneg fun _ => by positivity
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hamgm : ∀ t : ℝ, 0 < t → X ≤ (t * S + V / t) / 2 := by
    intro t ht
    have hpt : ∀ z, ‖g z‖ ≤ (t * ‖g z‖ ^ 2 + 1 / t) / 2 := by
      intro z
      have e : (t * ‖g z‖ ^ 2 + 1 / t) / 2 - ‖g z‖ = (t * ‖g z‖ - 1) ^ 2 / (2 * t) := by
        field_simp; ring
      have : 0 ≤ (t * ‖g z‖ - 1) ^ 2 / (2 * t) := by positivity
      linarith
    calc X ≤ ∫ z in s, (t * ‖g z‖ ^ 2 + 1 / t) / 2 :=
          integral_mono i1 (((i2.const_mul t).add (integrable_const _)).div_const 2) hpt
      _ = (t * S + V / t) / 2 := by
          rw [integral_div, integral_add (i2.const_mul t) (integrable_const _),
            integral_const_mul, integral_const, smul_eq_mul, Measure.real_def,
            Measure.restrict_apply MeasurableSet.univ, univ_inter]
          ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases eq_or_lt_of_le hX0 with h | h
  · rw [← h]; nlinarith [mul_nonneg hV0 hS0]
  have ht : 0 < X / (S + ε / (V + 1)) := by positivity
  have h1 := hamgm _ ht
  have hSε : 0 < S + ε / (V + 1) := by positivity
  have h2 : X ≤ (X + V * (S + ε / (V + 1)) / X) / 2 := by
    refine h1.trans ?_
    have : X / (S + ε / (V + 1)) * S ≤ X := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hSε]
      nlinarith [mul_pos h (div_pos hε (by linarith : (0:ℝ) < V + 1))]
    have : V / (X / (S + ε / (V + 1))) = V * (S + ε / (V + 1)) / X := by
      field_simp
    linarith
  have h3 : X ^ 2 ≤ V * (S + ε / (V + 1)) := by
    have : X ≤ V * (S + ε / (V + 1)) / X := by linarith
    rw [le_div_iff₀ h] at this; nlinarith
  have h4 : V * (ε / (V + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

lemma integrable_norm_sq_of_bounded {s : Set ℂ} (hs : volume s < ⊤) {g : ℂ → ℂ}
    (hgc : Continuous g) {B : ℝ} (hB : ∀ z, ‖g z‖ ≤ B) :
    Integrable (fun z => ‖g z‖ ^ 2) (volume.restrict s) := by
  haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs.ne
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  exact Integrable.of_bound (hgc.norm.pow 2).aestronglyMeasurable (B ^ 2)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hB z) 2)

/-- **Poincaré inequality with a ball normalization.** If `B = ball z₁ r ⊆ Ω`, a `C¹` function
with bounded value and derivative and `∫_B f = 0` satisfies `∫_Ω |f|² ≤ C ∫_Ω |∇f|²`. -/
theorem poincare_C1_ball (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {z₁ : ℂ}
    {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → (∃ B, ∀ z, ‖f z‖ ≤ B) →
      (∃ B, ∀ z, ‖fderiv ℝ f z‖ ≤ B) → ∫ z in ball z₁ r, f z = 0 →
        ∫ z in Ω, ‖f z‖ ^ 2 ≤ C * ∫ z in Ω, gradSq f z := by
  obtain ⟨CP, hCP, hP⟩ := poincare_C1 hb hL
  have hΩfin : volume Ω < ⊤ := hb.measure_lt_top
  have hBfin : volume (ball z₁ r) < ⊤ := measure_ball_lt_top
  set VΩ := (volume Ω).toReal with hVΩ
  set VB := (volume (ball z₁ r)).toReal with hVB
  have hVB : 0 < VB := ENNReal.toReal_pos (measure_ball_pos volume z₁ hr).ne' hBfin.ne
  have hVΩ0 : 0 ≤ VΩ := ENNReal.toReal_nonneg
  refine ⟨(2 + 2 * VΩ / VB) * CP, by positivity, fun f hf ⟨B, hB⟩ hd h0 => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  haveI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩfin.ne
  haveI : IsFiniteMeasure (volume.restrict (ball z₁ r)) := isFiniteMeasure_restrict.mpr hBfin.ne
  set μ : ℂ := (∫ z in Ω, f z) / (VΩ : ℂ) with hμ
  set g : ℂ → ℂ := fun z => f z - μ with hg
  have hgc : Continuous g := hf.continuous.sub continuous_const
  have hgB : ∀ z, ‖g z‖ ≤ B + ‖μ‖ := fun z => (norm_sub_le _ _).trans (by linarith [hB z])
  have hfi : ∀ s : Set ℂ, volume s < ⊤ → Integrable f (volume.restrict s) := fun s hs => by
    haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs.ne
    exact Integrable.of_bound hf.continuous.aestronglyMeasurable B (Eventually.of_forall hB)
  have hgd : ∀ z, fderiv ℝ g z = fderiv ℝ f z := fun z => by
    simp only [hg]; exact fderiv_sub_const _
  have hgrad : ∀ z, gradSq g z = gradSq f z := fun z => by simp only [gradSq, hgd]
  have hint_const : ∀ s : Set ℂ, ∫ _ in s, μ = (volume s).toReal * μ := fun s => by
    rw [integral_const, Measure.real_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Complex.real_smul]
  have hg0 : ∫ z in Ω, g z = 0 := by
    rw [hg, integral_sub (hfi Ω hΩfin) (integrable_const _), hint_const]
    rcases eq_or_lt_of_le hVΩ0 with h | h
    · rw [← hVΩ, ← h, Complex.ofReal_zero, zero_mul, sub_zero]
      have : volume Ω = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp h.symm with h' | h'
        · exact h'
        · exact absurd h' hΩfin.ne
      rw [Measure.restrict_eq_zero.mpr this, integral_zero_measure]
    · have hne : (VΩ : ℂ) ≠ 0 := by exact_mod_cast h.ne'
      rw [← hVΩ, hμ, mul_div_cancel₀ _ hne, sub_self]
  have hS := hP g (hf.sub contDiff_const) ⟨_, hgB⟩ ⟨_, fun z => (hgd z).symm ▸ hd.choose_spec z⟩ hg0
  simp only [hgrad] at hS
  set S := ∫ z in Ω, ‖g z‖ ^ 2 with hSdef
  have hgB0 : ∫ z in ball z₁ r, g z = -(VB * μ) := by
    rw [hg, integral_sub (hfi _ hBfin) (integrable_const _), hint_const, h0, zero_sub]
  have hμB : ‖μ‖ * VB ≤ ∫ z in ball z₁ r, ‖g z‖ := by
    have := norm_integral_le_integral_norm (μ := volume.restrict (ball z₁ r)) g
    rw [hgB0, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hVB] at this
    linarith
  have hCS := sq_integral_norm_le hBfin hgc hgB
  have hmono : ∫ z in ball z₁ r, ‖g z‖ ^ 2 ≤ S :=
    setIntegral_mono_set (integrable_norm_sq_of_bounded hΩfin hgc hgB)
      (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall hball)
  have hμ2 : ‖μ‖ ^ 2 * VB ≤ S := by
    have h1 : (‖μ‖ * VB) ^ 2 ≤ VB * S := by
      calc (‖μ‖ * VB) ^ 2 ≤ (∫ z in ball z₁ r, ‖g z‖) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hμB 2
        _ ≤ VB * ∫ z in ball z₁ r, ‖g z‖ ^ 2 := hCS
        _ ≤ VB * S := by gcongr
    nlinarith
  have hfg : ∫ z in Ω, ‖f z‖ ^ 2 ≤ 2 * S + 2 * ‖μ‖ ^ 2 * VΩ := by
    have hpt : ∀ z, ‖f z‖ ^ 2 ≤ 2 * ‖g z‖ ^ 2 + 2 * ‖μ‖ ^ 2 := fun z => by
      have : f z = g z + μ := by simp [hg]
      rw [this]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (g z) μ) 2
      nlinarith [sq_nonneg (‖g z‖ - ‖μ‖)]
    calc ∫ z in Ω, ‖f z‖ ^ 2 ≤ ∫ z in Ω, (2 * ‖g z‖ ^ 2 + 2 * ‖μ‖ ^ 2) :=
          integral_mono (integrable_norm_sq_of_bounded hΩfin hf.continuous hB)
            (((integrable_norm_sq_of_bounded hΩfin hgc hgB).const_mul 2).add
              (integrable_const _)) hpt
      _ = 2 * S + 2 * ‖μ‖ ^ 2 * VΩ := by
          rw [integral_add ((integrable_norm_sq_of_bounded hΩfin hgc hgB).const_mul 2)
            (integrable_const _), integral_const_mul, integral_const, smul_eq_mul,
            Measure.real_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
          ring
  have hS0 : 0 ≤ S := integral_nonneg fun _ => by positivity
  have hμ2' : ‖μ‖ ^ 2 ≤ S / VB := by rw [le_div_iff₀ hVB]; exact hμ2
  calc ∫ z in Ω, ‖f z‖ ^ 2 ≤ 2 * S + 2 * ‖μ‖ ^ 2 * VΩ := hfg
    _ ≤ 2 * S + 2 * (S / VB) * VΩ := by gcongr
    _ = (2 + 2 * VΩ / VB) * S := by ring
    _ ≤ (2 + 2 * VΩ / VB) * (CP * ∫ z in Ω, gradSq f z) := by gcongr
    _ = _ := by ring

section Herglotz

variable {a : ℝ → ℂ}

lemma contDiff_herglotzCoeff (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ) :
    ContDiff ℝ 1 (herglotzCoeff k a m) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨differentiable_herglotzCoeff ha k m, ?_⟩
  have hfd : fderiv ℝ (herglotzCoeff k a m) = fun z =>
      (-(Complex.I * k / 2) * herglotzCoeff k a (m + 1) z) • ContinuousLinearMap.id ℝ ℂ +
      (-(Complex.I * k / 2) * herglotzCoeff k a (m - 1) z) •
        Complex.conjCLE.toContinuousLinearMap := by
    funext z
    ext1 w
    rw [fderiv_herglotzCoeff_apply ha]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply]
    ring
  rw [hfd]
  have h1 := continuous_herglotzCoeff ha k (m + 1)
  have h2 := continuous_herglotzCoeff ha k (m - 1)
  fun_prop

lemma gradSq_herglotzCoeff (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ)
    (z : ℂ) : gradSq (herglotzCoeff k a m) z =
      k ^ 2 / 2 * (‖herglotzCoeff k a (m + 1) z‖ ^ 2 + ‖herglotzCoeff k a (m - 1) z‖ ^ 2) := by
  unfold gradSq
  rw [fderiv_herglotzCoeff_apply ha, fderiv_herglotzCoeff_apply ha]
  set A := herglotzCoeff k a (m + 1) z
  set B := herglotzCoeff k a (m - 1) z
  have hc : ‖-(Complex.I * k / 2)‖ = |k| / 2 := by
    rw [norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]; norm_num
  have e2 : Complex.I * A + conj Complex.I * B = Complex.I * (A - B) := by
    rw [Complex.conj_I]; ring
  simp only [one_mul, map_one, norm_mul, hc, e2, Complex.norm_I]
  have hpar : ‖A + B‖ ^ 2 + ‖A - B‖ ^ 2 = 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    have := parallelogram_law_with_norm ℝ A B
    nlinarith
  have hk : |k| ^ 2 = k ^ 2 := sq_abs k
  nlinarith

/-- **Poincaré for Herglotz coefficients** (zero mean over `Ω`). -/
theorem poincare_herglotzCoeff (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℂ), IntervalIntegrable a volume 0 (2 * π) → ∀ (k : ℝ) (m : ℤ),
      ∫ z in Ω, herglotzCoeff k a m z = 0 →
        ∫ z in Ω, ‖herglotzCoeff k a m z‖ ^ 2 ≤
          C * (k ^ 2 / 2 * ∫ z in Ω, (‖herglotzCoeff k a (m + 1) z‖ ^ 2 +
            ‖herglotzCoeff k a (m - 1) z‖ ^ 2)) := by
  obtain ⟨C, hC, hP⟩ := poincare_C1 hb hL
  refine ⟨C, hC, fun a ha k m h0 => ?_⟩
  have := hP _ (contDiff_herglotzCoeff ha k m) ⟨_, norm_herglotzCoeff_le k m⟩
    ⟨_, norm_fderiv_herglotzCoeff_le ha k m⟩ h0
  simp only [gradSq_herglotzCoeff ha] at this
  rwa [integral_const_mul] at this

/-- **Poincaré for Herglotz coefficients** (zero mean over a ball `B ⊆ Ω`). -/
theorem poincare_herglotzCoeff_ball (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {z₁ : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℂ), IntervalIntegrable a volume 0 (2 * π) → ∀ (k : ℝ) (m : ℤ),
      ∫ z in ball z₁ r, herglotzCoeff k a m z = 0 →
        ∫ z in Ω, ‖herglotzCoeff k a m z‖ ^ 2 ≤
          C * (k ^ 2 / 2 * ∫ z in Ω, (‖herglotzCoeff k a (m + 1) z‖ ^ 2 +
            ‖herglotzCoeff k a (m - 1) z‖ ^ 2)) := by
  obtain ⟨C, hC, hP⟩ := poincare_C1_ball hb hL hr hball
  refine ⟨C, hC, fun a ha k m h0 => ?_⟩
  have := hP _ (contDiff_herglotzCoeff ha k m) ⟨_, norm_herglotzCoeff_le k m⟩
    ⟨_, norm_fderiv_herglotzCoeff_le ha k m⟩ h0
  simp only [gradSq_herglotzCoeff ha] at this
  rwa [integral_const_mul] at this

end Herglotz

end PolyaNeumann
