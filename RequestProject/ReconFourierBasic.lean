module

public import Mathlib.Analysis.Fourier.LpSpace
public import RequestProject.ReconBasic

/-!
# Fourier transform on `ℂ = ℝ²`: basic identities

With `⟨z, ξ⟩ = Re(conj z · ξ)`, Mathlib's Fourier transform is
`𝓕 f ξ = ∫ ePlane ξ x * f x` (`fourier_eq_ePlane`) and `𝓕⁻ f ξ = ∫ conj (ePlane ξ x) * f x`.
This file proves:

* the multiplication formula `∫ 𝓕 g · h = ∫ g · 𝓕 h` for integrable `g`, `h`;
* the pairing of `L²` Fourier transforms with test functions,
  `∫ (𝓕⁻ A) φ = ∫ A · 𝓕⁻ φ` and `∫ (𝓕 A) φ = ∫ A · 𝓕 φ`;
* the compatibility of the `L²` and the integral Fourier transforms on `L¹ ∩ L²`
  (`fourier_toLp_ae_eq`), hence `𝓕 G ∈ L²` for `G ∈ L¹ ∩ L²`;
* the Fourier transforms of derivatives of test functions.
-/

@[expose] public section

open MeasureTheory Set Filter FourierTransform
open scoped ComplexConjugate Real FourierTransform

noncomputable section

namespace PolyaNeumann

lemma real_inner_eq_re (z w : ℂ) : inner ℝ z w = (conj z * w).re := by
  rw [Complex.inner, mul_comm]

lemma ePlane_eq_fourierChar (ξ x : ℂ) : ePlane ξ x = ((𝐞 (-inner ℝ x ξ) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, ePlane, real_inner_eq_re]
  congr 1
  push_cast
  ring

lemma fourier_eq_ePlane (f : ℂ → ℂ) (ξ : ℂ) : 𝓕 f ξ = ∫ x, ePlane ξ x * f x := by
  rw [Real.fourier_eq]
  congr 1
  funext x
  rw [ePlane_eq_fourierChar, Circle.smul_def, smul_eq_mul]

lemma conj_ePlane (ξ x : ℂ) : conj (ePlane ξ x) = ePlane (-ξ) x := by
  unfold ePlane
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I, mul_neg,
    Complex.neg_re, Complex.ofReal_neg]
  ring

lemma fourierInv_eq_ePlane (f : ℂ → ℂ) (ξ : ℂ) : 𝓕⁻ f ξ = ∫ x, conj (ePlane ξ x) * f x := by
  rw [Real.fourierInv_eq]
  congr 1
  funext x
  rw [Circle.smul_def, smul_eq_mul, conj_ePlane, ePlane_eq_fourierChar]
  congr 3
  rw [inner_neg_right, neg_neg]

lemma ePlane_comm (ξ x : ℂ) : ePlane ξ x = ePlane x ξ := by
  unfold ePlane
  rw [← Complex.conj_re (conj x * ξ)]
  simp [mul_comm]

lemma norm_ePlane (ξ x : ℂ) : ‖ePlane ξ x‖ = 1 := by
  rw [ePlane_eq_fourierChar]; exact Circle.norm_coe _

lemma continuous_ePlane_prod : Continuous fun p : ℂ × ℂ => ePlane p.2 p.1 := by
  unfold ePlane; fun_prop

lemma norm_ePlane_sub_le (ξ η x : ℂ) : ‖ePlane ξ x - ePlane η x‖ ≤ 2 * π * ‖x‖ * ‖ξ - η‖ := by
  have h : ePlane ξ x - ePlane η x = ePlane η x *
      (Complex.exp (Complex.I * ((-(2 * π * (conj x * (ξ - η)).re)) : ℝ)) - 1) := by
    unfold ePlane
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    simp only [mul_sub, Complex.sub_re]
    push_cast
    ring
  rw [h, norm_mul, norm_ePlane, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have h1 : |(conj x * (ξ - η)).re| ≤ ‖x‖ * ‖ξ - η‖ :=
    (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π)
  linarith

lemma norm_fourier_le (f : ℂ → ℂ) (ξ : ℂ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [fourier_eq_ePlane]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x; rw [norm_mul, norm_ePlane, one_mul]

/-- The Fourier transform of an integrable `f` with `∫ ‖x‖ ‖f x‖ < ∞` is Lipschitz. -/
lemma norm_fourier_sub_le {f : ℂ → ℂ} (hf : Integrable f)
    (hf' : Integrable fun x => ‖x‖ * ‖f x‖) (ξ η : ℂ) :
    ‖𝓕 f ξ - 𝓕 f η‖ ≤ 2 * π * (∫ x, ‖x‖ * ‖f x‖) * ‖ξ - η‖ := by
  have hi : ∀ ζ : ℂ, Integrable fun x => ePlane ζ x * f x := fun ζ =>
    hf.bdd_mul (c := 1) ((continuous_ePlane_prod.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (Eventually.of_forall fun x => (norm_ePlane ζ x).le)
  rw [fourier_eq_ePlane, fourier_eq_ePlane, ← integral_sub (hi ξ) (hi η)]
  refine (norm_integral_le_integral_norm _).trans ?_
  have e : 2 * π * (∫ x, ‖x‖ * ‖f x‖) * ‖ξ - η‖ =
      ∫ x, 2 * π * (‖x‖ * ‖f x‖) * ‖ξ - η‖ := by
    rw [integral_mul_const, integral_const_mul]
  rw [e]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
    ((hf'.const_mul _).mul_const _) (Eventually.of_forall fun x => ?_)
  simp only
  rw [← sub_mul, norm_mul]
  calc ‖ePlane ξ x - ePlane η x‖ * ‖f x‖ ≤ (2 * π * ‖x‖ * ‖ξ - η‖) * ‖f x‖ := by
        gcongr; exact norm_ePlane_sub_le ξ η x
    _ = 2 * π * (‖x‖ * ‖f x‖) * ‖ξ - η‖ := by ring

/-- The multiplication formula `∫ 𝓕 g · h = ∫ g · 𝓕 h`. -/
lemma integral_fourier_mul {g h : ℂ → ℂ} (hg : Integrable g) (hh : Integrable h) :
    ∫ ξ, 𝓕 g ξ * h ξ = ∫ x, g x * 𝓕 h x := by
  have hint : Integrable (fun p : ℂ × ℂ => ePlane p.2 p.1 * g p.1 * h p.2)
      ((volume : Measure ℂ).prod volume) := by
    refine (hg.norm.mul_prod hh.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((continuous_ePlane_prod.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_fst).mul
        hh.aestronglyMeasurable.comp_snd)
    · rw [norm_mul, norm_mul, norm_ePlane, one_mul]
  have e1 : ∀ ξ, (∫ x, ePlane ξ x * g x) * h ξ = ∫ x, ePlane ξ x * g x * h ξ := fun ξ =>
    (integral_mul_const _ _).symm
  have e2 : ∀ x, g x * (∫ ξ, ePlane x ξ * h ξ) = ∫ ξ, ePlane ξ x * g x * h ξ := fun x => by
    rw [← integral_const_mul]; congr 1; funext ξ; rw [ePlane_comm]; ring
  have L : ∫ ξ, 𝓕 g ξ * h ξ = ∫ ξ, ∫ x, ePlane ξ x * g x * h ξ := integral_congr_ae
      (Eventually.of_forall fun ξ => by simp only; rw [fourier_eq_ePlane, e1])
  have R : ∫ x, g x * 𝓕 h x = ∫ x, ∫ ξ, ePlane ξ x * g x * h ξ := integral_congr_ae
      (Eventually.of_forall fun x => by simp only; rw [fourier_eq_ePlane, e2])
  rw [L, R]
  exact (integral_integral_swap (f := fun x ξ => ePlane ξ x * g x * h ξ) hint).symm

/-- The multiplication formula for the inverse transform. -/
lemma integral_fourierInv_mul {g h : ℂ → ℂ} (hg : Integrable g) (hh : Integrable h) :
    ∫ ξ, 𝓕⁻ g ξ * h ξ = ∫ x, g x * 𝓕⁻ h x := by
  have hint : Integrable (fun p : ℂ × ℂ => conj (ePlane p.2 p.1) * g p.1 * h p.2)
      ((volume : Measure ℂ).prod volume) := by
    refine (hg.norm.mul_prod hh.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((Complex.continuous_conj.comp continuous_ePlane_prod).aestronglyMeasurable.mul
        hg.aestronglyMeasurable.comp_fst).mul hh.aestronglyMeasurable.comp_snd)
    · rw [norm_mul, norm_mul, Complex.norm_conj, norm_ePlane, one_mul]
  have e1 : ∀ ξ, (∫ x, conj (ePlane ξ x) * g x) * h ξ =
      ∫ x, conj (ePlane ξ x) * g x * h ξ := fun ξ => (integral_mul_const _ _).symm
  have e2 : ∀ x, g x * (∫ ξ, conj (ePlane x ξ) * h ξ) =
      ∫ ξ, conj (ePlane ξ x) * g x * h ξ := fun x => by
    rw [← integral_const_mul]; congr 1; funext ξ; rw [ePlane_comm]; ring
  have L : ∫ ξ, 𝓕⁻ g ξ * h ξ = ∫ ξ, ∫ x, conj (ePlane ξ x) * g x * h ξ :=
    integral_congr_ae
      (Eventually.of_forall fun ξ => by simp only; rw [fourierInv_eq_ePlane, e1])
  have R : ∫ x, g x * 𝓕⁻ h x = ∫ x, ∫ ξ, conj (ePlane ξ x) * g x * h ξ :=
    integral_congr_ae
      (Eventually.of_forall fun x => by simp only; rw [fourierInv_eq_ePlane, e2])
  rw [L, R]
  exact (integral_integral_swap (f := fun x ξ => conj (ePlane ξ x) * g x * h ξ) hint).symm

/-- A test function as a Schwartz map. -/
def TestFunction.schwartz {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) : SchwartzMap ℂ ℂ :=
  hφ.2.1.toSchwartzMap hφ.1

@[simp] lemma TestFunction.schwartz_apply {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ)
    (x : ℂ) : hφ.schwartz x = φ x := rfl

lemma inner_toLp_eq_integral {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (B : Lp ℂ 2 (volume : Measure ℂ)) :
    inner ℂ ((hφ.conj).schwartz.toLp 2 volume) B = ∫ x, φ x * B x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (hφ.conj).schwartz 2 volume] with x hx
  rw [hx, TestFunction.schwartz_apply, RCLike.inner_apply, Complex.conj_conj]
  exact mul_comm _ _

/-- Pairing of an inverse `L²` Fourier transform with a test function. -/
lemma integral_fourierInv_Lp_mul (A : Lp ℂ 2 (volume : Measure ℂ)) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) :
    ∫ x, (𝓕⁻ A : Lp ℂ 2 (volume : Measure ℂ)) x * φ x = ∫ ξ, A ξ * 𝓕⁻ φ ξ := by
  set s := (hφ.conj).schwartz
  have h1 := inner_toLp_eq_integral hφ (𝓕⁻ A)
  have h2 : inner ℂ (s.toLp 2 volume) (𝓕⁻ A) = inner ℂ ((𝓕 s).toLp 2 volume) A := by
    rw [← Lp.inner_fourier_eq (s.toLp 2 volume) (𝓕⁻ A), fourier_fourierInv_eq,
      SchwartzMap.toLp_fourier_eq]
  rw [show (∫ x, _ * φ x) = ∫ x, φ x * _ from
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _), ← h1, h2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 s) 2 volume] with ξ hξ
  rw [hξ, RCLike.inner_apply, SchwartzMap.fourier_coe, fourier_eq_ePlane, fourierInv_eq_ePlane,
    ← integral_conj]
  congr 1
  congr 1
  funext x
  simp [s, map_mul]

/-- Pairing of an `L²` Fourier transform with a test function. -/
lemma integral_fourier_Lp_mul (A : Lp ℂ 2 (volume : Measure ℂ)) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) :
    ∫ x, (𝓕 A : Lp ℂ 2 (volume : Measure ℂ)) x * φ x = ∫ ξ, A ξ * 𝓕 φ ξ := by
  set s := (hφ.conj).schwartz
  have h1 := inner_toLp_eq_integral hφ (𝓕 A)
  have h2 : inner ℂ (s.toLp 2 volume) (𝓕 A) = inner ℂ ((𝓕⁻ s).toLp 2 volume) A := by
    conv_lhs => rw [← fourier_fourierInv_eq (E := Lp ℂ 2 (volume : Measure ℂ))
      (F := Lp ℂ 2 (volume : Measure ℂ)) (s.toLp 2 volume)]
    rw [Lp.inner_fourier_eq, SchwartzMap.toLp_fourierInv_eq]
  rw [show (∫ x, _ * φ x) = ∫ x, φ x * _ from
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _), ← h1, h2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕⁻ s) 2 volume] with ξ hξ
  rw [hξ, RCLike.inner_apply, SchwartzMap.fourierInv_coe, fourier_eq_ePlane,
    fourierInv_eq_ePlane, ← integral_conj]
  congr 1
  congr 1
  funext x
  simp [s, map_mul]

/-! ### Compactly supported `L²` functions -/

lemma integrable_of_memLp_two_hasCompactSupport {G : ℂ → ℂ} (hG : MemLp G 2 volume)
    (hc : HasCompactSupport G) : Integrable G := by
  haveI : IsFiniteMeasure (volume.restrict (tsupport G)) :=
    isFiniteMeasure_restrict.mpr hc.isCompact.measure_lt_top.ne
  have : IntegrableOn G (tsupport G) := (hG.restrict _).integrable (by norm_num)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport G)).mp this

lemma integrable_norm_mul_of_hasCompactSupport {G : ℂ → ℂ} (hG : Integrable G)
    (hc : HasCompactSupport G) : Integrable fun x => ‖x‖ * ‖G x‖ := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine (hG.norm.const_mul R).mono' (continuous_norm.aestronglyMeasurable.mul
    hG.aestronglyMeasurable.norm) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_norm, norm_norm]
  by_cases hx : x ∈ tsupport G
  · have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero, mul_zero]

lemma continuous_fourier_of_moment {f : ℂ → ℂ} (hf : Integrable f)
    (hf' : Integrable fun x => ‖x‖ * ‖f x‖) : Continuous (𝓕 f) := by
  refine LipschitzWith.continuous (K := ⟨2 * π * ∫ x, ‖x‖ * ‖f x‖, by
    have : 0 ≤ ∫ x, ‖x‖ * ‖f x‖ := integral_nonneg fun x => by positivity
    positivity⟩) (LipschitzWith.of_dist_le_mul fun ξ η => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_fourier_sub_le hf hf' ξ η

/-- The `L²` and the integral Fourier transforms agree on `L¹ ∩ L²` (with a first moment). -/
lemma fourier_toLp_ae_eq {G : ℂ → ℂ} (hG2 : MemLp G 2 volume) (hG1 : Integrable G)
    (hG' : Integrable fun x => ‖x‖ * ‖G x‖) :
    ((𝓕 (hG2.toLp G) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume] 𝓕 G := by
  set A := hG2.toLp G
  have hc := continuous_fourier_of_moment hG1 hG'
  have hb : ∀ ξ, ‖𝓕 G ξ‖ ≤ ∫ x, ‖G x‖ := norm_fourier_le G
  have hloc : LocallyIntegrable (fun ξ => (𝓕 A : Lp ℂ 2 (volume : Measure ℂ)) ξ - 𝓕 G ξ)
      volume :=
    (Lp.memLp (𝓕 A)).locallyIntegrable (by norm_num) |>.sub hc.locallyIntegrable
  have h0 := ae_eq_zero_of_integral_mul_test isOpen_univ hloc (fun φ hφ => by
    have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
    have hi1 : Integrable fun x => (𝓕 A : Lp ℂ 2 (volume : Measure ℂ)) x * φ x :=
      integrable_mul_test (Lp.memLp _) hφ
    have hi2 : Integrable fun x => 𝓕 G x * φ x :=
      hφi.bdd_mul (c := ∫ x, ‖G x‖) hc.aestronglyMeasurable (Eventually.of_forall hb)
    simp_rw [sub_mul]
    rw [integral_sub hi1 hi2, integral_fourier_Lp_mul A hφ, integral_fourier_mul hG1 hφi]
    rw [sub_eq_zero]
    refine integral_congr_ae ?_
    filter_upwards [hG2.coeFn_toLp] with x hx
    rw [hx])
  rw [Measure.restrict_univ] at h0
  filter_upwards [h0] with ξ hξ
  exact sub_eq_zero.mp hξ

lemma memLp_fourier {G : ℂ → ℂ} (hG2 : MemLp G 2 volume) (hG1 : Integrable G)
    (hG' : Integrable fun x => ‖x‖ * ‖G x‖) : MemLp (𝓕 G) 2 volume :=
  (Lp.memLp _).ae_eq (fourier_toLp_ae_eq hG2 hG1 hG')

/-! ### Derivatives of plane waves and of test functions -/

lemma hasFDerivAt_ePlane (ξ z : ℂ) :
    HasFDerivAt (ePlane ξ) ((ePlane ξ z * (-(2 * π * Complex.I))) •
      (Complex.ofRealCLM.comp (Complex.reCLM.comp
        ((((ContinuousLinearMap.mul ℂ ℂ).flip ξ).restrictScalars ℝ).comp
          Complex.conjCLE.toContinuousLinearMap)))) z := by
  set L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp (Complex.reCLM.comp
    ((((ContinuousLinearMap.mul ℂ ℂ).flip ξ).restrictScalars ℝ).comp
      Complex.conjCLE.toContinuousLinearMap))
  have hL : ∀ w, L w = ((conj w * ξ).re : ℂ) := fun w => rfl
  have h1 : HasFDerivAt (fun z : ℂ => -(2 * π * Complex.I) * ((conj z * ξ).re : ℂ))
      ((-(2 * π * Complex.I)) • L) z := by
    have := (L.hasFDerivAt (x := z)).const_mul (-(2 * π * Complex.I))
    simpa only [hL] using this
  have := h1.cexp
  rw [smul_smul] at this
  exact this

lemma fderiv_ePlane_apply' (ξ z v : ℂ) :
    fderiv ℝ (ePlane ξ) z v = -(2 * π * Complex.I) * (conj v * ξ).re * ePlane ξ z := by
  rw [(hasFDerivAt_ePlane ξ z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  simp [mul_comm, mul_left_comm, mul_assoc]

lemma dirD_ePlane (ξ v : ℂ) :
    dirD (ePlane ξ) v = fun z => -(2 * π * Complex.I) * (conj v * ξ).re * ePlane ξ z :=
  funext fun z => fderiv_ePlane_apply' ξ z v

lemma lap_ePlane (ξ z : ℂ) : lap (ePlane ξ) z = -(4 * π ^ 2 * ‖ξ‖ ^ 2) * ePlane ξ z := by
  have h : ∀ v : ℂ, dirD (dirD (ePlane ξ) v) v z =
      (-(2 * π * Complex.I) * (conj v * ξ).re) ^ 2 * ePlane ξ z := by
    intro v
    rw [dirD_ePlane]
    unfold dirD
    rw [fderiv_const_mul ((hasFDerivAt_ePlane ξ z).differentiableAt), ContinuousLinearMap.smul_apply,
      fderiv_ePlane_apply', smul_eq_mul]
    ring
  rw [lap, h, h]
  have hn : (‖ξ‖ : ℂ) ^ 2 = (ξ.re : ℂ) ^ 2 + (ξ.im : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]; push_cast; ring
  simp only [map_one, one_mul, Complex.conj_I]
  rw [hn]
  simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im, Complex.neg_im]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `𝓕⁻ (∂ᵥ φ)(ξ) = -2πi ⟨v, ξ⟩ 𝓕⁻ φ(ξ)` for test functions. -/
lemma fourierInv_dirD {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (v ξ : ℂ) :
    𝓕⁻ (dirD φ v) ξ = -(2 * π * Complex.I) * (conj v * ξ).re * 𝓕⁻ φ ξ := by
  have hlip : LipschitzWith ⟨2 * π * ‖ξ‖, by positivity⟩ (ePlane (-ξ)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, ePlane_comm (-ξ) x, ePlane_comm (-ξ) y]
    change _ ≤ (2 * π * ‖ξ‖) * _
    have := norm_ePlane_sub_le x y (-ξ)
    rw [norm_neg] at this
    linarith
  have hibp := integral_mul_fderiv_of_lipschitz hlip (hφ.1.of_le (by exact_mod_cast le_top))
    hφ.2.1 v
  rw [fourierInv_eq_ePlane, fourierInv_eq_ePlane]
  simp_rw [conj_ePlane]
  unfold dirD
  rw [hibp, ← integral_const_mul, ← integral_neg]
  congr 1
  funext x
  rw [fderiv_ePlane_apply']
  simp only [mul_neg, Complex.neg_re, Complex.ofReal_neg]
  ring

lemma fourierInv_lap {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (ξ : ℂ) :
    𝓕⁻ (lap φ) ξ = -(4 * π ^ 2 * ‖ξ‖ ^ 2) * 𝓕⁻ φ ξ := by
  have hi : ∀ v : ℂ, Integrable (dirD (dirD φ v) v) := fun v =>
    ((hφ.dirD v).dirD v).1.continuous.integrable_of_hasCompactSupport ((hφ.dirD v).dirD v).2.1
  have hsplit : 𝓕⁻ (lap φ) ξ = 𝓕⁻ (dirD (dirD φ 1) 1) ξ +
      𝓕⁻ (dirD (dirD φ Complex.I) Complex.I) ξ := by
    rw [fourierInv_eq_ePlane, fourierInv_eq_ePlane, fourierInv_eq_ePlane, ← integral_add]
    · congr 1; funext x; rw [lap]; ring
    · exact (hi 1).bdd_mul (c := 1) ((Complex.continuous_conj.comp (continuous_ePlane_prod.comp
        (continuous_id.prodMk continuous_const))).aestronglyMeasurable)
        (Eventually.of_forall fun x => by rw [Complex.norm_conj, norm_ePlane])
    · exact (hi _).bdd_mul (c := 1) ((Complex.continuous_conj.comp (continuous_ePlane_prod.comp
        (continuous_id.prodMk continuous_const))).aestronglyMeasurable)
        (Eventually.of_forall fun x => by rw [Complex.norm_conj, norm_ePlane])
  rw [hsplit, fourierInv_dirD (hφ.dirD 1), fourierInv_dirD hφ, fourierInv_dirD (hφ.dirD _),
    fourierInv_dirD hφ]
  have hn : (‖ξ‖ : ℂ) ^ 2 = (ξ.re : ℂ) ^ 2 + (ξ.im : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]; push_cast; ring
  rw [hn]
  simp only [map_one, one_mul, Complex.conj_I, Complex.mul_re, Complex.neg_re, Complex.I_re,
    Complex.I_im, Complex.neg_im]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Fourier inversion `∫ 𝓕 g · 𝓕⁻ φ = ∫ g φ` for integrable `g` and test functions `φ`. -/
lemma integral_fourier_mul_fourierInv {g : ℂ → ℂ} (hg : Integrable g) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) : ∫ ξ, 𝓕 g ξ * 𝓕⁻ φ ξ = ∫ x, g x * φ x := by
  have hs : (hφ.schwartz : ℂ → ℂ) = φ := rfl
  have hinv : 𝓕⁻ φ = ((𝓕⁻ hφ.schwartz : SchwartzMap ℂ ℂ) : ℂ → ℂ) := by
    rw [SchwartzMap.fourierInv_coe, hs]
  rw [integral_fourier_mul hg (by rw [hinv]; exact (𝓕⁻ hφ.schwartz).integrable)]
  congr 1
  funext x
  rw [hinv, ← SchwartzMap.fourier_coe, fourier_fourierInv_eq, hs]

end PolyaNeumann
