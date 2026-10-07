module

public import RequestProject.SmallTransport

/-!
# A double integration by parts for periodic kernels (proof of Lemma 8.4, kernel part)

Let `r(θ, s)` be a kernel on `[0, L]²` (`L = 2π`) that is periodic in both variables
(`r(θ, L) = r(θ, 0)`, `r(L, s) = r(0, s)`) and absolutely continuous in `s`,
`r(θ, s) = r(θ, 0) + ∫₀^s ρ(θ, t) dt`, where `ρ` is Lipschitz in `θ` with constant `M`.
For a bounded measurable `g` with primitive `G(θ) = ∫₀^θ g` and `G(L) = 0`, and any constant
`c`, we show (`norm_kernel_form_le`)

  `|∫₀^L conj(g(θ)) ∫₀^L r(θ, s) g(s) ds dθ| ≤ M (∫₀^L |G - c|)²`.

The proof integrates by parts in `s` (a Fubini argument on the triangle `t ≤ s`), which gives
`∫₀^L r(θ, s) g(s) ds = -∫₀^L ρ(θ, t) (G(t) - c) dt =: Φ(θ)`; `Φ` is Lipschitz with constant
`M ∫|G - c|` and periodic, and a second integration by parts in `θ` gives the bound.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

/-- Fubini on a triangle: `∫₀^L (∫₀^s f) g(s) ds = ∫₀^L f(t) ∫_t^L g`. -/
lemma integral_primitive_mul_eq {L : ℝ} (hL : 0 ≤ L) {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 L)))
    (hg : AEStronglyMeasurable g (volume.restrict (Icc 0 L))) {Bf Bg : ℝ}
    (hfB : ∀ t ∈ Icc 0 L, ‖f t‖ ≤ Bf) (hgB : ∀ t ∈ Icc 0 L, ‖g t‖ ≤ Bg) :
    ∫ s in (0 : ℝ)..L, (∫ t in (0 : ℝ)..s, f t) * g s =
      ∫ t in (0 : ℝ)..L, f t * ∫ s in t..L, g s := by
  set μ : Measure ℝ := volume.restrict (Icc 0 L) with hμ
  set Φ : ℝ → ℝ → ℂ := fun s t => if t ≤ s then f t * g s else 0 with hΦdef
  have hBf : 0 ≤ Bf := (norm_nonneg _).trans (hfB 0 ⟨le_rfl, hL⟩)
  have hBg : 0 ≤ Bg := (norm_nonneg _).trans (hgB 0 ⟨le_rfl, hL⟩)
  have hΦ : Integrable (Function.uncurry Φ) (μ.prod μ) := by
    have hm0 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 * g p.1) (μ.prod μ) :=
      hf.comp_snd.mul hg.comp_fst
    have heq : Function.uncurry Φ = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
        (fun p : ℝ × ℝ => f p.2 * g p.1) := by
      funext p
      simp only [Function.uncurry, Φ, Set.indicator, mem_setOf_eq]
    have hm : AEStronglyMeasurable (Function.uncurry Φ) (μ.prod μ) := by
      rw [heq]
      exact hm0.indicator (measurableSet_le measurable_snd measurable_fst)
    haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
    refine Integrable.of_bound hm (Bf * Bg) ?_
    rw [hμ, Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).mpr
      (Eventually.of_forall fun p hp => ?_)
    simp only [Function.uncurry, Φ]
    split_ifs
    · rw [norm_mul]; exact mul_le_mul (hfB _ hp.2) (hgB _ hp.1) (norm_nonneg _) hBf
    · rw [norm_zero]; positivity
  have key := integral_integral_swap hΦ
  have hlhs : ∫ s in (0 : ℝ)..L, (∫ t in (0 : ℝ)..s, f t) * g s = ∫ s, ∫ t, Φ s t ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have e : (fun t => Φ s t) = (Iic s).indicator (fun t => f t * g s) := by
      funext t; simp only [Φ, Set.indicator, mem_Iic]
    have e2 : Icc 0 L ∩ Iic s = Icc 0 s := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hs.2⟩, h3⟩
    simp only [hμ]
    rw [e, setIntegral_indicator measurableSet_Iic, e2, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hs.1, intervalIntegral.integral_mul_const]
  have hrhs : ∫ t in (0 : ℝ)..L, f t * ∫ s in t..L, g s = ∫ t, ∫ s, Φ s t ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    have e : (fun s => Φ s t) = (Ici t).indicator (fun s => f t * g s) := by
      funext s; simp only [Φ, Set.indicator, mem_Ici]
    have e2 : Icc 0 L ∩ Ici t = Icc t L := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨ht.1.trans h1, h2⟩, h1⟩
    simp only [hμ]
    rw [e, setIntegral_indicator measurableSet_Ici, e2, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.2, intervalIntegral.integral_const_mul]
  rw [hlhs, hrhs, key]

/-- Primitives of bounded functions are continuous on the interval. -/
lemma continuousOn_primitive_of_bound {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 L))) {B : ℝ}
    (hB : ∀ t ∈ Icc 0 L, ‖f t‖ ≤ B) :
    ContinuousOn (fun s => ∫ t in (0 : ℝ)..s, f t) (Icc 0 L) := by
  have hi : IntegrableOn f (uIcc 0 L) volume := by
    rw [uIcc_of_le hL]
    haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) L)) := by infer_instance
    exact Integrable.of_bound hf B ((ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall hB))
  have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := L) hi
  rwa [uIcc_of_le hL] at this

lemma intervalIntegrable_of_restrict_bound {L : ℝ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 L))) {B : ℝ}
    (hB : ∀ t ∈ Icc 0 L, ‖f t‖ ≤ B) {a b : ℝ} (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L) :
    IntervalIntegrable f volume a b := by
  have hsub : uIcc a b ⊆ Icc 0 L := uIcc_subset_Icc ha hb
  refine (IntegrableOn.mono_set ?_ hsub).intervalIntegrable
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) L)) := by infer_instance
  exact Integrable.of_bound hf B ((ae_restrict_iff' measurableSet_Icc).mpr
    (Eventually.of_forall hB))

/-- Bound for a primitive of a bounded function. -/
lemma norm_primitive_le {L : ℝ} {f : ℝ → ℂ} {B : ℝ} (hB : ∀ t ∈ Icc 0 L, ‖f t‖ ≤ B) {s : ℝ}
    (hs : s ∈ Icc 0 L) : ‖∫ t in (0 : ℝ)..s, f t‖ ≤ B * L := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hs.1.trans hs.2⟩)
  have h : ‖∫ t in (0 : ℝ)..s, f t‖ ≤ B * |s - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
      rw [uIoc_of_le hs.1] at ht; exact hB t ⟨ht.1.le, ht.2.trans hs.2⟩
  rw [sub_zero, abs_of_nonneg hs.1] at h
  exact h.trans (mul_le_mul_of_nonneg_left hs.2 hB0)

/-- First integration by parts: `∫₀^L r(θ, s) g(s) ds = -∫₀^L ρ(θ, t) (G(t) - c) dt`. -/
lemma kernel_integral_eq {L : ℝ} (hL : 0 ≤ L) {r ρ : ℝ → ℝ → ℂ} {g : ℝ → ℂ} {θ Bρ Bg : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Icc 0 L)))
    (hgB : ∀ t ∈ Icc 0 L, ‖g t‖ ≤ Bg)
    (hρm : AEStronglyMeasurable (ρ θ) (volume.restrict (Icc 0 L)))
    (hρB : ∀ t ∈ Icc 0 L, ‖ρ θ t‖ ≤ Bρ)
    (hr : ∀ s ∈ Icc 0 L, r θ s = r θ 0 + ∫ t in (0 : ℝ)..s, ρ θ t)
    (hper : r θ L = r θ 0) (hG : ∫ t in (0 : ℝ)..L, g t = 0) (c : ℂ) :
    ∫ s in (0 : ℝ)..L, r θ s * g s =
      -∫ t in (0 : ℝ)..L, ρ θ t * ((∫ u in (0 : ℝ)..t, g u) - c) := by
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  have hL' : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  have hgi := intervalIntegrable_of_restrict_bound hg hgB h0 hL'
  have hρi := intervalIntegrable_of_restrict_bound hρm hρB h0 hL'
  have hPc := continuousOn_primitive_of_bound hL hρm hρB
  have hGc := continuousOn_primitive_of_bound hL hg hgB
  have h1 : ∫ s in (0 : ℝ)..L, r θ s * g s =
      ∫ s in (0 : ℝ)..L, (r θ 0 * g s + (∫ t in (0 : ℝ)..s, ρ θ t) * g s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hL] at hs
    simp only [hr s hs]; ring
  have hint2 : IntervalIntegrable (fun s => (∫ t in (0 : ℝ)..s, ρ θ t) * g s) volume 0 L := by
    refine intervalIntegrable_of_restrict_bound
      ((hPc.aestronglyMeasurable measurableSet_Icc).mul hg) (B := Bρ * L * Bg)
      (fun s hs => ?_) h0 hL'
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_mul (norm_primitive_le hρB hs) (hgB s hs) (norm_nonneg _)
      (by have := (norm_nonneg _).trans (hρB 0 h0); positivity)
  rw [h1, intervalIntegral.integral_add (hgi.const_mul _) hint2,
    intervalIntegral.integral_const_mul, hG, mul_zero, zero_add,
    integral_primitive_mul_eq hL hρm hg hρB hgB]
  have h2 : ∀ t ∈ Icc 0 L, ∫ s in t..L, g s = -∫ u in (0 : ℝ)..t, g u := by
    intro t ht
    have := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_restrict_bound hg hgB h0 ht)
      (intervalIntegrable_of_restrict_bound hg hgB ht hL')
    rw [hG] at this
    linear_combination this
  have hρ0 : ∫ t in (0 : ℝ)..L, ρ θ t = 0 := by
    have := hr L hL'
    rw [hper] at this
    linear_combination -this
  have hGint : IntervalIntegrable (fun t => ρ θ t * ∫ u in (0 : ℝ)..t, g u) volume 0 L := by
    refine intervalIntegrable_of_restrict_bound
      (hρm.mul (hGc.aestronglyMeasurable measurableSet_Icc)) (B := Bρ * (Bg * L))
      (fun s hs => ?_) h0 hL'
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_mul (hρB s hs) (norm_primitive_le hgB hs) (norm_nonneg _)
      ((norm_nonneg _).trans (hρB 0 h0))
  rw [intervalIntegral.integral_congr (g := fun t => -(ρ θ t * ∫ u in (0 : ℝ)..t, g u))
    (fun t ht => by rw [uIcc_of_le hL] at ht; simp only [h2 t ht]; ring)]
  rw [intervalIntegral.integral_congr (f := fun t => ρ θ t * ((∫ u in (0 : ℝ)..t, g u) - c))
    (g := fun t => ρ θ t * (∫ u in (0 : ℝ)..t, g u) - c * ρ θ t) (fun t _ => by ring),
    intervalIntegral.integral_sub hGint (hρi.const_mul c), intervalIntegral.integral_const_mul,
    hρ0, intervalIntegral.integral_neg]
  ring

/-- **Double integration by parts for a periodic kernel.** -/
theorem norm_kernel_form_le {L : ℝ} (hL : 0 ≤ L) {r ρ : ℝ → ℝ → ℂ} {g : ℝ → ℂ}
    {M Bρ Bg : ℝ} (hM : 0 ≤ M)
    (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hρm : ∀ θ ∈ Icc 0 L, AEStronglyMeasurable (ρ θ) (volume.restrict (Icc 0 L)))
    (hρB : ∀ θ ∈ Icc 0 L, ∀ t ∈ Icc 0 L, ‖ρ θ t‖ ≤ Bρ)
    (hr : ∀ θ ∈ Icc 0 L, ∀ s ∈ Icc 0 L, r θ s = r θ 0 + ∫ t in (0 : ℝ)..s, ρ θ t)
    (hρL : ∀ θ₁ ∈ Icc 0 L, ∀ θ₂ ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      ‖ρ θ₁ t - ρ θ₂ t‖ ≤ M * |θ₁ - θ₂|)
    (hper_s : ∀ θ ∈ Icc 0 L, r θ L = r θ 0) (hper_θ : ∀ s ∈ Icc 0 L, r L s = r 0 s)
    (hG : ∫ t in (0 : ℝ)..L, g t = 0) (c : ℂ) :
    ‖∫ θ in (0 : ℝ)..L, conj (g θ) * ∫ s in (0 : ℝ)..L, r θ s * g s‖ ≤
      M * (∫ t in (0 : ℝ)..L, ‖(∫ u in (0 : ℝ)..t, g u) - c‖) ^ 2 := by
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  have hL' : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  have hgr : AEStronglyMeasurable g (volume.restrict (Icc 0 L)) := hg.restrict
  have hgBr : ∀ t ∈ Icc 0 L, ‖g t‖ ≤ Bg := fun t _ => hgB t
  set Gc : ℝ → ℂ := fun t => (∫ u in (0 : ℝ)..t, g u) - c with hGc
  have hGcc : ContinuousOn Gc (Icc 0 L) :=
    (continuousOn_primitive_of_bound hL hgr hgBr).sub continuousOn_const
  obtain ⟨BG, hBG⟩ := isCompact_Icc.exists_bound_of_continuousOn hGcc
  set N : ℝ := ∫ t in (0 : ℝ)..L, ‖Gc t‖ with hN
  have hN0 : 0 ≤ N := intervalIntegral.integral_nonneg hL fun t _ => norm_nonneg _
  have hNi : IntervalIntegrable (fun t => ‖Gc t‖) volume 0 L :=
    (hGcc.norm.intervalIntegrable_of_Icc hL)
  set Φ : ℝ → ℂ := fun θ => -∫ t in (0 : ℝ)..L, ρ θ t * Gc t with hΦ
  have hA : ∀ θ ∈ Icc 0 L, ∫ s in (0 : ℝ)..L, r θ s * g s = Φ θ := fun θ hθ =>
    kernel_integral_eq hL hgr hgBr (hρm θ hθ) (hρB θ hθ) (hr θ hθ) (hper_s θ hθ) hG c
  have hρGi : ∀ θ ∈ Icc 0 L, IntervalIntegrable (fun t => ρ θ t * Gc t) volume 0 L :=
    fun θ hθ => intervalIntegrable_of_restrict_bound
      ((hρm θ hθ).mul (hGcc.aestronglyMeasurable measurableSet_Icc)) (B := Bρ * BG)
      (fun t ht => by
        simp only [Pi.mul_apply]
        rw [norm_mul]
        exact mul_le_mul (hρB θ hθ t ht) (hBG t ht) (norm_nonneg _)
          ((norm_nonneg _).trans (hρB θ hθ 0 h0))) h0 hL'
  have hΦlip : ∀ θ₁ ∈ Icc 0 L, ∀ θ₂ ∈ Icc 0 L, ‖Φ θ₁ - Φ θ₂‖ ≤ M * N * |θ₁ - θ₂| := by
    intro θ₁ h₁ θ₂ h₂
    have e : Φ θ₁ - Φ θ₂ = -∫ t in (0 : ℝ)..L, (ρ θ₁ t - ρ θ₂ t) * Gc t := by
      have := intervalIntegral.integral_sub (hρGi θ₁ h₁) (hρGi θ₂ h₂)
      simp only [hΦ]
      rw [show (fun t => (ρ θ₁ t - ρ θ₂ t) * Gc t) =
        fun t => ρ θ₁ t * Gc t - ρ θ₂ t * Gc t from funext fun t => by ring, this]
      ring
    rw [e, norm_neg]
    calc ‖∫ t in (0 : ℝ)..L, (ρ θ₁ t - ρ θ₂ t) * Gc t‖ ≤
        ∫ t in (0 : ℝ)..L, M * |θ₁ - θ₂| * ‖Gc t‖ := by
          refine intervalIntegral.norm_integral_le_of_norm_le hL
            (Eventually.of_forall fun t ht => ?_) (hNi.const_mul _)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hρL θ₁ h₁ θ₂ h₂ t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
      _ = M * N * |θ₁ - θ₂| := by rw [intervalIntegral.integral_const_mul, hN]; ring
  have hper : Φ L = Φ 0 := by
    rw [← hA L hL', ← hA 0 h0]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hL] at hs
    simp only [hper_θ s hs]
  set Ψ : ℝ → ℂ := fun θ => Φ (projIcc 0 L hL θ) with hΨ
  have hΨL : LipschitzWith (M * N).toNNReal Ψ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hM hN0), Real.dist_eq]
    refine (hΦlip _ (projIcc 0 L hL x).2 _ (projIcc 0 L hL y).2).trans ?_
    exact mul_le_mul_of_nonneg_left (abs_projIcc_sub_projIcc hL) (mul_nonneg hM hN0)
  have hΨeq : ∀ θ ∈ Icc 0 L, Ψ θ = Φ θ := fun θ hθ => by
    simp only [hΨ, projIcc_of_mem hL hθ]
  have hΨd : ∀ θ, Ψ θ = Ψ 0 + ∫ t in (0 : ℝ)..θ, deriv Ψ t := fun θ => by
    rw [integral_deriv_of_lipschitz hΨL]; ring
  have hdB : ∀ t, ‖deriv Ψ t‖ ≤ M * N := fun t => by
    have := norm_deriv_le_of_lipschitz hΨL (x₀ := t)
    rwa [Real.coe_toNNReal _ (mul_nonneg hM hN0)] at this
  have hdm : AEStronglyMeasurable (deriv Ψ) volume := (measurable_deriv Ψ).aestronglyMeasurable
  have hcg : AEStronglyMeasurable (fun t => conj (g t)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hg
  have hcgB : ∀ t, ‖conj (g t)‖ ≤ Bg := fun t => by rw [Complex.norm_conj]; exact hgB t
  have hgi := intervalIntegrable_of_restrict_bound hgr hgBr h0 hL'
  have hcgi : IntervalIntegrable (fun t => conj (g t)) volume 0 L :=
    intervalIntegrable_of_restrict_bound hcg.restrict (fun t _ => hcgB t) h0 hL'
  have hPi : IntervalIntegrable (fun θ => (∫ t in (0 : ℝ)..θ, deriv Ψ t) * conj (g θ)) volume 0 L := by
    refine intervalIntegrable_of_restrict_bound
      (((continuousOn_primitive_of_bound hL hdm.restrict (fun t _ => hdB t)).aestronglyMeasurable
        measurableSet_Icc).mul hcg.restrict) (B := M * N * L * Bg) (fun θ hθ => ?_) h0 hL'
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_mul (norm_primitive_le (fun t _ => hdB t) hθ) (hcgB θ) (norm_nonneg _)
      (by positivity)
  have hmain : ∫ θ in (0 : ℝ)..L, conj (g θ) * ∫ s in (0 : ℝ)..L, r θ s * g s =
      -∫ t in (0 : ℝ)..L, deriv Ψ t * conj (Gc t) := by
    have e1 : ∫ θ in (0 : ℝ)..L, conj (g θ) * ∫ s in (0 : ℝ)..L, r θ s * g s =
        ∫ θ in (0 : ℝ)..L, (Ψ 0 * conj (g θ) + (∫ t in (0 : ℝ)..θ, deriv Ψ t) * conj (g θ)) := by
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le hL] at hθ
      rw [hA θ hθ, ← hΨeq θ hθ, hΨd θ]; ring
    rw [e1, intervalIntegral.integral_add (hcgi.const_mul _) hPi,
      intervalIntegral.integral_const_mul, intervalIntegral_conj, hG, map_zero, mul_zero,
      zero_add, integral_primitive_mul_eq hL hdm.restrict hcg.restrict (fun t _ => hdB t)
        (fun t _ => hcgB t)]
    have h2 : ∀ t ∈ Icc 0 L, ∫ s in t..L, conj (g s) = -conj (Gc t) - conj c := by
      intro t ht
      have := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_restrict_bound hgr hgBr h0 ht)
        (intervalIntegrable_of_restrict_bound hgr hgBr ht hL')
      rw [hG] at this
      rw [intervalIntegral_conj, hGc]
      simp only [map_sub]
      have h3 : ∫ s in t..L, g s = -∫ u in (0 : ℝ)..t, g u := by linear_combination this
      rw [h3, map_neg]; ring
    have hdi : IntervalIntegrable (deriv Ψ) volume 0 L :=
      intervalIntegrable_of_restrict_bound hdm.restrict (fun t _ => hdB t) h0 hL'
    have hdGi : IntervalIntegrable (fun t => deriv Ψ t * conj (Gc t)) volume 0 L := by
      refine intervalIntegrable_of_restrict_bound (hdm.restrict.mul
        (Complex.continuous_conj.comp_aestronglyMeasurable
          (hGcc.aestronglyMeasurable measurableSet_Icc))) (B := M * N * BG)
        (fun t ht => ?_) h0 hL'
      simp only [Pi.mul_apply]
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hdB t) (hBG t ht) (norm_nonneg _) (by positivity)
    rw [intervalIntegral.integral_congr (g := fun t => -(deriv Ψ t * conj (Gc t)) -
        conj c * deriv Ψ t) (fun t ht => by
          rw [uIcc_of_le hL] at ht; simp only [h2 t ht]; ring),
      intervalIntegral.integral_sub (f := fun t => -(deriv Ψ t * conj (Gc t))) hdGi.neg
        (hdi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_neg,
      integral_deriv_of_lipschitz hΨL, hΨeq L hL', hΨeq 0 h0, hper, sub_self, mul_zero,
      sub_zero]
  rw [hmain, norm_neg]
  calc ‖∫ t in (0 : ℝ)..L, deriv Ψ t * conj (Gc t)‖ ≤ ∫ t in (0 : ℝ)..L, M * N * ‖Gc t‖ := by
        refine intervalIntegral.norm_integral_le_of_norm_le hL
          (Eventually.of_forall fun t _ => ?_) (hNi.const_mul _)
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hdB t) (norm_nonneg _)
    _ = M * N ^ 2 := by rw [intervalIntegral.integral_const_mul, ← hN]; ring

end PolyaNeumann

end
