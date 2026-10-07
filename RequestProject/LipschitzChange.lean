module

public import RequestProject.ArcLength
public import RequestProject.CurveContinuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Lipschitz maps of the plane and of closed curves (tools for Section 10)

* `volume_image_eq_zero_of_lipschitzOnWith`: a Lipschitz map of the plane sends null sets to null
  sets;
* `abs_det_le_sq_norm`, `abs_det_fderiv_le`: `|det Df| ≤ ‖Df‖² ≤ K²` for a map that is
  `K`-Lipschitz on an open set;
* `volume_image_eq_lintegral`: change of variables `|f(Ω)| = ∫_Ω |det Df|` for maps that are
  Lipschitz and injective on an open set `Ω` (via Rademacher's theorem);
* `tendsto_integral_signedAreaDensity`: the signed-area integral `∫₀^{2π} Im(conj γ · γ')` is
  continuous under uniform convergence of uniformly Lipschitz `2π`-periodic curves.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

/-- A Lipschitz map of the plane sends null sets to null sets. -/
lemma volume_image_eq_zero_of_lipschitzOnWith {f : ℂ → ℂ} {K : NNReal} {s : Set ℂ}
    (hf : LipschitzOnWith K f s) (hs : volume s = 0) : volume (f '' s) = 0 := by
  set P : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  have hpre : ∀ t : Set ℂ, volume t = (volume : Measure (ℝ × ℝ)) (P '' t) := by
    intro t
    have : (P : ℂ → ℝ × ℝ) '' t = Complex.measurableEquivRealProd.symm ⁻¹' t := by
      rw [← MeasurableEquiv.image_eq_preimage_symm]; rfl
    rw [this, (Complex.volume_preserving_equiv_real_prod.symm _).measure_preimage_equiv]
  have h2 : (μH[((2 : NNReal) : ℝ)] : Measure (ℝ × ℝ)) = volume := by
    rw [NNReal.coe_ofNat]; exact MeasureTheory.hausdorffMeasure_prod_real
  have hg : LipschitzOnWith (‖(P : ℂ →L[ℝ] ℝ × ℝ)‖₊ * K * ‖(P.symm : ℝ × ℝ →L[ℝ] ℂ)‖₊)
      ((P : ℂ → ℝ × ℝ) ∘ f ∘ P.symm) (P '' s) := by
    have h1 := (P : ℂ →L[ℝ] ℝ × ℝ).lipschitz.lipschitzOnWith (s := f '' s) |>.comp hf
      (mapsTo_image f s)
    have h3 := h1.comp ((P.symm : ℝ × ℝ →L[ℝ] ℂ).lipschitz.lipschitzOnWith (s := P '' s))
      (by rintro _ ⟨z, hz, rfl⟩; simpa using hz)
    exact h3
  have himg : ((P : ℂ → ℝ × ℝ) ∘ f ∘ P.symm) '' (P '' s) = P '' (f '' s) := by
    rw [← image_comp, ← image_comp]
    congr 1
  have hle := hg.hausdorffMeasure_image_le (d := ((2 : NNReal) : ℝ)) (by positivity)
  rw [himg, h2, ← hpre, ← hpre, hs, mul_zero] at hle
  exact le_antisymm hle (zero_le)

/-- `|det A| ≤ ‖A‖²` for a real-linear map of the plane. -/
lemma abs_det_le_sq_norm (A : ℂ →L[ℝ] ℂ) : |A.det| ≤ ‖A‖ ^ 2 := by
  have h1 := Measure.addHaar_image_continuousLinearMap (volume : Measure ℂ) A (Metric.ball 0 1)
  have hsub : (A : ℂ → ℂ) '' Metric.ball 0 1 ⊆ Metric.closedBall 0 ‖A‖ := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_ball_zero_iff] at hz
    rw [mem_closedBall_zero_iff]
    calc ‖A z‖ ≤ ‖A‖ * ‖z‖ := A.le_opNorm z
      _ ≤ ‖A‖ * 1 := by gcongr
      _ = ‖A‖ := mul_one _
  have h2 := measure_mono (μ := (volume : Measure ℂ)) hsub
  rw [h1, Measure.addHaar_closedBall _ _ (norm_nonneg _), Complex.finrank_real_complex] at h2
  have hpos : (volume : Measure ℂ) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure ℂ) (Metric.ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h3 := (ENNReal.mul_le_mul_iff_left hpos hfin).mp h2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  exact h3

/-- `|det Df(x)| ≤ K²` at every point of an open set on which `f` is `K`-Lipschitz. -/
lemma abs_det_fderiv_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} {K : NNReal}
    (hf : LipschitzOnWith K f Ω) {x : ℂ} (hx : x ∈ Ω) :
    |(fderiv ℝ f x).det| ≤ (K : ℝ) ^ 2 :=
  (abs_det_le_sq_norm _).trans (pow_le_pow_left₀ (norm_nonneg _)
    (norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hf) 2)

/-- Change of variables for a map that is Lipschitz and injective on an open set:
`|f(Ω)| = ∫_Ω |det Df|`. -/
theorem volume_image_eq_lintegral {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} {K : NNReal}
    (hf : LipschitzOnWith K f Ω) (hinj : InjOn f Ω) :
    volume (f '' Ω) =
      ∫⁻ x in Ω, ENNReal.ofReal |(fderiv ℝ f x).det| := by
  set s' := Ω ∩ {x | DifferentiableAt ℝ f x} with hs'
  have hD : MeasurableSet {x | DifferentiableAt ℝ f x} := measurableSet_of_differentiableAt ℝ f
  have hnull : volume (Ω \ s') = 0 := by
    have h := hf.ae_differentiableWithinAt_of_mem (μ := volume)
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro x hx hcon
    exact hx.2 ⟨hx.1, (hcon hx.1).differentiableAt (hΩ.mem_nhds hx.1)⟩
  have hder : ∀ x ∈ s', HasFDerivWithinAt f (fderiv ℝ f x) s' x := fun x hx =>
    hx.2.hasFDerivAt.hasFDerivWithinAt
  have h1 := lintegral_abs_det_fderiv_eq_addHaar_image volume (hΩ.measurableSet.inter hD) hder
    (hinj.mono inter_subset_left)
  have h2 : volume (f '' Ω) = volume (f '' s') := by
    refine le_antisymm ?_ (measure_mono (image_mono inter_subset_left))
    calc volume (f '' Ω) ≤ volume (f '' s' ∪ f '' (Ω \ s')) := by
          rw [← image_union, union_diff_cancel inter_subset_left]
      _ ≤ volume (f '' s') + volume (f '' (Ω \ s')) := measure_union_le _ _
      _ = volume (f '' s') := by
          rw [volume_image_eq_zero_of_lipschitzOnWith (hf.mono diff_subset) hnull, add_zero]
  rw [h2, ← h1]
  refine setLIntegral_congr (ae_eq_set.mpr ⟨?_, hnull⟩)
  rw [diff_eq_empty.mpr inter_subset_left, measure_empty]

/-- A continuous `2π`-periodic function is bounded. -/
lemma exists_bound_of_periodic {β : ℝ → ℂ} (hβ : Continuous β)
    (hp : Function.Periodic β (2 * π)) : ∃ M, ∀ θ, ‖β θ‖ ≤ M := by
  have hc : IsCompact (β '' Icc 0 (0 + 2 * π)) := isCompact_Icc.image hβ
  rw [hp.image_Icc Real.two_pi_pos] at hc
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  exact ⟨M, fun θ => hM _ (mem_range_self θ)⟩

/-- Products of a bounded derivative-type factor and a bounded continuous factor are
interval integrable. -/
lemma intervalIntegrable_conj_mul {f g : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) {A B : ℝ} (hA : ∀ θ, ‖f θ‖ ≤ A) (hB : ∀ θ, ‖g θ‖ ≤ B)
    (a b : ℝ) : IntervalIntegrable (fun θ => conj (f θ) * g θ) volume a b := by
  refine intervalIntegrable_of_bounded
    ((Complex.continuous_conj.comp_aestronglyMeasurable hf).mul hg) (B := A * B)
    (fun θ => ?_) a b
  show ‖conj (f θ) * g θ‖ ≤ A * B
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hA θ) (hB θ) (norm_nonneg _) ((norm_nonneg _).trans (hA θ))

/-- Integration by parts for Lipschitz `2π`-periodic curves:
`∫₀^{2π} conj β · δ' = -∫₀^{2π} conj β' · δ`. -/
lemma integral_conj_mul_deriv_periodic {β δ : ℝ → ℂ} {Kβ Kδ : NNReal}
    (hβ : LipschitzWith Kβ β) (hδ : LipschitzWith Kδ δ)
    (hβp : Function.Periodic β (2 * π)) (hδp : Function.Periodic δ (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (β θ) * deriv δ θ =
      -∫ θ in (0 : ℝ)..(2 * π), conj (deriv β θ) * δ θ := by
  obtain ⟨Mβ, hMβ⟩ := exists_bound_of_periodic hβ.continuous hβp
  obtain ⟨Mδ, hMδ⟩ := exists_bound_of_periodic hδ.continuous hδp
  have hMβ0 : 0 ≤ Mβ := (norm_nonneg _).trans (hMβ 0)
  have hMδ0 : 0 ≤ Mδ := (norm_nonneg _).trans (hMδ 0)
  set P : ℝ → ℂ := fun θ => conj (β θ) * δ θ with hPdef
  have hP : LipschitzWith (Mβ.toNNReal * Kδ + Kβ * Mδ.toNNReal) P := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hδ.dist_le_mul x y
    have h2 := hβ.dist_le_mul x y
    rw [dist_eq_norm] at h1 h2 ⊢
    have e : P x - P y = conj (β x) * (δ x - δ y) + conj (β x - β y) * δ y := by
      simp only [hPdef, map_sub]; ring
    rw [e]
    push_cast
    rw [Real.coe_toNNReal _ hMβ0, Real.coe_toNNReal _ hMδ0]
    calc ‖conj (β x) * (δ x - δ y) + conj (β x - β y) * δ y‖
        ≤ ‖β x‖ * ‖δ x - δ y‖ + ‖β x - β y‖ * ‖δ y‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      _ ≤ Mβ * (Kδ * dist x y) + Kβ * dist x y * Mδ := by
          gcongr
          · exact hMβ x
          · exact hMδ y
      _ = (Mβ * Kδ + Kβ * Mδ) * dist x y := by ring
  have hderiv : ∀ᵐ θ, θ ∈ Ι (0 : ℝ) (2 * π) →
      deriv P θ = conj (deriv β θ) * δ θ + conj (β θ) * deriv δ θ := by
    filter_upwards [hβ.ae_differentiableAt (μ := volume),
      hδ.ae_differentiableAt (μ := volume)] with θ h1 h2 _
    exact (h1.hasDerivAt.star.mul h2.hasDerivAt).deriv
  have hFTC := integral_deriv_of_lipschitz hP 0 (2 * π)
  rw [intervalIntegral.integral_congr_ae hderiv,
    intervalIntegral.integral_add
      (intervalIntegrable_conj_mul (measurable_deriv β).aestronglyMeasurable
        hδ.continuous.aestronglyMeasurable (fun _ => norm_deriv_le_of_lipschitz hβ) hMδ _ _)
      (intervalIntegrable_conj_mul hβ.continuous.aestronglyMeasurable
        (measurable_deriv δ).aestronglyMeasurable hMβ (fun _ => norm_deriv_le_of_lipschitz hδ) _ _)] at hFTC
  have hP2 : P (2 * π) = P 0 := by
    simp only [hPdef]; rw [show (2 * π : ℝ) = 0 + 2 * π by ring, hβp, hδp]
  rw [hP2, sub_self] at hFTC
  linear_combination hFTC

/-- Continuity of the signed-area integral under uniform convergence of uniformly Lipschitz
periodic curves. -/
theorem tendsto_integral_signedAreaDensity {α : ℕ → ℝ → ℂ} {β : ℝ → ℂ} {K : NNReal}
    (hα : ∀ n, LipschitzWith K (α n)) (hβ : LipschitzWith K β)
    (hαp : ∀ n, Function.Periodic (α n) (2 * π)) (hβp : Function.Periodic β (2 * π))
    (h : TendstoUniformlyOn α β atTop (Icc 0 (2 * π))) :
    Tendsto (fun n => ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity (α n) θ) atTop
      (𝓝 (∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity β θ)) := by
  have hint : ∀ {γ : ℝ → ℂ} {Kγ : NNReal}, LipschitzWith Kγ γ → Function.Periodic γ (2 * π) →
      IntervalIntegrable (fun θ => conj (γ θ) * deriv γ θ) volume 0 (2 * π) := by
    intro γ Kγ hγ hγp
    obtain ⟨M, hM⟩ := exists_bound_of_periodic hγ.continuous hγp
    exact intervalIntegrable_conj_mul hγ.continuous.aestronglyMeasurable
      (measurable_deriv γ).aestronglyMeasurable hM (fun _ => norm_deriv_le_of_lipschitz hγ) _ _
  have him : ∀ {γ : ℝ → ℂ} {Kγ : NNReal}, LipschitzWith Kγ γ → Function.Periodic γ (2 * π) →
      ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ θ =
        (∫ θ in (0 : ℝ)..(2 * π), conj (γ θ) * deriv γ θ).im := by
    intro γ Kγ hγ hγp
    exact Complex.imCLM.intervalIntegral_comp_comm (hint hγ hγp)
  have e : (fun n => ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity (α n) θ) =
      fun n => (∫ θ in (0 : ℝ)..(2 * π), conj (α n θ) * deriv (α n) θ).im :=
    funext fun n => him (hα n) (hαp n)
  rw [e, him hβ hβp]
  refine (Complex.continuous_im.tendsto _).comp (Metric.tendsto_nhds.mpr fun ε hε => ?_)
  set η := ε / (4 * π * K + 1) with hηdef
  have hη : 0 < η := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h η hη] with n hn
  set δ : ℝ → ℂ := fun θ => α n θ - β θ with hδdef
  have hδL : LipschitzWith (K + K) δ := (hα n).sub hβ
  have hδp : Function.Periodic δ (2 * π) := fun θ => by simp only [hδdef, hαp n θ, hβp θ]
  have hδd : ∀ᵐ θ, θ ∈ Ι (0 : ℝ) (2 * π) →
      conj (α n θ) * deriv (α n) θ - conj (β θ) * deriv β θ =
        conj (δ θ) * deriv (α n) θ + conj (β θ) * deriv δ θ := by
    filter_upwards [(hα n).ae_differentiableAt (μ := volume),
      hβ.ae_differentiableAt (μ := volume)] with θ h1 h2 _
    have hd : deriv δ θ = deriv (α n) θ - deriv β θ := deriv_sub h1 h2
    rw [hd]; simp only [hδdef, map_sub]; ring
  obtain ⟨Mβ, hMβ⟩ := exists_bound_of_periodic hβ.continuous hβp
  obtain ⟨Mδ, hMδ⟩ := exists_bound_of_periodic hδL.continuous hδp
  have i1 : IntervalIntegrable (fun θ => conj (δ θ) * deriv (α n) θ) volume 0 (2 * π) :=
    intervalIntegrable_conj_mul hδL.continuous.aestronglyMeasurable
      (measurable_deriv _).aestronglyMeasurable hMδ (fun _ => norm_deriv_le_of_lipschitz (hα n)) _ _
  have i2 : IntervalIntegrable (fun θ => conj (β θ) * deriv δ θ) volume 0 (2 * π) :=
    intervalIntegrable_conj_mul hβ.continuous.aestronglyMeasurable
      (measurable_deriv _).aestronglyMeasurable hMβ (fun _ => norm_deriv_le_of_lipschitz hδL) _ _
  have key : (∫ θ in (0 : ℝ)..(2 * π), conj (α n θ) * deriv (α n) θ) -
      ∫ θ in (0 : ℝ)..(2 * π), conj (β θ) * deriv β θ =
      (∫ θ in (0 : ℝ)..(2 * π), conj (δ θ) * deriv (α n) θ) -
        ∫ θ in (0 : ℝ)..(2 * π), conj (deriv β θ) * δ θ := by
    rw [← intervalIntegral.integral_sub (hint (hα n) (hαp n)) (hint hβ hβp),
      intervalIntegral.integral_congr_ae hδd, intervalIntegral.integral_add i1 i2,
      integral_conj_mul_deriv_periodic hβ hδL hβp hδp]
    ring
  have hδη : ∀ θ ∈ Ι (0 : ℝ) (2 * π), ‖δ θ‖ ≤ η := by
    intro θ hθ
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    have := hn θ (Ioc_subset_Icc_self hθ)
    rw [dist_comm, dist_eq_norm] at this
    exact this.le
  have b1 : ‖∫ θ in (0 : ℝ)..(2 * π), conj (δ θ) * deriv (α n) θ‖ ≤ η * K * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hδη θ hθ) (norm_deriv_le_of_lipschitz (hα n)) (norm_nonneg _) hη.le
  have b2 : ‖∫ θ in (0 : ℝ)..(2 * π), conj (deriv β θ) * δ θ‖ ≤ K * η * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (norm_deriv_le_of_lipschitz hβ) (hδη θ hθ) (norm_nonneg _) K.2
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at b1 b2
  have hfin : 4 * π * K * η < ε := by
    rw [hηdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, K.2]
  rw [dist_eq_norm, key]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ η * K * (2 * π) + K * η * (2 * π) := add_le_add b1 b2
    _ = 4 * π * K * η := by ring
    _ < ε := hfin

end PolyaNeumann

end
