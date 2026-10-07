module

public import RequestProject.LipschitzChange
public import RequestProject.Defs

/-!
# Bi-Lipschitz changes of variables and the `L²` pullback

For a homeomorphism `f` of the plane which is `K`-Lipschitz on an open set `Ω` and whose inverse
is `K`-Lipschitz on `f(Ω)`:

* `ae_inv_sq_le_abs_det`: `|det Df| ≥ K⁻²` almost everywhere on `Ω`;
* `quasiMeasurePreserving_restrict`, `quasiMeasurePreserving_symm_restrict`: `f` and `f⁻¹` are
  quasi-measure-preserving between `Ω` and `f(Ω)`;
* `lintegral_image_bilip`, `integral_image_bilip`: the change of variables formulas
  `∫_{f(Ω)} g = ∫_Ω |det Df| g ∘ f`;
* `bilipPull`: the pullback `L²(f(Ω)) ≃ L²(Ω)`, `v ↦ v ∘ f`, with
  `⟨v, w⟩_{L²(f(Ω))} = ∫_Ω |det Df| ⟨v ∘ f, w ∘ f⟩` (`inner_eq_integral_bilipPull`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : NNReal}

/-- A Lipschitz constant may be increased. -/
lemma lipschitzOnWith_weaken {F : ℂ → ℂ} {s : Set ℂ} {K' : NNReal} (h : LipschitzOnWith K F s)
    (hKK : K ≤ K') : LipschitzOnWith K' F s := fun _ hx _ hy =>
  (h hx hy).trans (mul_le_mul_left (ENNReal.coe_le_coe.mpr hKK) _)

/-- A map that is Lipschitz on an open set is differentiable almost everywhere on it. -/
lemma ae_differentiableAt_of_lipschitzOnWith {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : LipschitzOnWith K F U) : ∀ᵐ x ∂(volume.restrict U), DifferentiableAt ℝ F x := by
  have h := hF.ae_differentiableWithinAt_of_mem (μ := volume)
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [h] with x hx hxU
  exact (hx hxU).differentiableAt (hU.mem_nhds hxU)

/-- `f` is quasi-measure-preserving from `Ω` to `f(Ω)`. -/
lemma quasiMeasurePreserving_restrict (hg : LipschitzOnWith K f.symm (f '' Ω)) :
    Measure.QuasiMeasurePreserving f (volume.restrict Ω) (volume.restrict (f '' Ω)) := by
  refine ⟨f.continuous.measurable, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply f.continuous.measurable hs,
    Measure.restrict_apply (f.continuous.measurable hs)]
  rw [Measure.restrict_apply hs] at h0
  refine measure_mono_null ?_ (volume_image_eq_zero_of_lipschitzOnWith
    (hg.mono inter_subset_right) h0)
  intro x ⟨hxs, hxΩ⟩
  exact ⟨f x, ⟨hxs, mem_image_of_mem f hxΩ⟩, f.symm_apply_apply x⟩

/-- `f⁻¹` is quasi-measure-preserving from `f(Ω)` to `Ω`. -/
lemma quasiMeasurePreserving_symm_restrict (hf : LipschitzOnWith K f Ω) :
    Measure.QuasiMeasurePreserving f.symm (volume.restrict (f '' Ω)) (volume.restrict Ω) := by
  refine ⟨f.symm.continuous.measurable, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply f.symm.continuous.measurable hs,
    Measure.restrict_apply (f.symm.continuous.measurable hs)]
  rw [Measure.restrict_apply hs] at h0
  refine measure_mono_null ?_ (volume_image_eq_zero_of_lipschitzOnWith
    (hf.mono inter_subset_right) h0)
  rintro y ⟨hys, x, hxΩ, rfl⟩
  refine ⟨x, ⟨?_, hxΩ⟩, rfl⟩
  simpa using hys

/-- The differentiability set of `f` in `Ω` has full measure. -/
lemma volume_diff_differentiable (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) :
    volume (Ω \ (Ω ∩ {x | DifferentiableAt ℝ f x})) = 0 := by
  have h := hf.ae_differentiableWithinAt_of_mem (μ := volume)
  rw [ae_iff] at h
  refine measure_mono_null ?_ h
  intro x hx hcon
  exact hx.2 ⟨hx.1, (hcon hx.1).differentiableAt (hΩ.mem_nhds hx.1)⟩

/-- The images of `Ω` and of its differentiability set agree up to a null set. -/
lemma image_ae_eq_image_differentiable (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) :
    (f '' (Ω ∩ {x | DifferentiableAt ℝ f x}) : Set ℂ) =ᵐ[volume] (f '' Ω : Set ℂ) := by
  refine ae_eq_set.mpr ⟨?_, ?_⟩
  · rw [diff_eq_empty.mpr (image_mono inter_subset_left), measure_empty]
  · refine measure_mono_null ?_ (volume_image_eq_zero_of_lipschitzOnWith (hf.mono diff_subset)
      (volume_diff_differentiable hΩ hf))
    rintro _ ⟨⟨x, hx, rfl⟩, hnot⟩
    exact ⟨x, ⟨hx, fun h => hnot ⟨x, h, rfl⟩⟩, rfl⟩

/-- Change of variables for lower integrals along a bi-Lipschitz map. -/
lemma lintegral_image_bilip (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) (g : ℂ → ENNReal) :
    ∫⁻ y in f '' Ω, g y = ∫⁻ x in Ω, ENNReal.ofReal |(fderiv ℝ f x).det| * g (f x) := by
  set s' := Ω ∩ {x | DifferentiableAt ℝ f x}
  have hD : MeasurableSet {x | DifferentiableAt ℝ f x} := measurableSet_of_differentiableAt ℝ f
  have hder : ∀ x ∈ s', HasFDerivWithinAt f (fderiv ℝ f x) s' x := fun x hx =>
    hx.2.hasFDerivAt.hasFDerivWithinAt
  have h1 := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hΩ.measurableSet.inter hD)
    hder (f.injective.injOn) g
  rw [setLIntegral_congr (image_ae_eq_image_differentiable hΩ hf).symm, h1]
  refine setLIntegral_congr (ae_eq_set.mpr ⟨?_, volume_diff_differentiable hΩ hf⟩)
  rw [diff_eq_empty.mpr inter_subset_left, measure_empty]

/-- Change of variables for integrals along a bi-Lipschitz map. -/
lemma integral_image_bilip (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) (g : ℂ → ℂ) :
    ∫ y in f '' Ω, g y = ∫ x in Ω, |(fderiv ℝ f x).det| • g (f x) := by
  set s' := Ω ∩ {x | DifferentiableAt ℝ f x}
  have hD : MeasurableSet {x | DifferentiableAt ℝ f x} := measurableSet_of_differentiableAt ℝ f
  have hder : ∀ x ∈ s', HasFDerivWithinAt f (fderiv ℝ f x) s' x := fun x hx =>
    hx.2.hasFDerivAt.hasFDerivWithinAt
  have h1 := integral_image_eq_integral_abs_det_fderiv_smul volume (hΩ.measurableSet.inter hD)
    hder (f.injective.injOn) g
  rw [setIntegral_congr_set (image_ae_eq_image_differentiable hΩ hf).symm, h1]
  refine setIntegral_congr_set (ae_eq_set.mpr ⟨?_, volume_diff_differentiable hΩ hf⟩)
  rw [diff_eq_empty.mpr inter_subset_left, measure_empty]

/-- The Jacobian of a bi-Lipschitz map is bounded below: `|det Df| ≥ K⁻²` a.e. on `Ω`. -/
lemma ae_inv_sq_le_abs_det (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) :
    ∀ᵐ x ∂(volume.restrict Ω), ((K : ℝ) ^ 2)⁻¹ ≤ |(fderiv ℝ f x).det| := by
  have hU : IsOpen (f '' Ω) := f.isOpenMap _ hΩ
  have h2 := (quasiMeasurePreserving_restrict hg).ae
    (ae_differentiableAt_of_lipschitzOnWith hU hg)
  filter_upwards [ae_differentiableAt_of_lipschitzOnWith hΩ hf, h2,
    ae_restrict_mem hΩ.measurableSet] with x h1 h2 hx
  have hcomp : (fderiv ℝ f.symm (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ ℂ := by
    have h := h2.hasFDerivAt.comp x h1.hasFDerivAt
    have hid : (f.symm ∘ f : ℂ → ℂ) = id := funext f.symm_apply_apply
    rw [hid] at h
    exact h.unique (hasFDerivAt_id x)
  have hdet : (fderiv ℝ f.symm (f x)).det * (fderiv ℝ f x).det = 1 := by
    have h := congrArg ContinuousLinearMap.det hcomp
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
      ContinuousLinearMap.coe_id, LinearMap.det_id] at h
    exact (LinearMap.det_comp _ _).symm.trans h
  have hb : |(fderiv ℝ f.symm (f x)).det| ≤ (K : ℝ) ^ 2 :=
    abs_det_fderiv_le hU hg (mem_image_of_mem f hx)
  have h1' : 1 ≤ (K : ℝ) ^ 2 * |(fderiv ℝ f x).det| := by
    calc (1 : ℝ) = |(fderiv ℝ f.symm (f x)).det| * |(fderiv ℝ f x).det| := by
          rw [← abs_mul, hdet, abs_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  by_cases hK : (K : ℝ) ^ 2 = 0
  · rw [hK, inv_zero]; exact abs_nonneg _
  · rw [inv_le_iff_one_le_mul₀' (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hK))]
    exact h1'

/-! ### The `L²` pullback -/

lemma memLp_two_of_lintegral {μ : Measure ℂ} {h : ℂ → ℂ} (hm : AEStronglyMeasurable h μ)
    (hl : ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2) ∂μ < ⊤) : MemLp h 2 μ :=
  (memLp_two_iff_integrable_sq_norm hm).mpr ⟨hm.norm.pow 2,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr hl⟩

lemma lintegral_sq_lt_top {μ : Measure ℂ} (v : Lp ℂ 2 μ) :
    ∫⁻ x, ENNReal.ofReal (‖(v : ℂ → ℂ) x‖ ^ 2) ∂μ < ⊤ :=
  (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mp
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)).2

lemma memLp_comp_bilip (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) (v : L2 (f '' Ω)) :
    MemLp (fun x => (v : ℂ → ℂ) (f x)) 2 (volume.restrict Ω) := by
  refine memLp_two_of_lintegral ((Lp.aestronglyMeasurable v).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_restrict hg)) ?_
  have hK2 : 0 < (K : ℝ) ^ 2 := by positivity
  calc ∫⁻ x in Ω, ENNReal.ofReal (‖(v : ℂ → ℂ) (f x)‖ ^ 2)
      ≤ ∫⁻ x in Ω, ENNReal.ofReal ((K : ℝ) ^ 2) * (ENNReal.ofReal |(fderiv ℝ f x).det| *
          ENNReal.ofReal (‖(v : ℂ → ℂ) (f x)‖ ^ 2)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_inv_sq_le_abs_det hΩ hf hg] with x hx
        have h1 : 1 ≤ (K : ℝ) ^ 2 * |(fderiv ℝ f x).det| :=
          (inv_le_iff_one_le_mul₀' hK2).mp hx
        rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hK2.le, ← mul_assoc]
        exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (sq_nonneg _) h1)
    _ = ENNReal.ofReal ((K : ℝ) ^ 2) * ∫⁻ y in f '' Ω, ENNReal.ofReal (‖(v : ℂ → ℂ) y‖ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_image_bilip hΩ hf]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_sq_lt_top v)

lemma memLp_comp_symm_bilip (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) (u : L2 Ω) :
    MemLp (fun y => (u : ℂ → ℂ) (f.symm y)) 2 (volume.restrict (f '' Ω)) := by
  refine memLp_two_of_lintegral ((Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_symm_restrict hf)) ?_
  calc ∫⁻ y in f '' Ω, ENNReal.ofReal (‖(u : ℂ → ℂ) (f.symm y)‖ ^ 2)
      = ∫⁻ x in Ω, ENNReal.ofReal |(fderiv ℝ f x).det| *
          ENNReal.ofReal (‖(u : ℂ → ℂ) x‖ ^ 2) := by
        rw [lintegral_image_bilip hΩ hf]
        simp only [Homeomorph.symm_apply_apply]
    _ ≤ ∫⁻ x in Ω, ENNReal.ofReal ((K : ℝ) ^ 2) * ENNReal.ofReal (‖(u : ℂ → ℂ) x‖ ^ 2) := by
        refine setLIntegral_mono' hΩ.measurableSet fun x hx => ?_
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (abs_det_fderiv_le hΩ hf hx)) _
    _ = ENNReal.ofReal ((K : ℝ) ^ 2) * ∫⁻ x in Ω, ENNReal.ofReal (‖(u : ℂ → ℂ) x‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_sq_lt_top u)

/-- The pullback `L²(f(Ω)) ≃ L²(Ω)`, `v ↦ v ∘ f`, along a bi-Lipschitz homeomorphism. -/
def bilipPull (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) : L2 (f '' Ω) ≃ₗ[ℂ] L2 Ω where
  toFun v := (memLp_comp_bilip hΩ hK hf hg v).toLp _
  invFun u := (memLp_comp_symm_bilip hΩ hf u).toLp _
  map_add' v w := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_comp_bilip hΩ hK hf hg (v + w)),
      Lp.coeFn_add ((memLp_comp_bilip hΩ hK hf hg v).toLp _)
        ((memLp_comp_bilip hΩ hK hf hg w).toLp _),
      MemLp.coeFn_toLp (memLp_comp_bilip hΩ hK hf hg v),
      MemLp.coeFn_toLp (memLp_comp_bilip hΩ hK hf hg w),
      (quasiMeasurePreserving_restrict hg).ae (Lp.coeFn_add v w)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_comp_bilip hΩ hK hf hg (c • v)),
      Lp.coeFn_smul c ((memLp_comp_bilip hΩ hK hf hg v).toLp _),
      MemLp.coeFn_toLp (memLp_comp_bilip hΩ hK hf hg v),
      (quasiMeasurePreserving_restrict hg).ae (Lp.coeFn_smul c v)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply]
  left_inv v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_comp_symm_bilip hΩ hf
        ((memLp_comp_bilip hΩ hK hf hg v).toLp _)),
      (quasiMeasurePreserving_symm_restrict hf).ae
        (MemLp.coeFn_toLp (memLp_comp_bilip hΩ hK hf hg v))] with y h1 h2
    rw [h1, h2, Homeomorph.apply_symm_apply]
  right_inv u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_comp_bilip hΩ hK hf hg
        ((memLp_comp_symm_bilip hΩ hf u).toLp _)),
      (quasiMeasurePreserving_restrict hg).ae
        (MemLp.coeFn_toLp (memLp_comp_symm_bilip hΩ hf u))] with x h1 h2
    rw [h1, h2, Homeomorph.symm_apply_apply]

lemma bilipPull_ae (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) (v : L2 (f '' Ω)) :
    (bilipPull hΩ hK hf hg v : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun x => (v : ℂ → ℂ) (f x) :=
  MemLp.coeFn_toLp (memLp_comp_bilip hΩ hK hf hg v)

/-- The pullback carries the `L²(f(Ω))` inner product to the weighted inner product
`∫_Ω |det Df| ⟨·, ·⟩`. -/
lemma inner_eq_integral_bilipPull (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) (v w : L2 (f '' Ω)) :
    inner ℂ v w = ∫ x in Ω, ((|(fderiv ℝ f x).det| : ℝ) : ℂ) *
      inner ℂ ((bilipPull hΩ hK hf hg v : ℂ → ℂ) x) ((bilipPull hΩ hK hf hg w : ℂ → ℂ) x) := by
  rw [L2.inner_def, integral_image_bilip hΩ hf (fun y => inner ℂ ((v : ℂ → ℂ) y) ((w : ℂ → ℂ) y))]
  refine integral_congr_ae ?_
  filter_upwards [bilipPull_ae hΩ hK hf hg v, bilipPull_ae hΩ hK hf hg w] with x h1 h2
  rw [h1, h2, Complex.real_smul]

end PolyaNeumann

end
