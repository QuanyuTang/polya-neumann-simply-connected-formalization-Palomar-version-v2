module

public import RequestProject.WeakConstancy

/-!
# Mollifier estimates for `H¹` functions

For `u ∈ L²(Ω)` with weak gradient `g`, extended by zero to `U : ℂ → ℂ`, and a probability
density `ρ` supported in `{‖z‖ ≤ R}`, the mollification `ρ ⋆ U` is close to `U` in `L²` on
every open set `W` from which all segments `t - s z` (`t ∈ W`, `z ∈ supp ρ`, `0 ≤ s ≤ 1`)
stay inside `Ω`:
`‖1_W (U - ρ ⋆ U)‖_{L²} ≤ R (‖g₀‖ + ‖g₁‖)`.

The proof is by duality: the pairing of `U - ρ ⋆ U` with a test function is computed with the
fundamental theorem of calculus along segments and the definition of the weak gradient, and an
`L²` function whose pairings with test functions supported in `W` are bounded by `C ‖φ‖` has
norm at most `C`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set
open scoped Manifold

noncomputable section

namespace PolyaNeumann

/-- The extension by zero of an element of `L²(Ω)` to a function on `ℂ`. -/
def extZero (Ω : Set ℂ) (u : L2 Ω) : ℂ → ℂ := Ω.indicator (fun z => u z)

/-- Mollification `(ρ ⋆ U)(x) = ∫ ρ(z) U(x - z) dz`. -/
def mollify (ρ : ℂ → ℝ) (U : ℂ → ℂ) : ℂ → ℂ :=
  convolution ρ U (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The `L²(ℂ)` norm of a function, as a real number. -/
def l2norm (f : ℂ → ℂ) : ℝ := (eLpNorm f 2 volume).toReal

lemma memLp_extZero {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (u : L2 Ω) :
    MemLp (extZero Ω u) 2 volume :=
  (memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp u)

/-- Cauchy–Schwarz for `∫_Ω g ψ`. -/
lemma norm_setIntegral_mul_le {Ω : Set ℂ} (g : L2 Ω) {ψ : ℂ → ℂ} (hψ : MemLp ψ 2 volume) :
    ‖∫ w in Ω, g w * ψ w‖ ≤ ‖g‖ * l2norm ψ := by
  have hψ' : MemLp (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω) :=
    (hψ.restrict Ω).star
  set Ψ : L2 Ω := hψ'.toLp _
  have key : ∫ w in Ω, g w * ψ w = inner ℂ Ψ g := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ'.coeFn_toLp] with w hw
    simp only [Ψ, hw, RCLike.inner_apply, Complex.conj_conj, mul_comm]
  rw [key]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [mul_comm]
  gcongr
  rw [Lp.norm_toLp, l2norm]
  refine ENNReal.toReal_mono (hψ.eLpNorm_ne_top) ?_
  calc eLpNorm (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω)
      = eLpNorm ψ 2 (volume.restrict Ω) := by
        refine eLpNorm_congr_norm_ae hψ'.aestronglyMeasurable
          hψ.aestronglyMeasurable.restrict ?_
        filter_upwards with w; simp
    _ ≤ eLpNorm ψ 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self

/-- The weak gradient identity, in an arbitrary direction `v`. -/
lemma integral_extZero_mul_fderiv {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) {ψ : ℂ → ℂ} (hψ : TestFunction Ω ψ) (v : ℂ) :
    ∫ t, extZero Ω u t * fderiv ℝ ψ t v =
      -((v.re : ℂ) * (∫ w in Ω, g 0 w * ψ w) + (v.im : ℂ) * ∫ w in Ω, g 1 w * ψ w) := by
  set A : Fin 2 → ℂ → ℂ := fun i t => extZero Ω u t * fderiv ℝ ψ t (coordDir i)
  have hv : (fun t => extZero Ω u t * fderiv ℝ ψ t v) =
      fun t => (v.re : ℂ) * A 0 t + (v.im : ℂ) * A 1 t := by
    ext t
    have : v = v.re • (1 : ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul]
    simp only [A, coordDir, Complex.real_smul]
    simp; ring
  have hU : LocallyIntegrable (extZero Ω u) volume :=
    locallyIntegrable_indicator_L2 hΩ.measurableSet u
  have hint : ∀ i, Integrable (A i) := by
    intro i
    have hs : HasCompactSupport fun t => fderiv ℝ ψ t (coordDir i) :=
      (hψ.2.1.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T (coordDir i)) rfl
    exact hU.integrable_smul_right_of_hasCompactSupport
      ((hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const) hs
  have hI : ∀ i, ∫ t, A i t = -∫ w in Ω, g i w * ψ w := by
    intro i
    rw [← hg ψ hψ i]
    rw [← integral_indicator hΩ.measurableSet]
    congr 1; ext t
    by_cases ht : t ∈ Ω <;> simp [A, extZero, ht]
  rw [hv, integral_add ((hint 0).const_mul _) ((hint 1).const_mul _), integral_const_mul,
    integral_const_mul, hI, hI]
  ring

lemma testFunction_translate {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ) (a : ℂ) (ha : ∀ t ∈ tsupport φ, t - a ∈ Ω) :
    TestFunction Ω (fun t => φ (t + a)) := by
  refine ⟨hφ.comp (contDiff_id.add contDiff_const), ?_, ?_⟩
  · exact hφs.comp_homeomorph (Homeomorph.addRight a)
  · intro t ht
    have : t + a ∈ tsupport φ := by
      have h := tsupport_comp_subset_preimage φ (f := fun t => t + a) ((continuous_id.add continuous_const : Continuous fun x => x + a))
      exact h ht
    simpa using ha _ this

lemma l2norm_translate {φ : ℂ → ℂ} (hφ : AEStronglyMeasurable φ volume) (a : ℂ) :
    l2norm (fun t => φ (t + a)) = l2norm φ := by
  unfold l2norm
  congr 1
  exact eLpNorm_comp_measurePreserving hφ (measurePreserving_add_right volume a)

/-- **Pairing with a translation difference.** If every segment from `tsupport φ` in the
direction `-z` of length `‖z‖` stays in `Ω`, then
`|∫ U(t) (φ(t+z) - φ(t)) dt| ≤ ‖z‖ (‖g₀‖ + ‖g₁‖) ‖φ‖₂`. -/
theorem pairing_translate_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ) (z : ℂ)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ tsupport φ, t - s • z ∈ Ω) :
    ‖∫ t, extZero Ω u t * (φ (t + z) - φ t)‖ ≤ ‖z‖ * (‖g 0‖ + ‖g 1‖) * l2norm φ := by
  set D : ℂ → ℝ → ℂ := fun t s => fderiv ℝ φ (t + s • z) z with hD
  have hDc : Continuous (fun p : ℂ × ℝ => D p.1 p.2) :=
    ((hφ.continuous_fderiv (by simp)).comp (continuous_fst.add
      (continuous_snd.smul continuous_const))).clm_apply continuous_const
  -- fundamental theorem of calculus along the segment
  have hftc : ∀ t, φ (t + z) - φ t = ∫ s in (0 : ℝ)..1, D t s := by
    intro t
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => φ (t + s • z)) (D t s) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => t + s • z) z s := by
        simpa using ((hasDerivAt_id s).smul_const z).const_add t
      exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s h1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hDc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    simp
  -- the inner integrals, by the weak gradient identity
  set B := ‖z‖ * (‖g 0‖ + ‖g 1‖) * l2norm φ
  have hinner : ∀ s ∈ Icc (0 : ℝ) 1, ‖∫ t, extZero Ω u t * D t s‖ ≤ B := by
    intro s hs
    have hψ := testFunction_translate hφ hφs (s • z) (hseg s hs)
    have hfd : ∀ t, fderiv ℝ (fun t => φ (t + s • z)) t = fderiv ℝ φ (t + s • z) := by
      intro t
      exact fderiv_comp_add_right _
    have := integral_extZero_mul_fderiv hΩ hg hψ z
    simp only [hfd] at this
    rw [show (fun t => extZero Ω u t * D t s) = fun t => extZero Ω u t * fderiv ℝ φ (t + s • z) z
      from rfl, this, norm_neg]
    have hmem : MemLp (fun t => φ (t + s • z)) 2 volume :=
      (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1)
    have hn : l2norm (fun t => φ (t + s • z)) = l2norm φ :=
      l2norm_translate hφ.continuous.aestronglyMeasurable _
    have h0 := norm_setIntegral_mul_le (g 0) hmem
    have h1 := norm_setIntegral_mul_le (g 1) hmem
    rw [hn] at h0 h1
    have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hl : 0 ≤ l2norm φ := ENNReal.toReal_nonneg
    calc _ ≤ ‖(z.re : ℂ) * ∫ w in Ω, g 0 w * φ (w + s • z)‖ +
          ‖(z.im : ℂ) * ∫ w in Ω, g 1 w * φ (w + s • z)‖ := norm_add_le _ _
      _ ≤ |z.re| * (‖g 0‖ * l2norm φ) + |z.im| * (‖g 1‖ * l2norm φ) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
          gcongr
      _ ≤ ‖z‖ * (‖g 0‖ * l2norm φ) + ‖z‖ * (‖g 1‖ * l2norm φ) := by gcongr
      _ = _ := by ring
  -- Fubini
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hU : LocallyIntegrable (extZero Ω u) volume :=
    locallyIntegrable_indicator_L2 hΩ.measurableSet u
  set L : Set ℂ := (fun p : ℂ × ℝ => p.1 - p.2 • z) '' (tsupport φ ×ˢ Icc 0 1)
  have hL : IsCompact L := (hφs.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨M, hM⟩ := (hφs.fderiv ℝ).exists_bound_of_continuous (hφ.continuous_fderiv (by simp))
  have hDb : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖D t s‖ ≤ M * ‖z‖ * ‖L.indicator (fun _ => (1 : ℝ)) t‖ := by
    intro t s hs
    by_cases ht : t ∈ L
    · simp only [ht, indicator_of_mem, norm_one, mul_one]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hM _)
    · have : t + s • z ∉ tsupport (fderiv ℝ φ) := by
        intro h
        exact ht ⟨(t + s • z, s), ⟨tsupport_fderiv_subset ℝ h, hs⟩, by simp⟩
      simp only [D]
      rw [image_eq_zero_of_notMem_tsupport this]; simp [ht]
  have hint : Integrable (fun p : ℂ × ℝ => extZero Ω u p.1 * D p.1 p.2) (volume.prod ν) := by
    have hLU : Integrable (fun t => M * ‖z‖ * ‖L.indicator (extZero Ω u) t‖) :=
      (((integrable_indicator_iff hL.measurableSet).mpr
        (hU.integrableOn_isCompact hL)).norm.const_mul _)
    refine (hLU.comp_fst ν).mono' ?_ ?_
    · exact ((hU.aestronglyMeasurable.comp_fst (ν := ν)).mul hDc.aestronglyMeasurable)
    · have hae : ∀ᵐ p ∂((volume : Measure ℂ).prod ν), p.2 ∈ Ioc (0 : ℝ) 1 := by
        rw [ae_iff]
        have : {p : ℂ × ℝ | p.2 ∉ Ioc (0 : ℝ) 1} = univ ×ˢ (Ioc (0 : ℝ) 1)ᶜ := by ext; simp
        rw [this, Measure.prod_prod]
        simp [ν]
      filter_upwards [hae] with p hp
      have := hDb p.1 p.2 (Ioc_subset_Icc_self hp)
      by_cases ht : p.1 ∈ L
      · simp only [ht, indicator_of_mem, norm_mul] at this ⊢
        simp only [norm_one, mul_one] at this
        calc ‖extZero Ω u p.1‖ * ‖D p.1 p.2‖ ≤ ‖extZero Ω u p.1‖ * (M * ‖z‖) := by gcongr
          _ = _ := by ring
      · simp only [ht, not_false_eq_true, indicator_of_notMem, norm_zero, mul_zero] at this ⊢
        simp [norm_le_zero_iff.mp this]
  have hswap : ∫ t, extZero Ω u t * (φ (t + z) - φ t) =
      ∫ s in Ioc (0 : ℝ) 1, ∫ t, extZero Ω u t * D t s := by
    simp_rw [hftc, intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
    exact integral_integral_swap hint
  rw [hswap]
  calc ‖∫ s in Ioc (0 : ℝ) 1, ∫ t, extZero Ω u t * D t s‖ ≤
        B * (volume (Ioc (0 : ℝ) 1)).toReal :=
        norm_setIntegral_le_of_norm_le_const (by simp)
          fun s hs => hinner s (Ioc_subset_Icc_self hs)
    _ = B := by simp

/-- **Pairing with a mollification difference.** -/
theorem pairing_mollify_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ) {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : ∫ z, ρ z = 1) {R : ℝ} (hR : ∀ z ∈ tsupport ρ, ‖z‖ ≤ R)
    (hseg : ∀ z ∈ tsupport ρ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ tsupport φ, t - s • z ∈ Ω) :
    ‖∫ t, (extZero Ω u t - mollify ρ (extZero Ω u) t) * φ t‖ ≤
      R * (‖g 0‖ + ‖g 1‖) * l2norm φ := by
  set U := extZero Ω u
  have hU : LocallyIntegrable U volume := locallyIntegrable_indicator_L2 hΩ.measurableSet u
  set C := (‖g 0‖ + ‖g 1‖) * l2norm φ
  have hC : 0 ≤ C := by unfold C l2norm; positivity
  have hmc : Continuous (mollify ρ U) :=
    hρs.continuous_convolution_left _ hρc hU
  have hUφ : Integrable (fun t => U t * φ t) :=
    hU.integrable_smul_right_of_hasCompactSupport hφ.continuous hφs
  have hmφ : Integrable (fun t => mollify ρ U t * φ t) :=
    (hmc.mul hφ.continuous).integrable_of_hasCompactSupport (hφs.mul_left)
  have hUφz : ∀ z, Integrable (fun t => U t * φ (t + z)) := fun z =>
    hU.integrable_smul_right_of_hasCompactSupport (hφ.continuous.comp ((continuous_id.add continuous_const : Continuous fun x => x + z)))
      (hφs.comp_homeomorph (Homeomorph.addRight z))
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  -- Fubini
  set L' : Set ℂ := (fun p : ℂ × ℂ => p.1 - p.2) '' (tsupport φ ×ˢ tsupport ρ)
  have hL' : IsCompact L' := (hφs.prod hρs).image (by fun_prop)
  set F : ℂ → ℂ → ℂ := fun x z => ρ z • U (x - z) * φ x with hF
  have hFeq : ∀ x z, F x z = ρ z • L'.indicator U (x - z) * φ x := by
    intro x z
    by_cases hz : z ∈ tsupport ρ
    · by_cases hx : x ∈ tsupport φ
      · have : x - z ∈ L' := ⟨(x, z), ⟨hx, hz⟩, rfl⟩
        simp [F, this]
      · simp [F, image_eq_zero_of_notMem_tsupport hx]
    · simp [F, image_eq_zero_of_notMem_tsupport hz]
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have h1 := Integrable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure ℂ)) (ν := volume) hρi
      ((integrable_indicator_iff hL'.measurableSet).mpr (hU.integrableOn_isCompact hL'))
    obtain ⟨Mφ, hMφ⟩ := hφs.exists_bound_of_continuous hφ.continuous
    have h2 := h1.mul_bdd (c := Mφ) (g := fun p : ℂ × ℂ => φ p.1)
      (hφ.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hMφ p.1)
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, hFeq]
  have hG : ∀ z, ∫ x, F x z = ρ z • ∫ t, U t * φ (t + z) := by
    intro z
    simp only [hF]
    simp_rw [smul_mul_assoc]
    rw [integral_smul]
    congr 1
    have := integral_sub_right_eq_self (μ := volume) (fun x => U x * φ (x + z)) z
    simpa using this
  have hGi : Integrable (fun z => ρ z • ∫ t, U t * φ (t + z)) := by
    have := hFint.integral_prod_right
    refine this.congr (Eventually.of_forall fun z => ?_)
    simpa [Function.uncurry] using hG z
  have hm : ∫ x, mollify ρ U x * φ x = ∫ z, ρ z • ∫ t, U t * φ (t + z) := by
    have h1 : ∀ x, mollify ρ U x * φ x = ∫ z, F x z := by
      intro x
      simp only [mollify, convolution_def, hF, ContinuousLinearMap.lsmul_apply]
      rw [integral_mul_const]
    simp_rw [h1]
    rw [integral_integral_swap hFint]
    exact integral_congr_ae (Eventually.of_forall hG)
  have hu : ∫ t, U t * φ t = ∫ z, ρ z • ∫ t, U t * φ t := by
    rw [integral_smul_const, hρ1, one_smul]
  have hdiff : ∫ t, (U t - mollify ρ U t) * φ t =
      -∫ z, ρ z • ∫ t, U t * (φ (t + z) - φ t) := by
    simp_rw [sub_mul]
    rw [integral_sub hUφ hmφ, hm, hu, ← integral_sub (hρi.smul_const _) hGi, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [mul_sub]
    rw [integral_sub (hUφz z) hUφ, smul_sub, ← smul_sub]
    simp only [smul_sub, neg_sub]
  rw [hdiff, norm_neg]
  calc ‖∫ z, ρ z • ∫ t, U t * (φ (t + z) - φ t)‖ ≤ ∫ z, ρ z * (R * C) := by
        refine norm_integral_le_of_norm_le (hρi.mul_const _) (Eventually.of_forall fun z => ?_)
        rw [norm_smul, Real.norm_of_nonneg (hρ0 z)]
        by_cases hz : z ∈ tsupport ρ
        · gcongr
          · exact hρ0 z
          refine (pairing_translate_le hΩ hg hφ hφs z
            (fun s hs t ht => hseg z hz s hs t ht)).trans ?_
          rw [mul_assoc]
          gcongr
          exact hR z hz
        · simp [image_eq_zero_of_notMem_tsupport hz]
    _ = R * (‖g 0‖ + ‖g 1‖) * l2norm φ := by
        rw [integral_mul_const, hρ1, one_mul, mul_assoc]

lemma l2norm_nonneg (f : ℂ → ℂ) : 0 ≤ l2norm f := ENNReal.toReal_nonneg

/-- Cauchy–Schwarz for `∫ A B` on `ℂ`. -/
lemma norm_integral_mul_le_l2 {A B : ℂ → ℂ} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume) :
    ‖∫ x, A x * B x‖ ≤ l2norm A * l2norm B := by
  have hA' : MemLp (fun x => (starRingEnd ℂ) (A x)) 2 volume := hA.star
  have key : ∫ x, A x * B x = inner ℂ (hA'.toLp _) (hB.toLp _) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hA'.coeFn_toLp, hB.coeFn_toLp] with x h1 h2
    simp only [h1, h2, RCLike.inner_apply, Complex.conj_conj, mul_comm]
  rw [key]
  refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [Lp.norm_toLp, Lp.norm_toLp, l2norm, l2norm]
  congr 2
  refine eLpNorm_congr_norm_ae hA'.aestronglyMeasurable hA.aestronglyMeasurable ?_
  filter_upwards with w; simp

lemma l2norm_mono {f g : ℂ → ℂ} (hg : MemLp g 2 volume) (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    l2norm f ≤ l2norm g := by
  by_cases hf : AEStronglyMeasurable f volume
  · exact ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono hf h)
  · unfold l2norm
    rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.toReal_top]
    exact ENNReal.toReal_nonneg

lemma l2norm_add_le {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2norm (f + g) ≤ l2norm f + l2norm g := by
  unfold l2norm
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (by norm_num))

/-- Duality on a compact subset. -/
lemma l2norm_indicator_le_of_pairing {W K : Set ℂ} (hW : IsOpen W) (hK : IsCompact K)
    (hKW : K ⊆ W) {F : ℂ → ℂ} (hF : MemLp F 2 volume) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ‖∫ x, F x * φ x‖ ≤ C * l2norm φ) :
    l2norm (K.indicator F) ≤ C := by
  -- a smooth cutoff
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ, ℂ))
    (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := δ) (E := K)) hK.isClosed (self_subset_thickening hδ K)
  have hχ' : ContDiff ℝ (⊤ : ℕ∞) χ := contMDiff_iff_contDiff.mp hχ
  have hχt : tsupport χ ⊆ cthickening δ K := by
    rw [tsupport, hχs]; exact closure_thickening_subset_cthickening δ K
  have hχb : ∀ x, ‖(χ x : ℂ)‖ ≤ 1 := fun x => by
    have := hχr (mem_range_self x)
    rw [Complex.norm_real, Real.norm_of_nonneg this.1]; exact this.2
  have hχm : AEStronglyMeasurable (fun x => (χ x : ℂ)) volume :=
    (Complex.continuous_ofReal.comp hχ'.continuous).aestronglyMeasurable
  set FK := K.indicator F
  have hFK : MemLp FK 2 volume := hF.indicator hK.measurableSet
  set H : ℂ → ℂ := fun x => (starRingEnd ℂ) (FK x)
  have hH : MemLp H 2 volume := hFK.star
  set a := l2norm FK
  have hHa : l2norm H = a := by
    unfold l2norm; congr 1
    refine eLpNorm_congr_norm_ae hH.aestronglyMeasurable hFK.aestronglyMeasurable ?_
    filter_upwards with w; simp [H]
  -- key identity `∫ F χ conj(1_K F) = ‖1_K F‖²`
  have hkey : ∫ x, F x * ((χ x : ℂ) * H x) = (a ^ 2 : ℝ) := by
    have h1 : ∀ x, F x * ((χ x : ℂ) * H x) = ((‖FK x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      by_cases hx : x ∈ K
      · have : χ x = 1 := (hχ1 x).mp hx
        simp only [H, FK, indicator_of_mem hx, this, Complex.ofReal_one, one_mul]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp [H, FK, hx]
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    have := hFK.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at this
    have hnn : 0 ≤ ∫ x, ‖FK x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
    rw [show a = (eLpNorm FK 2 volume).toReal from rfl, this, ENNReal.toReal_ofReal (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  have hineq : ∀ ε > 0, a ^ 2 ≤ C * (a + ε) + l2norm F * ε := by
    intro ε hε
    obtain ⟨g, hgc, hgs, hgε⟩ := hH.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε
    have hg : MemLp g 2 volume := hgs.continuous.memLp_of_hasCompactSupport hgc
    have hgH : l2norm (g - H) ≤ ε := by
      unfold l2norm
      rw [← eLpNorm_neg, neg_sub]
      exact ENNReal.toReal_le_of_le_ofReal hε.le hgε
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x => (χ x : ℂ) * g x) :=
      (Complex.ofRealCLM.contDiff.comp hχ').mul hgs
    have hφs : HasCompactSupport (fun x => (χ x : ℂ) * g x) := hgc.mul_left
    have hφW : tsupport (fun x => (χ x : ℂ) * g x) ⊆ W := by
      refine (tsupport_mul_subset_left (f := fun x => (χ x : ℂ))).trans ?_
      refine (closure_mono ?_).trans (hχt.trans hδW)
      intro x hx; simpa using hx
    have h1 := h _ hφ hφs hφW
    have hφn : l2norm (fun x => (χ x : ℂ) * g x) ≤ a + ε := by
      calc l2norm (fun x => (χ x : ℂ) * g x) ≤ l2norm g := l2norm_mono hg fun x => by
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (hχb x)
        _ = l2norm (H + (g - H)) := by congr 1; abel
        _ ≤ l2norm H + l2norm (g - H) := l2norm_add_le hH (hg.sub hH)
        _ ≤ a + ε := by rw [hHa]; gcongr
    have hm : MemLp (fun x => (χ x : ℂ) * (g - H) x) 2 volume := by
      refine MemLp.of_le (hg.sub hH) (hχm.mul (hg.sub hH).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hχb x)
    have hrest : ‖∫ x, F x * ((χ x : ℂ) * (g - H) x)‖ ≤ l2norm F * ε := by
      refine (norm_integral_mul_le_l2 hF hm).trans ?_
      gcongr
      · exact l2norm_nonneg _
      refine (l2norm_mono (hg.sub hH) fun x => ?_).trans hgH
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hχb x)
    have hint : ∀ {B : ℂ → ℂ}, MemLp B 2 volume → Integrable (fun x => F x * B x) :=
      fun hB => hF.integrable_mul hB
    have hsplit : ∫ x, F x * ((χ x : ℂ) * H x) = (∫ x, F x * ((χ x : ℂ) * g x)) -
        ∫ x, F x * ((χ x : ℂ) * (g - H) x) := by
      rw [← integral_sub (hint (hφ.continuous.memLp_of_hasCompactSupport hφs)) (hint hm)]
      congr 1; ext x; simp only [Pi.sub_apply]; ring
    have : a ^ 2 = ‖∫ x, F x * ((χ x : ℂ) * H x)‖ := by
      rw [hkey, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    rw [this, hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add h1 hrest).trans ?_)
    gcongr
  have ha : 0 ≤ a := l2norm_nonneg _
  have ha2 : a ^ 2 ≤ C * a := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hF0 := l2norm_nonneg F
    set δ := ε / (2 * (C + l2norm F + 1))
    have hδ : 0 < δ := by positivity
    have := hineq δ hδ
    have : C * δ + l2norm F * δ < ε := by
      have : (C + l2norm F) * δ < ε := by
        rw [show δ = ε / (2 * (C + l2norm F + 1)) from rfl, mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    nlinarith
  nlinarith

lemma eLpNorm_indicator_eq_withDensity {F : ℂ → ℂ} (hF : AEStronglyMeasurable F volume)
    {A : Set ℂ} (hA : MeasurableSet A) :
    eLpNorm (A.indicator F) 2 volume =
      (volume.withDensity (fun x => ‖F x‖ₑ ^ (2 : ℝ)) A) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hF.indicator hA),
    withDensity_apply _ hA,
    ← lintegral_indicator hA]
  congr 2
  ext x
  by_cases hx : x ∈ A <;> simp [hx]

/-- Passing from compact subsets of `W` to `W`. -/
lemma l2norm_le_of_compact {W : Set ℂ} (hW : IsOpen W) {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (hFW : ∀ x ∉ W, F x = 0) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ K, IsCompact K → K ⊆ W → l2norm (K.indicator F) ≤ C) : l2norm F ≤ C := by
  obtain ⟨S, hSc, hSW, hSU, hSm⟩ := hW.exists_iUnion_isClosed
  set K : ℕ → Set ℂ := fun n => S n ∩ closedBall 0 n
  have hKc : ∀ n, IsCompact (K n) := fun n => (isCompact_closedBall 0 (n : ℝ)).inter_left (hSc n)
  have hKm : Monotone K := fun a b hab => inter_subset_inter (hSm hab)
    (closedBall_subset_closedBall (by exact_mod_cast hab))
  have hKU : ⋃ n, K n = W := by
    apply subset_antisymm
    · exact iUnion_subset fun n => inter_subset_left.trans (hSW n)
    · intro x hx
      rw [← hSU] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
      refine mem_iUnion.mpr ⟨max n m, hSm (le_max_left n m) hn, ?_⟩
      simp only [mem_closedBall, dist_zero_right]
      exact hm.trans (by exact_mod_cast le_max_right n m)
  set ν := volume.withDensity (fun x => ‖F x‖ₑ ^ (2 : ℝ))
  have hFeq : F = W.indicator F := by
    ext x; by_cases hx : x ∈ W <;> simp [hx, hFW]
  have hbound : ∀ n, ν (K n) ≤ ENNReal.ofReal C ^ (2 : ℝ) := by
    intro n
    have h1 := h (K n) (hKc n) (by rw [← hKU]; exact subset_iUnion K n)
    have h2 := eLpNorm_indicator_eq_withDensity hF.aestronglyMeasurable (hKc n).measurableSet
    have hfin : eLpNorm ((K n).indicator F) 2 volume ≠ ⊤ :=
      (hF.indicator (hKc n).measurableSet).eLpNorm_ne_top
    have h3 : eLpNorm ((K n).indicator F) 2 volume ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal h1
    rw [h2] at h3
    have := ENNReal.rpow_le_rpow h3 (by norm_num : (0 : ℝ) ≤ 2)
    rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at this
  have hW' : ν W ≤ ENNReal.ofReal C ^ (2 : ℝ) := by
    rw [← hKU]
    exact le_of_tendsto' (tendsto_measure_iUnion_atTop hKm) hbound
  unfold l2norm
  rw [hFeq, eLpNorm_indicator_eq_withDensity hF.aestronglyMeasurable hW.measurableSet]
  have := ENNReal.rpow_le_rpow hW' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at this
  exact ENNReal.toReal_le_of_le_ofReal hC this

/-- **Duality.** An `L²` function vanishing outside an open set `W`, whose pairings with smooth
compactly supported functions supported in `W` are bounded by `C ‖φ‖₂`, has `L²` norm at
most `C`. -/
theorem l2norm_le_of_pairing {W : Set ℂ} (hW : IsOpen W) {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (hFW : ∀ x ∉ W, F x = 0) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ‖∫ x, F x * φ x‖ ≤ C * l2norm φ) :
    l2norm F ≤ C :=
  l2norm_le_of_compact hW hF hFW hC fun _ hK hKW =>
    l2norm_indicator_le_of_pairing hW hK hKW hF hC h

lemma memLp_indicator_of_continuous {W : Set ℂ} (hW : MeasurableSet W)
    (hWb : Bornology.IsBounded W) {f : ℂ → ℂ} (hf : Continuous f) :
    MemLp (W.indicator f) 2 volume := by
  obtain ⟨M, hM⟩ := hWb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  rw [memLp_indicator_iff_restrict hW]
  haveI : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.mpr hWb.measure_lt_top.ne
  refine MemLp.of_bound hf.aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem hW] with x hx
  exact hM x (subset_closure hx)

/-- **Mollifier estimate.** If all segments `t - s z` (`t ∈ W`, `z ∈ supp ρ`, `s ∈ [0,1]`) stay
in `Ω`, then `‖1_W (U - ρ ⋆ U)‖₂ ≤ R (‖g₀‖ + ‖g₁‖)`. -/
theorem l2norm_indicator_sub_mollify_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω}
    {g : Fin 2 → L2 Ω} (hg : IsWeakGradient Ω u g) {W : Set ℂ} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : ∫ z, ρ z = 1) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ z ∈ tsupport ρ, ‖z‖ ≤ R)
    (hseg : ∀ t ∈ W, ∀ z ∈ tsupport ρ, ∀ s ∈ Icc (0 : ℝ) 1, t - s • z ∈ Ω) :
    MemLp (W.indicator fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) 2 volume ∧
    l2norm (W.indicator fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) ≤
      R * (‖g 0‖ + ‖g 1‖) := by
  have hU : LocallyIntegrable (extZero Ω u) volume :=
    locallyIntegrable_indicator_L2 hΩ.measurableSet u
  have hmc : Continuous (mollify ρ (extZero Ω u)) :=
    hρs.continuous_convolution_left _ hρc hU
  have hmem : MemLp (W.indicator fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) 2 volume := by
    rw [show (fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) =
      extZero Ω u - mollify ρ (extZero Ω u) from rfl, indicator_sub']
    exact ((memLp_extZero hΩ.measurableSet u).indicator hW.measurableSet).sub
      (memLp_indicator_of_continuous hW.measurableSet hWb hmc)
  refine ⟨hmem, l2norm_le_of_pairing hW hmem (fun x hx => by simp [hx]) (by positivity) ?_⟩
  intro φ hφ hφs hφW
  have heq : ∫ x, (W.indicator fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) x * φ x =
      ∫ x, (extZero Ω u x - mollify ρ (extZero Ω u) x) * φ x := by
    congr 1; ext x
    by_cases hx : x ∈ W
    · simp [hx]
    · have : x ∉ tsupport φ := fun h => hx (hφW h)
      simp [image_eq_zero_of_notMem_tsupport this]
  rw [heq]
  exact pairing_mollify_le hΩ hg hφ hφs hρc hρs hρ0 hρ1 hR
    (fun z hz s hs t ht => hseg t (hφW ht) z hz s hs)

end PolyaNeumann

end
