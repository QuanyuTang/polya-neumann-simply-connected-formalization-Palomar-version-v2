module

public import RequestProject.Defs

/-!
# Functions with vanishing weak gradient are constant

On a domain (connected open set) `Ω ⊂ ℂ`, an `L²(Ω)` function whose weak gradient vanishes is
a.e. equal to a constant. This is the step of the Poincaré–Wirtinger inequality that identifies
the limit of a minimizing sequence.

The proof mollifies: for a smooth bump `ρ` of radius `ε`, the convolution `u ⋆ ρ` is smooth,
and its derivative at `x` is `-∫_Ω u ∂ψ` for the test function `ψ = ρ(x - ·)`, hence zero
whenever `B̄(x, ε) ⊆ Ω`. So `u ⋆ ρ` is constant on small balls, and by the Lebesgue
differentiation theorem `u ⋆ ρ_ε → u` a.e., so `u` is a.e. constant on small balls; a
connectedness argument concludes.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric

noncomputable section

namespace PolyaNeumann

/-- The extension by zero of an `L²(Ω)` function is locally integrable on `ℂ`. -/
lemma locallyIntegrable_indicator_L2 {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (u : L2 Ω) :
    LocallyIntegrable (Ω.indicator (fun z => u z)) volume :=
  ((memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp u)).locallyIntegrable one_le_two

/-- A real-linear map `ℂ → ℂ` vanishing at `1` and `i` vanishes. -/
lemma clm_eq_zero_of_one_I {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℂ →L[ℝ] E) (h1 : T 1 = 0) (hI : T Complex.I = 0) : T = 0 := by
  ext v
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul, h1, hI]
  simp

/-- The reflected, translated bump `t ↦ ρ(x - t)` as a complex test function. -/
def reflBump (φ : ContDiffBump (0 : ℂ)) (x : ℂ) : ℂ → ℂ :=
  fun t => ((φ.normed volume (x - t) : ℝ) : ℂ)

lemma reflBump_eq_zero (φ : ContDiffBump (0 : ℂ)) (x t : ℂ) (ht : t ∉ closedBall x φ.rOut) :
    reflBump φ x t = 0 := by
  have : x - t ∉ tsupport (φ.normed volume) := by
    rw [φ.tsupport_normed_eq]
    simpa [dist_comm, dist_eq_norm] using ht
  simp [reflBump, image_eq_zero_of_notMem_tsupport this]

lemma tsupport_reflBump_subset (φ : ContDiffBump (0 : ℂ)) (x : ℂ) :
    tsupport (reflBump φ x) ⊆ closedBall x φ.rOut := by
  refine closure_minimal (fun t ht => ?_) isClosed_closedBall
  by_contra h
  exact ht (reflBump_eq_zero φ x t h)

lemma testFunction_reflBump {Ω : Set ℂ} (φ : ContDiffBump (0 : ℂ)) (x : ℂ)
    (hx : closedBall x φ.rOut ⊆ Ω) : TestFunction Ω (reflBump φ x) := by
  refine ⟨?_, ?_, (tsupport_reflBump_subset φ x).trans hx⟩
  · exact Complex.ofRealCLM.contDiff.comp (φ.contDiff_normed.comp (contDiff_const.sub contDiff_id))
  · exact HasCompactSupport.intro (isCompact_closedBall x φ.rOut) (reflBump_eq_zero φ x)

lemma fderiv_reflBump (φ : ContDiffBump (0 : ℂ)) (x t v : ℂ) :
    fderiv ℝ (reflBump φ x) t v = -((fderiv ℝ (φ.normed volume) (x - t) v : ℝ) : ℂ) := by
  have hρ : HasFDerivAt (φ.normed volume) (fderiv ℝ (φ.normed volume) (x - t)) (x - t) :=
    ((φ.contDiff_normed (n := 1)).differentiable (by simp) _).hasFDerivAt
  have h := (Complex.ofRealCLM.hasFDerivAt).comp t (hρ.comp t ((hasFDerivAt_id t).const_sub x))
  have : reflBump φ x = Complex.ofRealCLM ∘ (φ.normed volume) ∘ (fun t => x - t) := rfl
  rw [this, h.fderiv]
  simp

/-- The derivative of the mollified function vanishes, tested in the coordinate directions. -/
lemma integral_fderiv_bump_smul_eq_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) (u : L2 Ω)
    (hu : IsWeakGradient Ω u 0) (φ : ContDiffBump (0 : ℂ)) (x : ℂ)
    (hx : closedBall x φ.rOut ⊆ Ω) (i : Fin 2) :
    ∫ t, fderiv ℝ (φ.normed volume) (x - t) (coordDir i) • Ω.indicator (fun z => u z) t = 0 := by
  have h := hu (reflBump φ x) (testFunction_reflBump φ x hx) i
  have h0 : ∫ w in Ω, (0 : Fin 2 → L2 Ω) i w * reflBump φ x w = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
    · simp
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w hw
      simp only [Pi.zero_apply]
      rw [hw]
      simp
  rw [h0, neg_zero] at h
  simp_rw [fderiv_reflBump] at h
  have e : ∀ t, fderiv ℝ (φ.normed volume) (x - t) (coordDir i) • Ω.indicator (fun z => u z) t =
      Ω.indicator (fun t => -(u t * -((fderiv ℝ (φ.normed volume) (x - t) (coordDir i) : ℝ) : ℂ))) t := by
    intro t
    by_cases ht : t ∈ Ω
    · simp [ht, Complex.real_smul, mul_comm]
    · simp [ht]
  simp_rw [e]
  rw [integral_indicator hΩ.measurableSet, integral_neg, h, neg_zero]

/-- The bilinear map `(f, s) ↦ s • f` used for mollification. -/
abbrev smulFlip : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip

/-- The mollification `u ⋆ ρ` has zero derivative at every `x` with `B̄(x, rOut) ⊆ Ω`. -/
lemma hasFDerivAt_mollify_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) (u : L2 Ω)
    (hu : IsWeakGradient Ω u 0) (φ : ContDiffBump (0 : ℂ)) (x : ℂ)
    (hx : closedBall x φ.rOut ⊆ Ω) :
    HasFDerivAt (convolution (Ω.indicator (fun z => u z)) (φ.normed volume) smulFlip volume)
      (0 : ℂ →L[ℝ] ℂ) x := by
  have hU := locallyIntegrable_indicator_L2 hΩ.measurableSet u
  have hd := HasCompactSupport.hasFDerivAt_convolution_right smulFlip
    (φ.hasCompactSupport_normed (μ := volume)) hU (φ.contDiff_normed (n := 1)) x
  convert hd using 1
  symm
  have hint : Integrable (fun t => ContinuousLinearMap.precompR ℂ smulFlip
      (Ω.indicator (fun z => u z) t) (fderiv ℝ (φ.normed volume) (x - t))) volume :=
    HasCompactSupport.convolutionExists_right (ContinuousLinearMap.precompR ℂ smulFlip)
      ((φ.hasCompactSupport_normed (μ := volume)).fderiv ℝ) hU
      ((φ.contDiff_normed (n := 1)).continuous_fderiv (by simp)) x
  have key : ∀ i : Fin 2, convolution (Ω.indicator (fun z => u z)) (fderiv ℝ (φ.normed volume))
      (ContinuousLinearMap.precompR ℂ smulFlip) volume x (coordDir i) = 0 := by
    intro i
    rw [convolution_def, ContinuousLinearMap.integral_apply hint]
    simpa using integral_fderiv_bump_smul_eq_zero hΩ u hu φ x hx i
  exact clm_eq_zero_of_one_I _ (by simpa [coordDir] using key 0) (by simpa [coordDir] using key 1)

/-- On every ball `B(x₀, r)` with `B̄(x₀, 2r) ⊆ Ω`, a function with zero weak gradient is a.e.
constant. -/
lemma ae_const_on_ball_of_weakGradient_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) (u : L2 Ω)
    (hu : IsWeakGradient Ω u 0) {x₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall x₀ (2 * r) ⊆ Ω) :
    ∃ c : ℂ, ∀ᵐ z ∂(volume.restrict (ball x₀ r)), u z = c := by
  set U := Ω.indicator (fun z => u z) with hUdef
  have hU := locallyIntegrable_indicator_L2 hΩ.measurableSet u
  have hε : ∀ n : ℕ, 0 < r / (n + 1) := fun n => by positivity
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨r / (n + 1) / 2, r / (n + 1), by linarith [hε n], by linarith [hε n]⟩
  have hεr : ∀ n : ℕ, r / (n + 1) ≤ r := fun n =>
    div_le_self hr.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  set conv := fun n => convolution U ((φ n).normed volume) smulFlip volume with hconv
  -- the mollifications are constant on `B(x₀, r)`
  have hconst : ∀ n, ∀ x ∈ ball x₀ r, conv n x = conv n x₀ := by
    intro n x hx
    have hsub : ∀ y ∈ ball x₀ r, closedBall y (φ n).rOut ⊆ Ω := by
      intro y hy z hz
      apply hsub
      have h1 : dist z y ≤ r / (n + 1) := hz
      have h2 : dist y x₀ < r := hy
      have := dist_triangle z y x₀
      show dist z x₀ ≤ 2 * r
      linarith [hεr n]
    have hd : ∀ y ∈ ball x₀ r, HasFDerivAt (conv n) (0 : ℂ →L[ℝ] ℂ) y := fun y hy =>
      hasFDerivAt_mollify_zero hΩ u hu (φ n) y (hsub y hy)
    exact isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball x₀ r).isPreconnected
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y hy).fderiv) hx (mem_ball_self hr)
  -- the mollifications converge a.e. to `U`
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => conv n x) atTop (𝓝 (U x)) := by
    have h0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, φ] using this
    have hK : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn :=
      Eventually.of_forall fun n => by simp only [φ]; linarith
    have := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable h0 hK hU
    filter_upwards [this] with x hx
    simpa [hconv, convolution_flip] using hx
  have hlim' : ∀ᵐ x ∂(volume.restrict (ball x₀ r)),
      Tendsto (fun n => conv n x₀) atTop (𝓝 (u x)) := by
    filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem measurableSet_ball] with x hx hxb
    have hxU : U x = u x := by
      rw [hUdef, Set.indicator_of_mem]
      exact hsub (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hxb)
    rw [← hxU]
    exact hx.congr fun n => hconst n x hxb
  haveI : (ae (volume.restrict (ball x₀ r))).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero]
    exact (isOpen_ball.measure_pos volume ⟨x₀, mem_ball_self hr⟩).ne'
  obtain ⟨x₁, hx₁⟩ := hlim'.exists
  refine ⟨u x₁, ?_⟩
  filter_upwards [hlim'] with x hx
  exact tendsto_nhds_unique hx hx₁

/-- Two a.e. constant values of a function on overlapping open sets agree. -/
lemma eq_of_ae_const_inter {f : ℂ → ℂ} {B B' : Set ℂ} (hB : IsOpen B) (hB' : IsOpen B')
    (hne : (B ∩ B').Nonempty) {c c' : ℂ} (h : ∀ᵐ z ∂(volume.restrict B), f z = c)
    (h' : ∀ᵐ z ∂(volume.restrict B'), f z = c') : c = c' := by
  by_contra hcc
  have h1 := ae_restrict_of_ae_restrict_of_subset (Set.inter_subset_left (s := B) (t := B')) h
  have h2 := ae_restrict_of_ae_restrict_of_subset (Set.inter_subset_right (s := B) (t := B')) h'
  have h3 : ∀ᵐ z ∂(volume.restrict (B ∩ B')), False := by
    filter_upwards [h1, h2] with z hz hz' using hcc (hz ▸ hz')
  rw [ae_iff, Measure.restrict_apply' (hB.inter hB').measurableSet] at h3
  simp only [not_false_eq_true, Set.setOf_true, Set.univ_inter] at h3
  exact ((hB.inter hB').measure_pos volume hne).ne' h3

/-- A function that is a.e. constant near every point of a domain is a.e. constant. -/
lemma ae_const_of_locally_ae_const {Ω : Set ℂ} (hΩ : IsDomain Ω) (f : ℂ → ℂ)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ball x r ⊆ Ω ∧ ∃ c : ℂ, ∀ᵐ z ∂(volume.restrict (ball x r)), f z = c) :
    ∃ c : ℂ, ∀ᵐ z ∂(volume.restrict Ω), f z = c := by
  obtain ⟨x₀, hx₀⟩ := hΩ.2.nonempty
  obtain ⟨r₀, hr₀, hb₀, c₀, hc₀⟩ := hloc x₀ hx₀
  have hopen : ∀ (P : Set ℂ → Prop), (∀ B B', B' ⊆ B → P B → P B') →
      IsOpen {x | ∃ r > 0, ball x r ⊆ Ω ∧ P (ball x r)} := by
    intro P hP
    rw [Metric.isOpen_iff]
    rintro x ⟨r, hr, hb, hPx⟩
    refine ⟨r, hr, fun y hy => ?_⟩
    have hs : 0 < r - dist y x := sub_pos.mpr (mem_ball.mp hy)
    have hsub : ball y (r - dist y x) ⊆ ball x r := ball_subset_ball' (by linarith)
    exact ⟨_, hs, hsub.trans hb, hP _ _ hsub hPx⟩
  set S := {x | ∃ r > 0, ball x r ⊆ Ω ∧ ∀ᵐ z ∂(volume.restrict (ball x r)), f z = c₀}
  set T := {x | ∃ r > 0, ball x r ⊆ Ω ∧
    ∃ c ≠ c₀, ∀ᵐ z ∂(volume.restrict (ball x r)), f z = c}
  have hS : IsOpen S := hopen (fun B => ∀ᵐ z ∂(volume.restrict B), f z = c₀)
    (fun B B' h hB => ae_restrict_of_ae_restrict_of_subset h hB)
  have hT : IsOpen T := hopen (fun B => ∃ c ≠ c₀, ∀ᵐ z ∂(volume.restrict B), f z = c)
    (fun B B' h ⟨c, hc, hB⟩ => ⟨c, hc, ae_restrict_of_ae_restrict_of_subset h hB⟩)
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro x ⟨r, hr, -, h1⟩ ⟨s, hs, -, c, hc, h2⟩
    exact hc (eq_of_ae_const_inter isOpen_ball isOpen_ball
      ⟨x, mem_ball_self hs, mem_ball_self hr⟩ h2 h1)
  have hcover : Ω ⊆ S ∪ T := by
    intro x hx
    obtain ⟨r, hr, hb, c, hc⟩ := hloc x hx
    by_cases h : c = c₀
    · exact Or.inl ⟨r, hr, hb, h ▸ hc⟩
    · exact Or.inr ⟨r, hr, hb, c, h, hc⟩
  have hΩS : Ω ⊆ S := IsPreconnected.subset_left_of_subset_union hS hT hdisj hcover
    ⟨x₀, hx₀, r₀, hr₀, hb₀, hc₀⟩ hΩ.2.isPreconnected
  have hΩS' : ∀ x ∈ Ω, ∃ r > 0, ball x r ⊆ Ω ∧
      ∀ᵐ z ∂(volume.restrict (ball x r)), f z = c₀ := hΩS
  choose! rad hrad hradb hradc using hΩS'
  obtain ⟨I, hIc, hI⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : Ω => ball (x : ℂ) (rad x)) (fun _ => isOpen_ball)
  have hΩeq : Ω = ⋃ x ∈ I, ball (x : ℂ) (rad x) := by
    rw [hI]
    apply subset_antisymm
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hrad x hx)⟩
    · exact Set.iUnion_subset fun x => hradb x x.2
  refine ⟨c₀, ?_⟩
  rw [hΩeq, ae_restrict_biUnion_iff _ hIc]
  exact fun x _ => hradc x x.2

/-- **Constancy lemma**: on a domain, an `L²` function whose weak gradient vanishes is a.e.
equal to a constant. -/
theorem ae_const_of_weakGradient_zero {Ω : Set ℂ} (hΩ : IsDomain Ω) (u : L2 Ω)
    (hu : IsWeakGradient Ω u 0) :
    ∃ c : ℂ, ∀ᵐ z ∂(volume.restrict Ω), u z = c := by
  refine ae_const_of_locally_ae_const hΩ _ fun x hx => ?_
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hΩ.1 x hx
  refine ⟨ε / 3, by positivity, (ball_subset_ball (by linarith)).trans hb, ?_⟩
  exact ae_const_on_ball_of_weakGradient_zero hΩ.1 u hu (by positivity)
    ((closedBall_subset_ball (by linarith)).trans hb)

end PolyaNeumann

end
