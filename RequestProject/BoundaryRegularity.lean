module

public import RequestProject.BoundaryChart
public import RequestProject.ArcLength
public import RequestProject.SmoothDomain
public import RequestProject.ReconChordArc

/-!
# Regularity of the constant-speed boundary parametrization of a smooth domain

For a smooth domain `Ω`, a boundary parametrization `γ` in the sense of `IsBoundaryParam`
(Lipschitz, `2π`-periodic, injective on `[0, 2π)`, onto `∂Ω`, with constant speed a.e.) is
`C^{1,1}`: `γ` is differentiable everywhere and `γ'` is Lipschitz on `[0, 2π]`
(`IsBoundaryParam.deriv_lipschitz`). This is the regularity hypothesis on the curve used in the
fractional regularity of the corrected kernel (Lemma 6.6).

In a smooth chart `w = p + c̄ (x + i f(x))` the abscissa `X(θ) = Re(c(γ(θ) - p))` is Lipschitz and
strictly monotone (`γ` is injective), so the constant speed gives
`γ'(θ) = Φ(X(θ))` almost everywhere, with the smooth field
`Φ(x) = c̄ (1 + i f'(x)) σ c₀ / √(1 + f'(x)²)` (`σ = ±1` the orientation). Since `γ` is the integral
of its derivative, `γ' = Φ ∘ X` everywhere, which is Lipschitz.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- **Lipschitz on a compact interval from local Lipschitz bounds** (for a bounded function). -/
lemma lipschitzOn_Icc_of_local {g : ℝ → ℂ} {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) {a b : ℝ}
    (hloc : ∀ x ∈ Icc a b, ∃ ε > 0, ∃ M : ℝ, ∀ y ∈ Ioo (x - ε) (x + ε),
      ∀ z ∈ Ioo (x - ε) (x + ε), ‖g y - g z‖ ≤ M * |y - z|) :
    ∃ M : ℝ, ∀ y ∈ Icc a b, ∀ z ∈ Icc a b, ‖g y - g z‖ ≤ M * |y - z| := by
  choose! ε hε M hM using hloc
  obtain ⟨t, htcov⟩ := (isCompact_Icc (a := a) (b := b)).elim_finite_subcover
    (fun x : Icc a b => ball (x : ℝ) (ε x)) (fun _ => isOpen_ball)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hε y hy)⟩)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := a) (b := b))
    (c := fun i : t => ball ((i : Icc a b) : ℝ) (ε i)) (fun _ => isOpen_ball)
    (by
      intro y hy
      have := htcov hy
      simp only [mem_iUnion] at this ⊢
      obtain ⟨i, hi, hyi⟩ := this
      exact ⟨⟨i, hi⟩, hyi⟩)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a)
  refine ⟨(∑ i ∈ t, |M i|) + 2 * B / δ, fun y hy z hz => ?_⟩
  by_cases hyz : |y - z| < δ
  · obtain ⟨i, hi⟩ := hleb y hy
    have hyi : y ∈ ball ((i : Icc a b) : ℝ) (ε i) := hi (mem_ball_self hδ)
    have hzi : z ∈ ball ((i : Icc a b) : ℝ) (ε i) := hi (by
      rw [mem_ball, Real.dist_eq, abs_sub_comm]; exact hyz)
    have hball : ∀ w, w ∈ ball ((i : Icc a b) : ℝ) (ε i) →
        w ∈ Ioo ((i : ℝ) - ε i) (i + ε i) := fun w hw => by
      rw [mem_ball, Real.dist_eq, abs_lt] at hw
      constructor <;> linarith
    have h1 := hM i i.1.2 y (hball y hyi) z (hball z hzi)
    have h2 : M i ≤ ∑ j ∈ t, |M j| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j : Icc a b => |M j|)
        (fun j _ => abs_nonneg _) i.2)
    calc ‖g y - g z‖ ≤ M i * |y - z| := h1
      _ ≤ (∑ j ∈ t, |M j|) * |y - z| := by gcongr
      _ ≤ _ := by
        have : 0 ≤ 2 * B / δ * |y - z| := by positivity
        nlinarith
  · push_neg at hyz
    have h1 : ‖g y - g z‖ ≤ 2 * B := by
      calc ‖g y - g z‖ ≤ ‖g y‖ + ‖g z‖ := norm_sub_le _ _
        _ ≤ 2 * B := by linarith [hB y, hB z]
    have h2 : 2 * B ≤ 2 * B / δ * |y - z| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      gcongr
    have h3 : 0 ≤ (∑ j ∈ t, |M j|) * |y - z| :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)
    nlinarith

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- The speed field of a chart: `Φ(x) = c̄ (1 + i f'(x)) σ c₀ / √(1 + f'(x)²)`. -/
def chartSpeedField (c : ℂ) (f : ℝ → ℝ) (σ c₀ : ℝ) (x : ℝ) : ℂ :=
  conj c * (1 + ((deriv f x : ℝ) : ℂ) * Complex.I) *
    ((σ * c₀ / Real.sqrt (1 + deriv f x ^ 2) : ℝ) : ℂ)

lemma contDiff_chartSpeedField {c : ℂ} {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (σ c₀ : ℝ) :
    ContDiff ℝ 1 (chartSpeedField c f σ c₀) := by
  have h2 : ContDiff ℝ (1 + 1) f := hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hd : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp h2).2.2
  have hs : ContDiff ℝ 1 (fun x => Real.sqrt (1 + deriv f x ^ 2)) :=
    (contDiff_const.add (hd.pow 2)).sqrt fun x => by positivity
  have hq : ContDiff ℝ 1 (fun x => σ * c₀ / Real.sqrt (1 + deriv f x ^ 2)) :=
    contDiff_const.div hs fun x => by positivity
  unfold chartSpeedField
  exact (contDiff_const.mul (contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp hd).mul contDiff_const))).mul
    (Complex.ofRealCLM.contDiff.comp hq)


lemma hasDerivAt_chartPt {p c : ℂ} {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (chartPt p c f) (conj c * (1 + ((deriv f x : ℝ) : ℂ) * Complex.I)) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((y : ℂ) + ((f y : ℝ) : ℂ) * Complex.I))
      (1 + ((deriv f x : ℝ) : ℂ) * Complex.I) x :=
    (Complex.ofRealCLM.hasDerivAt.add
      ((hf.hasDerivAt.ofReal_comp).mul_const Complex.I))
  have h2 := (h1.const_mul (conj c)).const_add p
  convert h2 using 1
  funext y; simp [chartPt]

lemma chartSpeedField_eq_mul (c : ℂ) (f : ℝ → ℝ) (σ c₀ x : ℝ) :
    chartSpeedField c f σ c₀ x = (σ : ℂ) * chartSpeedField c f 1 c₀ x := by
  simp only [chartSpeedField]
  push_cast
  ring

lemma norm_chartTangent {c : ℂ} (hc : ‖c‖ = 1) (d : ℝ) :
    ‖conj c * (1 + (d : ℂ) * Complex.I)‖ = Real.sqrt (1 + d ^ 2) := by
  rw [norm_mul, Complex.norm_conj, hc, one_mul, Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

/-- **Local regularity.** Near every parameter, `γ` is differentiable and `γ'` is Lipschitz. -/
theorem IsBoundaryParam.local_deriv_lipschitz (hS : IsSmoothDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (θ₀ : ℝ) :
    ∃ ε > 0, ∃ M : ℝ, ∀ y ∈ Ioo (θ₀ - ε) (θ₀ + ε), ∀ z ∈ Ioo (θ₀ - ε) (θ₀ + ε),
      ‖deriv γ y - deriv γ z‖ ≤ M * |y - z| := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c₀, hc₀, hspeed⟩ := hγ.const_speed
  have hΩo : IsOpen Ω := hS.1.1
  set p := γ θ₀ with hpdef
  have hp : p ∈ frontier Ω := hγ.mem_frontier θ₀
  obtain ⟨c, r, h, Kf, f, hc, hr, hh, hfs, hfL, hf0, hfb, hΩ⟩ := hS.2 p hp
  have hch : IsChartAt Ω p c r h Kf f := ⟨hc, hr, hh, hfL, hf0, hfb, hΩ⟩
  have hfd : Differentiable ℝ f := hfs.differentiable (by simp)
  set X : ℝ → ℝ := fun θ => (c * (γ θ - p)).re with hXdef
  have hXc : Continuous X := by
    simp only [hXdef]; exact Complex.continuous_re.comp
      (continuous_const.mul (hK.continuous.sub continuous_const))
  have hX0 : X θ₀ = 0 := by simp [hXdef, hpdef]
  have hXL : ∀ y z, |X y - X z| ≤ K * |y - z| := fun y z => by
    have e : X y - X z = (c * (γ y - γ z)).re := by
      simp only [hXdef]; rw [← Complex.sub_re]; ring_nf
    rw [e]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, hc, one_mul, ← dist_eq_norm, ← Real.dist_eq]
    exact hK.dist_le_mul y z
  -- the speed field is Lipschitz near `0`
  set Φ := chartSpeedField c f 1 c₀ with hΦdef
  obtain ⟨L, t, ht, hLt⟩ :=
    ((contDiff_chartSpeedField (c := c) hfs 1 c₀).contDiffAt (x := 0)).exists_lipschitzOnWith
  -- choice of the interval
  have hev : ∀ᶠ θ in 𝓝 θ₀, γ θ ∈ chartBox p c r h ∧ X θ ∈ t := by
    have hb : chartBox p c r h ∈ 𝓝 p := (isOpen_chartBox p c r h).mem_nhds (by
      simp [chartBox, hr, hh])
    have ht' : t ∈ 𝓝 (X θ₀) := by rw [hX0]; exact ht
    exact Filter.inter_mem (hK.continuous.continuousAt.preimage_mem_nhds hb)
      (hXc.continuousAt.preimage_mem_nhds ht')
  obtain ⟨ε₁, hε₁, hε₁P⟩ := Metric.eventually_nhds_iff.mp hev
  set ε := min ε₁ π with hεdef
  have hε : 0 < ε := lt_min hε₁ Real.pi_pos
  set I := Ioo (θ₀ - ε) (θ₀ + ε) with hIdef
  have hIP : ∀ θ ∈ I, γ θ ∈ chartBox p c r h ∧ X θ ∈ t := fun θ hθ => hε₁P (by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2, min_le_left ε₁ π])
  have hIo : IsOpen I := isOpen_Ioo
  -- the boundary is the graph over `I`
  have hgraph : ∀ θ ∈ I, γ θ = chartPt p c f (X θ) := fun θ hθ =>
    eq_chartPt_of_frontier hΩo hch (hγ.mem_frontier θ) (hIP θ hθ).1
  -- monotonicity of the abscissa
  have hinj : InjOn X I := by
    intro y hy z hz hyz
    refine hγ.eq_of_eq ?_ (by rw [hgraph y hy, hgraph z hz, hyz])
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2, hz.1, hz.2, min_le_right ε₁ π]
  obtain ⟨σ, hσ, hσmono⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ MonotoneOn (fun θ => σ * X θ) I := by
    rcases hXc.continuousOn.strictMonoOn_of_injOn_Ioo (by linarith) hinj with hm | hm
    · exact ⟨1, Or.inl rfl, fun a ha b hb hab => by simpa using hm.monotoneOn ha hb hab⟩
    · exact ⟨-1, Or.inr rfl, fun a ha b hb hab => by simpa using hm.antitoneOn ha hb hab⟩
  -- almost everywhere, `γ' = σ Φ(X)`
  set G : ℝ → ℂ := fun θ => (σ : ℂ) * Φ (X θ) with hGdef
  have hGc : Continuous G :=
    continuous_const.mul ((contDiff_chartSpeedField hfs 1 c₀).continuous.comp hXc)
  have hae : ∀ᵐ θ, θ ∈ I → deriv γ θ = G θ := by
    filter_upwards [hK.ae_differentiableAt (μ := volume), hspeed] with θ hd hs hθ
    set dX := (c * deriv γ θ).re
    have hXd : HasDerivAt X dX θ := by
      have h1 : HasDerivAt (fun θ => c * (γ θ - p)) (c * deriv γ θ) θ :=
        (hd.hasDerivAt.sub_const p).const_mul c
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ h1
    have hcomp := (hasDerivAt_chartPt (p := p) (c := c) (hfd (X θ))).scomp θ hXd
    have heq : (chartPt p c f ∘ X) =ᶠ[𝓝 θ] γ :=
      Filter.eventually_of_mem (hIo.mem_nhds hθ) fun y hy => (hgraph y hy).symm
    have hγd : deriv γ θ = dX • (conj c * (1 + ((deriv f (X θ) : ℝ) : ℂ) * Complex.I)) :=
      hd.hasDerivAt.unique (hcomp.congr_of_eventuallyEq heq.symm)
    have hnorm : |dX| * Real.sqrt (1 + deriv f (X θ) ^ 2) = c₀ := by
      rw [← hs, hγd, norm_smul, norm_chartTangent hc, Real.norm_eq_abs]
    have hsq : 0 < Real.sqrt (1 + deriv f (X θ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hsign : 0 ≤ σ * dX := by
      have hσd : HasDerivAt (fun θ => σ * X θ) (σ * dX) θ := hXd.const_mul σ
      have := hσmono.derivWithin_nonneg (x := θ)
      rwa [derivWithin_of_isOpen hIo hθ, hσd.deriv] at this
    have hdX : dX = σ * c₀ / Real.sqrt (1 + deriv f (X θ) ^ 2) := by
      rw [eq_div_iff hsq.ne', ← hnorm]
      rcases hσ with rfl | rfl
      · rw [abs_of_nonneg (by linarith)]; ring
      · rw [abs_of_nonpos (by linarith)]; ring
    rw [hγd]
    simp only [hGdef, hΦdef]
    rw [← chartSpeedField_eq_mul, chartSpeedField, hdX, Complex.real_smul]
    ring
  -- hence `γ' = σ Φ(X)` everywhere on `I`
  have hderiv : ∀ θ ∈ I, deriv γ θ = G θ := by
    intro θ hθ
    have hFTC : ∀ x ∈ I, γ x = γ θ₀ + ∫ s in θ₀..x, G s := by
      intro x hx
      have hsub : uIoc θ₀ x ⊆ I := by
        intro s hs
        have := uIoc_subset_uIcc hs
        rw [mem_uIcc] at this
        constructor <;> rcases this with h | h <;> linarith [hx.1, hx.2, h.1, h.2]
      rw [← intervalIntegral.integral_congr_ae (hae.mono fun s hs hsI => hs (hsub hsI)),
        integral_deriv_of_lipschitz hK]
      ring
    have hd : HasDerivAt (fun x => γ θ₀ + ∫ s in θ₀..x, G s) (G θ) θ :=
      ((hGc.integral_hasStrictDerivAt θ₀ θ).hasDerivAt).const_add _
    have heq : (fun x => γ θ₀ + ∫ s in θ₀..x, G s) =ᶠ[𝓝 θ] γ :=
      Filter.eventually_of_mem (hIo.mem_nhds hθ) fun y hy => (hFTC y hy).symm
    exact (hd.congr_of_eventuallyEq heq.symm).deriv
  refine ⟨ε, hε, L * K, fun y hy z hz => ?_⟩
  rw [hderiv y hy, hderiv z hz, hGdef]
  simp only
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show |σ| = 1 by rcases hσ with rfl | rfl <;> simp, one_mul]
  have h1 := hLt.dist_le_mul (X y) (hIP y hy).2 (X z) (hIP z hz).2
  rw [dist_eq_norm, Real.dist_eq] at h1
  calc ‖Φ (X y) - Φ (X z)‖ ≤ L * |X y - X z| := h1
    _ ≤ L * (K * |y - z|) := by gcongr; exact hXL y z
    _ = L * K * |y - z| := by ring

/-- **`γ'` is Lipschitz on `[0, 2π]`** for the constant-speed boundary parametrization of a
smooth domain. -/
theorem IsBoundaryParam.deriv_lipschitz (hS : IsSmoothDomain Ω) (hγ : IsBoundaryParam Ω γ) :
    ∃ K' : NNReal, ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y| := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨M, hM⟩ := lipschitzOn_Icc_of_local (g := deriv γ) (B := K)
    (fun x => norm_deriv_le_of_lipschitzWith hK x)
    (fun x _ => hγ.local_deriv_lipschitz hS x)
  refine ⟨⟨max M 0, le_max_right _ _⟩, fun x hx y hy => ?_⟩
  refine (hM x hx y hy).trans ?_
  change _ ≤ max M 0 * _
  gcongr
  exact le_max_left _ _

end PolyaNeumann
