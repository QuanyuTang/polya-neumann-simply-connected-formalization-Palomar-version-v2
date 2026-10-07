module

public import RequestProject.PhysicalCauchyBase
public import RequestProject.WindingJump
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual local control of the weighted physical Cauchy integral

For a C¹ curve with nonzero tangent, its real tangent projection grows at a
positive rate on a genuine neighborhood.  The mean value theorem therefore
controls the parameter by the distance to every point on the normal line.
Combining this with the actual local Lipschitz property of a C¹ density gives
a uniform bound for the Cauchy commutator.  Dominated convergence proves its
two-sided normal limit.

In particular these conclusions apply to the actual physical moment primitive
constructed in `PhysicalMomentPrimitive`, without assuming a chord bound,
Hardy support, a weighted jump, or any elliptic regularity.  This file proves
the local commutator part of the weighted jump; the constant-density part is
the existing `windingNumber_jump` theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

/-- The actual (not necessarily unit) physical normal to the supplied tangent. -/
def physicalCauchyNormal (γ : ℝ → ℂ) : ℂ := Complex.I * deriv γ 0

/-- The real tangent projection has the actual projected derivative. -/
private theorem physicalTangentProjection_hasDerivAt
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (θ : ℝ) :
    HasDerivAt
      (fun s : ℝ => (conj (deriv γ 0) * (γ s - γ 0)).re)
      (conj (deriv γ 0) * deriv γ θ).re θ := by
  have hd := ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0))
    .const_mul (conj (deriv γ 0))
  simpa only [Function.comp_def, Complex.reCLM_apply] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ hd

/-- A genuine local inverse-parameter estimate.  Its coefficient is positive
and is derived from the nonzero tangent, rather than postulated.  The estimate
holds uniformly for every displacement on the actual normal line. -/
theorem exists_local_physical_normal_parameter_bound
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (ht : deriv γ 0 ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
      ∀ θ ∈ Icc (-η) η, ∀ s : ℝ,
        |θ| ≤ C * ‖γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ‖ := by
  let c : ℂ := conj (deriv γ 0)
  let D : ℝ := Complex.normSq (deriv γ 0)
  let x : ℝ → ℝ := fun θ => (c * (γ θ - γ 0)).re
  have hD : 0 < D := Complex.normSq_pos.mpr ht
  have hc : 0 < ‖c‖ := by
    simpa only [c, Complex.norm_conj] using norm_pos_iff.mpr ht
  have hx0 : x 0 = 0 := by simp only [x, sub_self, mul_zero, Complex.zero_re]
  have hd0 : (c * deriv γ 0).re = D := by
    dsimp only [c, D]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hdx (θ : ℝ) : HasDerivAt x (c * deriv γ θ).re θ :=
    physicalTangentProjection_hasDerivAt γ hγ θ
  have hx : Differentiable ℝ x := fun θ => (hdx θ).differentiableAt
  have hdc : Continuous (fun θ : ℝ => (c * deriv γ θ).re) :=
    Complex.continuous_re.comp (continuous_const.mul hγ.continuous_deriv_one)
  have hopen : IsOpen {θ : ℝ | D / 2 < (c * deriv γ θ).re} :=
    isOpen_lt continuous_const hdc
  have h0mem : (0 : ℝ) ∈ {θ : ℝ | D / 2 < (c * deriv γ θ).re} := by
    change D / 2 < (c * deriv γ 0).re
    rw [hd0]
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds h0mem)
  have hlower (θ : ℝ) (hθ : θ ∈ Ioo (-r) r) : D / 2 ≤ deriv x θ := by
    rw [(hdx θ).deriv]
    apply le_of_lt (hball ?_)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] using hθ
  have hgrowth := convex_Ioo.mul_sub_le_image_sub_of_le_deriv
    hx.continuous.continuousOn hx.differentiableOn
    (fun θ hθ => hlower θ (interior_subset hθ))
  have hz : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  refine ⟨r / 2, half_pos hr, ‖c‖ / (D / 2), div_pos hc (half_pos hD), ?_⟩
  intro θ hθ s
  have hθr : θ ∈ Ioo (-r) r := by
    constructor <;> linarith [hθ.1, hθ.2]
  have hp : D / 2 * |θ| ≤ |x θ| := by
    by_cases hθ0 : 0 ≤ θ
    · have hg := hgrowth 0 hz θ hθr hθ0
      simp only [hx0, sub_zero] at hg
      rw [abs_of_nonneg hθ0]
      exact hg.trans (le_abs_self _)
    · have hθ0' : θ ≤ 0 := (not_le.mp hθ0).le
      have hg := hgrowth θ hθr 0 hz hθ0'
      simp only [hx0, zero_sub] at hg
      rw [abs_of_nonpos hθ0']
      exact hg.trans (neg_le_abs _)
  have hnormal : (c * ((s : ℂ) * physicalCauchyNormal γ)).re = 0 := by
    have heq : c * ((s : ℂ) * physicalCauchyNormal γ) =
        ((s : ℂ) * Complex.I) * (D : ℂ) := by
      dsimp only [c, D, physicalCauchyNormal]
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    rw [heq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_sub]
  have hproj : (c * (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ)).re = x θ := by
    rw [mul_sub, Complex.sub_re, hnormal, sub_zero]
    rfl
  have hpn : D / 2 * |θ| ≤
      ‖c‖ * ‖γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ‖ := by
    calc
      _ ≤ |x θ| := hp
      _ = |(c * (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ)).re| := by rw [hproj]
      _ ≤ ‖c * (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ)‖ :=
        Complex.abs_re_le_norm _
      _ = _ := norm_mul _ _
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (half_pos hD)).mpr (by simpa only [mul_comm] using hpn)

/-- C¹ regularity of the density, together with the actual tangent estimate,
gives a genuine uniformly bounded local Cauchy commutator. -/
theorem exists_local_physicalCauchyCommutator_bound
    (γ K : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hK : ContDiff ℝ 1 K)
    (ht : deriv γ 0 ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ θ ∈ Icc (-η) η, θ ≠ 0 → γ θ - γ 0 ≠ 0) ∧
      ∀ θ ∈ Icc (-η) η, ∀ s : ℝ,
        ‖(deriv γ θ * (K θ - K 0)) /
          (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ)‖ ≤ B := by
  obtain ⟨r, hr, C, hC, hparam⟩ :=
    exists_local_physical_normal_parameter_bound γ hγ ht
  obtain ⟨L, U, hU, hKL⟩ := (hK.contDiffAt (x := 0)).exists_lipschitzOnWith
  obtain ⟨q, hq, hqU⟩ := Metric.mem_nhds_iff.mp hU
  let η : ℝ := min r (q / 2)
  have hη : 0 < η := lt_min hr (half_pos hq)
  have hηr : η ≤ r := min_le_left _ _
  have hηq : η ≤ q / 2 := min_le_right _ _
  have hθr (θ : ℝ) (hθ : θ ∈ Icc (-η) η) : θ ∈ Icc (-r) r := by
    constructor <;> linarith [hθ.1, hθ.2]
  have hθU (θ : ℝ) (hθ : θ ∈ Icc (-η) η) : θ ∈ U := by
    apply hqU
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2]
  have h0U : (0 : ℝ) ∈ U := hqU (Metric.mem_ball_self hq)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-η) η) hγ.continuous_deriv_one.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (deriv γ 0)).trans
    (hM 0 ⟨by linarith, hη.le⟩)
  refine ⟨η, hη, M * ((L : ℝ) * C), by positivity, ?_, ?_⟩
  · intro θ hθ hθ0 heq
    have hp := hparam θ (hθr θ hθ) 0
    rw [zero_mul, sub_zero, heq, norm_zero, mul_zero] at hp
    exact hθ0 (abs_eq_zero.mp (le_antisymm hp (abs_nonneg _)))
  · intro θ hθ s
    have hKLθ : ‖K θ - K 0‖ ≤ (L : ℝ) * |θ| := by
      simpa only [dist_eq_norm, Real.dist_eq, sub_zero] using
        hKL.dist_le_mul θ (hθU θ hθ) 0 h0U
    have hKb : ‖K θ - K 0‖ ≤ ((L : ℝ) * C) *
        ‖γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ‖ := by
      calc
        _ ≤ (L : ℝ) * |θ| := hKLθ
        _ ≤ (L : ℝ) * (C * ‖γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ‖) :=
          mul_le_mul_of_nonneg_left (hparam θ (hθr θ hθ) s) L.coe_nonneg
        _ = _ := by ring
    by_cases hd : γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ = 0
    · rw [hd, div_zero, norm_zero]
      positivity
    · rw [norm_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr hd)).mpr
      calc
        _ = ‖deriv γ θ‖ * ‖K θ - K 0‖ := norm_mul _ _
        _ ≤ M * ‖K θ - K 0‖ := mul_le_mul_of_nonneg_right (hM θ hθ) (norm_nonneg _)
        _ ≤ M * (((L : ℝ) * C) *
            ‖γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ‖) :=
          mul_le_mul_of_nonneg_left hKb hM0
        _ = _ := by ring

/-- The actual local commutator has the same limit from both sides of the
normal.  The uniform integrable domination above is derived from the C¹
curve and density; no boundary jump or quotient bound is assumed. -/
theorem exists_local_physicalCauchyCommutator_limit
    (γ K : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hK : ContDiff ℝ 1 K)
    (ht : deriv γ 0 ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      Tendsto
        (fun s : ℝ => ∫ θ in (-η)..η,
          (deriv γ θ * (K θ - K 0)) /
            (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ))
        (𝓝 0)
        (𝓝 (∫ θ in (-η)..η,
          (deriv γ θ * (K θ - K 0)) / (γ θ - γ 0))) := by
  obtain ⟨η, hη, B, _, hne, hB⟩ :=
    exists_local_physicalCauchyCommutator_bound γ K hγ hK ht
  refine ⟨η, hη, ?_⟩
  have hab : -η ≤ η := by linarith
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun _ : ℝ => B) ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun s =>
      ((hγ.continuous_deriv_one.measurable.mul
        (hK.continuous.measurable.sub measurable_const)).div
        ((hγ.continuous.measurable.sub measurable_const).sub measurable_const))
        .aestronglyMeasurable
  · exact Eventually.of_forall fun s => Eventually.of_forall fun θ hθ => by
      rw [uIoc_of_le hab] at hθ
      exact hB θ ⟨hθ.1.le, hθ.2⟩ s
  · refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    by_cases hθ0 : θ = 0
    · subst θ
      simpa only [sub_self, mul_zero, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝 0) (𝓝 0))
    · have hd : γ θ - γ 0 ≠ 0 := hne θ ⟨hθ.1.le, hθ.2⟩ hθ0
      have hc : Continuous (fun s : ℝ =>
          γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ) := by fun_prop
      have hdt := hc.tendsto' 0 (γ θ - γ 0) (by simp only [Complex.ofReal_zero,
        zero_mul, sub_zero])
      exact tendsto_const_nhds.div hdt hd

/-- The actual physical moment primitive supplies the required C¹ density.
Its normalization at the supplied boundary origin makes its local weighted
integral itself a commutator, with no constant or zero mode discarded. -/
theorem exists_local_physicalMomentPrimitive_Cauchy_limit
    (γ H : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (ht : deriv γ 0 ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      Tendsto
        (fun s : ℝ => ∫ θ in (-η)..η,
          (deriv γ θ * physicalMomentPrimitive γ H θ) /
            (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ))
        (𝓝 0)
        (𝓝 (∫ θ in (-η)..η,
          (deriv γ θ * physicalMomentPrimitive γ H θ) / (γ θ - γ 0))) := by
  simpa only [physicalMomentPrimitive_zero, sub_zero] using
    exists_local_physicalCauchyCommutator_limit γ (physicalMomentPrimitive γ H)
      hγ (contDiff_physicalMomentPrimitive γ H hγ hH) ht

/-- The actual commutator over one complete physical boundary period.
The denominator convention agrees with `windingNumber`, including its sign. -/
def physicalCauchyCommutator (γ K : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (deriv γ θ * (K θ - K 0)) / (γ θ - γ 0 - w)

/-- Compact separation on the remaining arc joins the genuine local
commutator limit into the actual full-period limit.  The avoidance hypothesis
is precisely absence of another visit to the supplied boundary origin during
the open period, as supplied by a simple physical Jordan parameter. -/
theorem physicalCauchyCommutator_normal_limit
    (γ K : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hK : ContDiff ℝ 1 K)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hpK : Function.Periodic K (2 * Real.pi)) (ht : deriv γ 0 ≠ 0)
    (havoid : ∀ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), γ θ ≠ γ 0) :
    Tendsto (fun s : ℝ =>
      physicalCauchyCommutator γ K ((s : ℂ) * physicalCauchyNormal γ))
      (𝓝 0) (𝓝 (physicalCauchyCommutator γ K 0)) := by
  obtain ⟨r, hr, B, _, _, hB⟩ :=
    exists_local_physicalCauchyCommutator_bound γ K hγ hK ht
  let η : ℝ := min r (Real.pi / 2)
  have hη : 0 < η := lt_min hr (half_pos Real.pi_pos)
  have hηr : η ≤ r := min_le_left _ _
  have hfar : ∀ θ ∈ Icc η (2 * Real.pi - η), γ θ ≠ γ 0 := by
    intro θ hθ
    exact havoid θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  obtain ⟨d, hd, hdist⟩ := exists_pos_le_norm_sub hγ.continuous hfar
  let g : ℝ → ℂ := fun θ => deriv γ θ * (K θ - K 0)
  have hg : Continuous g :=
    hγ.continuous_deriv_one.mul (hK.continuous.sub continuous_const)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * Real.pi)) hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans
    (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hshiftγ (θ : ℝ) : γ (θ - 2 * Real.pi) = γ θ := by
    simpa only [sub_add_cancel] using (hpγ (θ - 2 * Real.pi)).symm
  have hshiftK (θ : ℝ) : K (θ - 2 * Real.pi) = K θ := by
    simpa only [sub_add_cancel] using (hpK (θ - 2 * Real.pi)).symm
  have hshiftd (θ : ℝ) : deriv γ (θ - 2 * Real.pi) = deriv γ θ := by
    simpa only [sub_add_cancel] using (deriv_periodic hpγ (θ - 2 * Real.pi)).symm
  have hncont : Continuous (fun s : ℝ =>
      ‖(s : ℂ) * physicalCauchyNormal γ‖) := by fun_prop
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0,
      ‖(s : ℂ) * physicalCauchyNormal γ‖ < d / 2 :=
    (hncont.tendsto' 0 0 (by simp)).eventually_lt_const (half_pos hd)
  have hfull : ∀ᶠ s : ℝ in 𝓝 0, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖g θ / (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ)‖ ≤
        max B (M / (d / 2)) := by
    filter_upwards [hsmall] with s hs
    intro θ hθ
    by_cases hnear : θ ≤ η
    · have hθr : θ ∈ Icc (-r) r := by
        constructor <;> linarith [hθ.1, hηr]
      exact (hB θ hθr s).trans (le_max_left _ _)
    · by_cases htop : 2 * Real.pi - η ≤ θ
      · have hθr : θ - 2 * Real.pi ∈ Icc (-r) r := by
          constructor <;> linarith [hθ.2, hηr]
        have hb := hB (θ - 2 * Real.pi) hθr s
        rw [hshiftγ θ, hshiftK θ, hshiftd θ] at hb
        exact hb.trans (le_max_left _ _)
      · have hθfar : θ ∈ Icc η (2 * Real.pi - η) :=
          ⟨(not_le.mp hnear).le, (not_le.mp htop).le⟩
        have hlower : d / 2 ≤
            ‖γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ‖ := by
          have ht := norm_sub_norm_le (γ θ - γ 0)
            ((s : ℂ) * physicalCauchyNormal γ)
          have hh := hdist θ hθfar
          linarith
        rw [norm_div]
        exact (div_le_div₀ hM0 (hM θ hθ) (half_pos hd) hlower).trans
          (le_max_right _ _)
  have hlim : Tendsto
      (fun s : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        g θ / (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ))
      (𝓝 0) (𝓝 (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (γ θ - γ 0))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (bound := fun _ : ℝ => max B (M / (d / 2)))
      ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun s =>
        (hg.measurable.div ((hγ.continuous.measurable.sub measurable_const)
          .sub measurable_const)).aestronglyMeasurable
    · filter_upwards [hfull] with s hs
      exact Eventually.of_forall fun θ hθ => by
        rw [uIoc_of_le Real.two_pi_pos.le] at hθ
        exact hs θ ⟨hθ.1.le, hθ.2⟩
    · refine Eventually.of_forall fun θ hθ => ?_
      rw [uIoc_of_le Real.two_pi_pos.le] at hθ
      by_cases hθL : θ = 2 * Real.pi
      · subst θ
        have hKL : K (2 * Real.pi) = K 0 := by
          simpa only [zero_add] using hpK 0
        simpa only [g, hKL, sub_self, mul_zero, zero_div] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝 0) (𝓝 0))
      · have hdθ : γ θ - γ 0 ≠ 0 := sub_ne_zero.mpr
          (havoid θ ⟨hθ.1, lt_of_le_of_ne hθ.2 hθL⟩)
        have hc : Continuous (fun s : ℝ =>
            γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ) := by fun_prop
        exact tendsto_const_nhds.div
          (hc.tendsto' 0 (γ θ - γ 0) (by simp)) hdθ
  simpa only [physicalCauchyCommutator, sub_zero] using hlim

/-- The physical primitive has this actual full-period normal trace limit.
The only moment needed here is the zero moment, to make it periodic. -/
theorem physicalMomentPrimitive_full_Cauchy_limit
    (γ H : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hpH : Function.Periodic H (2 * Real.pi)) (ht : deriv γ 0 ≠ 0)
    (havoid : ∀ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), γ θ ≠ γ 0)
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    Tendsto (fun s : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (deriv γ θ * physicalMomentPrimitive γ H θ) /
        (γ θ - γ 0 - (s : ℂ) * physicalCauchyNormal γ))
      (𝓝 0) (𝓝 (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (deriv γ θ * physicalMomentPrimitive γ H θ) / (γ θ - γ 0))) := by
  simpa only [physicalCauchyCommutator, physicalMomentPrimitive_zero, sub_zero] using
    physicalCauchyCommutator_normal_limit γ (physicalMomentPrimitive γ H) hγ
      (contDiff_physicalMomentPrimitive γ H hγ hH) hpγ
      (physicalMomentPrimitive_periodic γ H hγ hH hpγ hpH hmom0) ht havoid

/-- In a physical chart with real tangent, the actual normal limit is the
vertical limit used by the existing winding jump.  No unit-speed condition
is needed: the nonzero real tangent is accounted for by a real rescaling. -/
theorem physicalCauchyCommutator_vertical_limit
    (γ K : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hK : ContDiff ℝ 1 K)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hpK : Function.Periodic K (2 * Real.pi)) (ht : deriv γ 0 ≠ 0)
    (htim : (deriv γ 0).im = 0)
    (havoid : ∀ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), γ θ ≠ γ 0) :
    Tendsto (fun s : ℝ => physicalCauchyCommutator γ K ((s : ℂ) * Complex.I))
      (𝓝 0) (𝓝 (physicalCauchyCommutator γ K 0)) := by
  let v : ℝ := (deriv γ 0).re
  have htv : deriv γ 0 = (v : ℂ) := by
    apply Complex.ext
    · simp only [v, Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using htim
  have hv : v ≠ 0 := by
    intro hv0
    apply ht
    rw [htv, hv0, Complex.ofReal_zero]
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  have hpath (s : ℝ) : ((s / v : ℝ) : ℂ) * physicalCauchyNormal γ =
      (s : ℂ) * Complex.I := by
    rw [physicalCauchyNormal, htv, Complex.ofReal_div]
    field_simp [hvC] <;> ring
  have hs : Tendsto (fun s : ℝ => s / v) (𝓝 0) (𝓝 0) :=
    (continuous_id.div_const v).tendsto' 0 0 (by simp)
  simpa only [Function.comp_def, hpath] using
    (physicalCauchyCommutator_normal_limit γ K hγ hK hpγ hpK ht havoid).comp hs

/-- The actual algebraic separation into the commutator and constant density.
The factor is `2πi`, with the sign dictated by `γ - z`. -/
theorem physicalWeightedCauchy_eq_commutator_add_winding
    (γ K : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hK : Continuous K)
    (h0 : γ 0 = 0) {z : ℂ}
    (havoid : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), γ θ ≠ z) :
    physicalWeightedCauchy γ K z = physicalCauchyCommutator γ K z +
      (2 * Real.pi * Complex.I) * K 0 * windingNumber γ z := by
  let f : ℝ → ℂ := fun θ => (deriv γ θ * (K θ - K 0)) / (γ θ - z)
  let q : ℝ → ℂ := fun θ => deriv γ θ / (γ θ - z)
  have hf : IntervalIntegrable f volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
    exact (hγ.continuous_deriv_one.mul (hK.sub continuous_const)).continuousOn.div
      (hγ.continuous.sub continuous_const).continuousOn
      (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))
  have hq : IntervalIntegrable q volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
    exact hγ.continuous_deriv_one.continuousOn.div
      (hγ.continuous.sub continuous_const).continuousOn
      (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))
  have heq : (fun θ => (deriv γ θ * K θ) / (γ θ - z)) =
      (fun θ => f θ + K 0 * q θ) := by
    funext θ
    dsimp only [f, q]
    ring
  have ha : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hconst : (2 * Real.pi * Complex.I) * K 0 * windingNumber γ z =
      K 0 * ∫ θ in (0 : ℝ)..(2 * Real.pi), q θ := by
    rw [windingNumber]
    change (2 * Real.pi * Complex.I) * K 0 *
      ((2 * Real.pi * Complex.I)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) = _
    field_simp [ha] <;> ring
  rw [hconst, physicalWeightedCauchy, heq,
    intervalIntegral.integral_add hf (hq.const_mul (K 0)),
    intervalIntegral.integral_const_mul, physicalCauchyCommutator, h0, sub_zero]

/-- The actual graph near the supplied origin and compact separation on the
remaining arc ensure that sufficiently small nonzero vertical points are
off the entire physical curve.  This supplies genuine integral identities
along both approaches; it is not a boundary-jump premise. -/
private theorem exists_vertical_avoidance
    {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hpγ : Function.Periodic γ (2 * Real.pi)) {η : ℝ}
    (hη : 0 < η) {f : ℝ → ℝ}
    (h0 : γ 0 = 0)
    (hgraph : ∀ θ ∈ Icc (-η) η, (γ θ).im = f (γ θ).re)
    (hfar : ∀ θ ∈ Icc η (2 * Real.pi - η), γ θ ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, s ≠ 0 → |s| < d →
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), γ θ ≠ (s : ℂ) * Complex.I := by
  obtain ⟨d, hd, hdist⟩ := exists_pos_le_norm_sub hγ hfar
  have hf0 : f 0 = 0 := by
    have hg := hgraph 0 ⟨by linarith, hη.le⟩
    rw [h0] at hg
    simpa only [Complex.zero_re, Complex.zero_im] using hg.symm
  have hnear (s : ℝ) (hs : s ≠ 0) (θ : ℝ) (hθ : θ ∈ Icc (-η) η) :
      γ θ ≠ (s : ℂ) * Complex.I := by
    intro heq
    have hre : (γ θ).re = 0 := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using
        congrArg Complex.re heq
    have him : (γ θ).im = 0 := by rw [hgraph θ hθ, hre, hf0]
    have hs0 : (0 : ℝ) = s := by
      simpa only [him, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] using
        congrArg Complex.im heq
    exact hs hs0.symm
  refine ⟨d, hd, ?_⟩
  intro s hs hsd θ hθ
  by_cases hleft : θ ≤ η
  · exact hnear s hs θ ⟨by linarith [hθ.1], hleft⟩
  · by_cases hright : 2 * Real.pi - η ≤ θ
    · have hθ' : θ - 2 * Real.pi ∈ Icc (-η) η := by
        constructor <;> linarith [hθ.2]
      have he := hnear s hs (θ - 2 * Real.pi) hθ'
      have hshift : γ (θ - 2 * Real.pi) = γ θ := by
        simpa only [sub_add_cancel] using (hpγ (θ - 2 * Real.pi)).symm
      rwa [hshift] at he
    · intro heq
      have hh := hdist θ ⟨(not_le.mp hleft).le, (not_le.mp hright).le⟩
      rw [heq, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one] at hh
      linarith

/-- A genuine weighted physical Cauchy jump.  All quotient bounds and the
commutator limit are proved above from the actual C¹ curve and density.
The remaining chart hypotheses are exactly geometric local graph data;
the constant-density jump is the existing `windingNumber_jump` theorem.

The density is complex-valued and the full complex factor is retained:
with denominator `γ - z`, the jump is `2πi σ K(0)`. -/
theorem physicalWeightedCauchy_jump
    {γ : ℝ → ℂ} {L : NNReal} (hLip : LipschitzWith L γ)
    (hγ : ContDiff ℝ 1 γ) (K : ℝ → ℂ) (hK : ContDiff ℝ 1 K)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hpK : Function.Periodic K (2 * Real.pi))
    (h0 : γ 0 = 0) (ht : deriv γ 0 ≠ 0) (htim : (deriv γ 0).im = 0)
    (havoid : ∀ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), γ θ ≠ γ 0)
    {η : ℝ} (hη : 0 < η) (hηπ : η < Real.pi) {f : ℝ → ℝ}
    (hgraph : ∀ θ ∈ Icc (-η) η, (γ θ).im = f (γ θ).re)
    (hinj : InjOn γ (Icc (-η) η)) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      Tendsto (fun s : ℝ =>
        physicalWeightedCauchy γ K ((s : ℂ) * Complex.I) -
          physicalWeightedCauchy γ K (-((s : ℂ) * Complex.I)))
        (𝓝[>] 0) (𝓝 ((2 * Real.pi * Complex.I) * K 0 * σ)) := by
  have hfar : ∀ θ ∈ Icc η (2 * Real.pi - η), γ θ ≠ 0 := by
    intro θ hθ
    simpa only [h0] using havoid θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  obtain ⟨σ, hσ, hjump⟩ :=
    windingNumber_jump hLip hpγ hη hηπ h0 hgraph hinj hfar
  obtain ⟨d, hd, hoff⟩ :=
    exists_vertical_avoidance hγ.continuous hpγ hη h0 hgraph hfar
  have hc := physicalCauchyCommutator_vertical_limit γ K hγ hK hpγ hpK ht htim havoid
  have hneg : Tendsto (fun s : ℝ => -s) (𝓝 0) (𝓝 0) :=
    continuous_neg.tendsto' 0 0 (by simp)
  have hdiff : Tendsto (fun s : ℝ =>
      physicalCauchyCommutator γ K ((s : ℂ) * Complex.I) -
        physicalCauchyCommutator γ K (-((s : ℂ) * Complex.I))) (𝓝[>] 0) (𝓝 0) := by
    have hh := hc.sub (hc.comp hneg)
    have hh' : Tendsto (fun s : ℝ =>
        physicalCauchyCommutator γ K ((s : ℂ) * Complex.I) -
          physicalCauchyCommutator γ K (-((s : ℂ) * Complex.I))) (𝓝 0) (𝓝 0) := by
      simpa only [Function.comp_def, Complex.ofReal_neg, neg_mul, sub_self] using hh
    exact tendsto_nhdsWithin_of_tendsto_nhds hh'
  have heq : (fun s : ℝ =>
      physicalWeightedCauchy γ K ((s : ℂ) * Complex.I) -
        physicalWeightedCauchy γ K (-((s : ℂ) * Complex.I))) =ᶠ[𝓝[>] 0]
      (fun s : ℝ =>
        (physicalCauchyCommutator γ K ((s : ℂ) * Complex.I) -
          physicalCauchyCommutator γ K (-((s : ℂ) * Complex.I))) +
        ((2 * Real.pi * Complex.I) * K 0) *
          (windingNumber γ ((s : ℂ) * Complex.I) -
            windingNumber γ (-((s : ℂ) * Complex.I)))) := by
    filter_upwards [Ioo_mem_nhdsGT hd] with s hs
    have hpos := hoff s (ne_of_gt hs.1) (by rwa [abs_of_pos hs.1])
    have hminus := hoff (-s) (neg_ne_zero.mpr (ne_of_gt hs.1))
      (by rwa [abs_neg, abs_of_pos hs.1])
    rw [physicalWeightedCauchy_eq_commutator_add_winding γ K hγ hK.continuous h0 hpos,
      physicalWeightedCauchy_eq_commutator_add_winding γ K hγ hK.continuous h0
        (by simpa only [Complex.ofReal_neg, neg_mul] using hminus)]
    ring
  refine ⟨σ, hσ, ?_⟩
  apply Tendsto.congr' heq.symm
  have hweighted : Tendsto (fun s : ℝ => ((2 * Real.pi * Complex.I) * K 0) *
      (windingNumber γ ((s : ℂ) * Complex.I) -
        windingNumber γ (-((s : ℂ) * Complex.I)))) (𝓝[>] 0)
      (𝓝 (((2 * Real.pi * Complex.I) * K 0) * σ)) :=
    tendsto_const_nhds.mul hjump
  simpa only [zero_add] using hdiff.add hweighted

end PolyaNeumann

end
