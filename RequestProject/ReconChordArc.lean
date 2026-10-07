module

public import RequestProject.ReconBasic
public import RequestProject.BoundaryChart
public import RequestProject.ArcLength

/-!
# Lipschitz extension of boundary traces

For a bounded Lipschitz domain `Ω` with boundary parametrization `γ`, the parametrization is
bi-Lipschitz onto `∂Ω` (with respect to the distance on the circle, `chord_arc`), so every
closed Lipschitz function `h` on `[0, 2π]` is the trace `V ∘ γ` of a Lipschitz compactly
supported `V : ℂ → ℂ` (`exists_lipschitz_extension_of_trace`).

The chord-arc estimate is proved locally in a boundary chart: there the boundary is a Lipschitz
graph, the abscissa `x(s)` of `γ(s)` is strictly monotone, and the constant speed of `γ`
together with the cone condition `|γ'| ≤ (1 + K)|x'|` gives `|x'| ≥ c₀/(1 + K)`. A compactness
argument makes the estimate global.
-/

@[expose] public section

open MeasureTheory Set Filter Metric Topology
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

lemma IsBoundaryParam.mem_frontier (hγ : IsBoundaryParam Ω γ) (s : ℝ) : γ s ∈ frontier Ω := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hm := toIcoMod_mem_Ico h2π 0 s
  have he : γ (toIcoMod h2π 0 s) = γ s := by
    rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  rw [← he, ← hγ.image]
  exact mem_image_of_mem γ (Ico_subset_Icc_self (by simpa using hm))

lemma IsBoundaryParam.eq_of_eq (hγ : IsBoundaryParam Ω γ) {s s' : ℝ} (hss : |s - s'| < 2 * π)
    (he : γ s = γ s') : s = s' := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hm := toIcoMod_mem_Ico h2π 0 s
  have hm' := toIcoMod_mem_Ico h2π 0 s'
  have e1 : γ (toIcoMod h2π 0 s) = γ s := by rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  have e2 : γ (toIcoMod h2π 0 s') = γ s' := by rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  have heq : toIcoMod h2π 0 s = toIcoMod h2π 0 s' :=
    hγ.injOn (by simpa using hm) (by simpa using hm') (by rw [e1, e2, he])
  obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod h2π).mp heq
  rw [zsmul_eq_mul] at hn
  have hlt : |(n : ℝ)| < 1 := by
    have : |(n : ℝ) * (2 * π)| < 2 * π := by rw [← hn, abs_sub_comm]; exact hss
    rw [abs_mul, abs_of_pos h2π] at this
    nlinarith
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hlt
    exact Int.abs_lt_one_iff.mp this
  rw [hn0] at hn
  simp at hn
  linarith

/-- **Lower bound in a cone.** If, on an interval, a constant-speed Lipschitz curve satisfies the
cone condition `‖γ s - γ s'‖ ≤ L |Re(c(γ s - γ s'))|` and `Re(c γ)` is strictly increasing, then
`Re(c γ)` grows at least at rate `c₀ / L`. -/
lemma lower_bound_of_cone {Kγ : NNReal} (hK : LipschitzWith Kγ γ) {a b : ℝ} {c : ℂ} {L c0 : ℝ}
    (hL : 0 < L) (hspeed : ∀ᵐ θ, ‖deriv γ θ‖ = c0)
    (hcone : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, ‖γ s - γ s'‖ ≤ L * |(c * (γ s - γ s')).re|)
    (hmono : StrictMonoOn (fun s => (c * γ s).re) (Ioo a b)) {s s' : ℝ} (hs : s ∈ Ioo a b)
    (hs' : s' ∈ Ioo a b) (hss : s ≤ s') :
    c0 / L * (s' - s) ≤ (c * (γ s' - γ s)).re := by
  have hpt : ∀ u ∈ Ioo a b, ∀ v, HasDerivAt γ v u → ‖v‖ ≤ L * |(c * v).re| ∧ 0 ≤ (c * v).re := by
    intro u hu v hv
    have ht := hv.tendsto_slope_zero
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), u + t ∈ Ioo a b := by
      have : Tendsto (fun t : ℝ => u + t) (𝓝 0) (𝓝 u) := by
        simpa using (continuous_const_add u).tendsto (0 : ℝ)
      exact nhdsWithin_le_nhds (this (isOpen_Ioo.mem_nhds hu))
    have hcre : Continuous fun v : ℂ => (c * v).re :=
      Complex.continuous_re.comp (continuous_const.mul continuous_id)
    constructor
    · refine (isClosed_le continuous_norm (continuous_const.mul hcre.abs)).mem_of_tendsto ht ?_
      filter_upwards [hev] with t ht1
      show ‖t⁻¹ • (γ (u + t) - γ u)‖ ≤ L * |(c * (t⁻¹ • (γ (u + t) - γ u))).re|
      rw [norm_smul, Complex.real_smul, mul_left_comm, Complex.re_ofReal_mul, abs_mul,
        Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_left (hcone _ ht1 u hu) (abs_nonneg t⁻¹)
      linarith
    · refine (isClosed_le continuous_const hcre).mem_of_tendsto ht ?_
      filter_upwards [hev, self_mem_nhdsWithin] with t ht1 ht0
      show 0 ≤ (c * (t⁻¹ • (γ (u + t) - γ u))).re
      rw [Complex.real_smul, mul_left_comm, Complex.re_ofReal_mul, mul_sub, Complex.sub_re]
      rcases lt_or_gt_of_ne (show t ≠ 0 from ht0) with hneg | hpos
      · have : (c * γ (u + t)).re < (c * γ u).re := hmono ht1 hu (by linarith)
        exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hneg.le) (by linarith)
      · have : (c * γ u).re < (c * γ (u + t)).re := hmono hu ht1 (by linarith)
        exact mul_nonneg (inv_nonneg.mpr hpos.le) (by linarith)
  have hae : ∀ᵐ u, u ∈ Ioo a b → c0 / L ≤ (c * deriv γ u).re := by
    filter_upwards [hK.ae_differentiableAt, hspeed] with u hd hsp hu
    obtain ⟨h1, h2⟩ := hpt u hu _ hd.hasDerivAt
    rw [hsp, abs_of_nonneg h2] at h1
    rw [div_le_iff₀ hL]
    linarith
  have hd : IntervalIntegrable (fun u => (c * deriv γ u).re) volume s s' := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hss).mpr ?_
    refine Measure.integrableOn_of_bounded (M := ‖c‖ * Kγ) measure_Ioc_lt_top.ne
      (Complex.measurable_re.comp ((measurable_deriv γ).const_mul c)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    gcongr
    exact norm_deriv_le_of_lipschitz hK
  have hftc : (c * (γ s' - γ s)).re = ∫ u in s..s', (c * deriv γ u).re := by
    rw [← integral_deriv_of_lipschitz hK s s', ← intervalIntegral.integral_const_mul]
    have := (Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) hss).mpr
        (Measure.integrableOn_of_bounded (μ := volume) (M := Kγ) measure_Ioc_lt_top.ne
          (measurable_deriv γ).aestronglyMeasurable
          (Eventually.of_forall fun u => norm_deriv_le_of_lipschitz hK))).const_mul c))
    simpa using this.symm
  rw [hftc]
  have hconst : ∫ _ in s..s', c0 / L = c0 / L * (s' - s) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [← hconst]
  refine intervalIntegral.integral_mono_ae_restrict hss intervalIntegrable_const hd ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hae] with u hu hu'
  exact hu ⟨by linarith [hs.1, hu'.1], by linarith [hs'.2, hu'.2]⟩

/-- **Local chord-arc estimate.** -/
lemma local_chord_arc (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) (θ₀ : ℝ) :
    ∃ ε > 0, ∃ c1 > 0, ∀ s ∈ Ioo (θ₀ - ε) (θ₀ + ε), ∀ s' ∈ Ioo (θ₀ - ε) (θ₀ + ε),
      c1 * |s - s'| ≤ ‖γ s - γ s'‖ := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨c0, hc0, hspeed⟩ := hγ.const_speed
  have hΩo : IsOpen Ω := hL.1.1
  obtain ⟨c, r, h, K, f, hch⟩ := hL.exists_chart (hγ.mem_frontier θ₀)
  have hc : ‖c‖ = 1 := hch.1
  have hbox : γ ⁻¹' chartBox (γ θ₀) c r h ∈ 𝓝 θ₀ :=
    hKγ.continuous.continuousAt.preimage_mem_nhds ((isOpen_chartBox _ _ _ _).mem_nhds
      ⟨by simp [hch.2.1], by simp [hch.2.2.1]⟩)
  obtain ⟨ε0, hε0, hball⟩ := Metric.mem_nhds_iff.mp hbox
  set ε := min ε0 (π / 2) with hε
  have hεpos : 0 < ε := lt_min hε0 (by positivity)
  have hε1 : ε ≤ ε0 := min_le_left _ _
  have hε2 : ε ≤ π / 2 := min_le_right _ _
  set U := Ioo (θ₀ - ε) (θ₀ + ε) with hUdef
  have hU : ∀ s ∈ U, γ s ∈ chartBox (γ θ₀) c r h := fun s hs => hball (by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hcone : ∀ s ∈ U, ∀ s' ∈ U, ‖γ s - γ s'‖ ≤ (1 + K) * |(c * (γ s - γ s')).re| := by
    intro s hs s' hs'
    have := norm_sub_le_of_frontier hΩo hch (hγ.mem_frontier s) (hγ.mem_frontier s')
      (hU s hs) (hU s' hs')
    have e : (c * (γ s - γ θ₀)).re - (c * (γ s' - γ θ₀)).re = (c * (γ s - γ s')).re := by
      simp only [mul_sub, Complex.sub_re]; ring
    rwa [e] at this
  have hdist : ∀ s ∈ U, ∀ s' ∈ U, |s - s'| < 2 * π := fun s hs s' hs' => by
    rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, hs'.1, hs'.2, Real.pi_pos]
  have hinj : InjOn (fun s => (c * γ s).re) U := by
    intro s hs s' hs' he
    have hre : (c * (γ s - γ θ₀)).re = (c * (γ s' - γ θ₀)).re := by
      simp only [mul_sub, Complex.sub_re]
      simp only at he
      rw [he]
    exact hγ.eq_of_eq (hdist s hs s' hs') (eq_of_frontier_of_re_eq hΩo hch (hγ.mem_frontier s)
      (hγ.mem_frontier s') (hU s hs) (hU s' hs') hre)
  have hcont : ContinuousOn (fun s => (c * γ s).re) U :=
    (Complex.continuous_re.comp (continuous_const.mul hKγ.continuous)).continuousOn
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  -- in either orientation we get the bound
  have key : ∀ c' : ℂ, ‖c'‖ = 1 → (∀ s ∈ U, ∀ s' ∈ U,
      ‖γ s - γ s'‖ ≤ (1 + K) * |(c' * (γ s - γ s')).re|) →
      StrictMonoOn (fun s => (c' * γ s).re) U →
      ∀ s ∈ U, ∀ s' ∈ U, c0 / (1 + K) * |s - s'| ≤ ‖γ s - γ s'‖ := by
    intro c' hc' hcone' hmono' s hs s' hs'
    have hre : ∀ w : ℂ, (c' * w).re ≤ ‖w‖ := fun w =>
      (Complex.re_le_norm _).trans (by rw [norm_mul, hc', one_mul])
    rcases le_total s s' with hle | hle
    · have := lower_bound_of_cone hKγ hK1 hspeed hcone' hmono' hs hs' hle
      rw [abs_sub_comm, abs_of_nonneg (by linarith), norm_sub_rev]
      exact this.trans (hre _)
    · have := lower_bound_of_cone hKγ hK1 hspeed hcone' hmono' hs' hs hle
      rw [abs_of_nonneg (by linarith)]
      exact this.trans (hre _)
  refine ⟨ε, hεpos, c0 / (1 + K), by positivity, ?_⟩
  rcases hcont.strictMonoOn_of_injOn_Ioo (by linarith) hinj with hm | hm
  · exact key c hc hcone hm
  · refine key (-c) (by rw [norm_neg, hc]) (fun s hs s' hs' => ?_) (fun s hs s' hs' hlt => ?_)
    · rw [neg_mul, Complex.neg_re, abs_neg]; exact hcone s hs s' hs'
    · simp only [neg_mul, Complex.neg_re, neg_lt_neg_iff]
      exact hm hs hs' hlt

/-- The distance on the circle `ℝ / 2πℤ`, for parameters in `[0, 2π]`. -/
def circDist (θ θ' : ℝ) : ℝ := min |θ - θ'| (2 * π - |θ - θ'|)

/-- **Chord-arc estimate.** The boundary parametrization is bi-Lipschitz from the circle onto
`∂Ω`. -/
theorem chord_arc (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) :
    ∃ c > 0, ∀ θ ∈ Icc 0 (2 * π), ∀ θ' ∈ Icc 0 (2 * π), c * circDist θ θ' ≤ ‖γ θ - γ θ'‖ := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have h2π : (0 : ℝ) < 2 * π := by positivity
  choose ε hε c1 hc1 hloc using local_chord_arc hL hγ
  set U : ℝ → Set ℝ := fun θ₀ => Ioo (θ₀ - ε θ₀) (θ₀ + ε θ₀) with hUdef
  obtain ⟨t, -, hcov⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).elim_nhds_subcover U
    (fun x _ => Ioo_mem_nhds (by linarith [hε x]) (by linarith [hε x]))
  have hcov' : Icc (0 : ℝ) (2 * π) ⊆ ⋃ i : t, U i := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (hcov hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun i : t => isOpen_Ioo) hcov'
  have htne : t.Nonempty := by
    obtain ⟨i, -⟩ := hleb 0 ⟨le_rfl, h2π.le⟩
    exact ⟨i, i.2⟩
  set cmin := t.inf' htne c1 with hcmin
  have hcmin0 : 0 < cmin := (Finset.lt_inf'_iff _).mpr fun i _ => hc1 i
  -- near pairs
  have hnear : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ'', |θ - θ''| < δ →
      cmin * |θ - θ''| ≤ ‖γ θ - γ θ''‖ := by
    intro θ hθ θ'' hθ''
    obtain ⟨i, hi⟩ := hleb θ hθ
    have h1 : θ ∈ U i := hi (mem_ball_self hδ)
    have h2 : θ'' ∈ U i := hi (by rw [mem_ball, Real.dist_eq, abs_sub_comm]; exact hθ'')
    exact (mul_le_mul_of_nonneg_right (Finset.inf'_le _ i.2) (abs_nonneg _)).trans
      (hloc i θ h1 θ'' h2)
  -- far pairs
  have hcd : Continuous fun q : ℝ × ℝ => circDist q.1 q.2 := by
    unfold circDist; fun_prop
  set P := (Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π)) ∩ {q | δ ≤ circDist q.1 q.2} with hP
  have hPc : IsCompact P :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_const hcd)
  have hcg : Continuous fun q : ℝ × ℝ => ‖γ q.1 - γ q.2‖ := by
    have := hKγ.continuous; fun_prop
  obtain ⟨m, hm0, hm⟩ : ∃ m > 0, ∀ q ∈ P, m ≤ ‖γ q.1 - γ q.2‖ := by
    rcases P.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun q hq => by rw [he] at hq; exact hq.elim⟩
    obtain ⟨q, hq, hqmin⟩ := hPc.exists_isMinOn hne hcg.continuousOn
    refine ⟨‖γ q.1 - γ q.2‖, ?_, fun q' hq' => hqmin hq'⟩
    rcases (norm_nonneg (γ q.1 - γ q.2)).lt_or_eq with hpos | hzero
    · exact hpos
    exfalso
    have he : γ q.1 = γ q.2 := sub_eq_zero.mp (norm_eq_zero.mp hzero.symm)
    obtain ⟨⟨hq1, hq2⟩, hqδ⟩ := hq
    simp only [mem_setOf_eq, circDist] at hqδ
    have habs : |q.1 - q.2| ≤ 2 * π := by
      rw [abs_le]; constructor <;> linarith [hq1.1, hq1.2, hq2.1, hq2.2]
    rcases habs.lt_or_eq with hlt | heq
    · have := hγ.eq_of_eq hlt he
      rw [this, sub_self, abs_zero] at hqδ
      linarith [min_le_left (0 : ℝ) (2 * π - 0)]
    · rw [heq, sub_self] at hqδ
      linarith [min_le_right (2 * π) (0 : ℝ)]
  refine ⟨min cmin (m / (2 * π)), lt_min hcmin0 (by positivity), fun θ hθ θ' hθ' => ?_⟩
  have hd0 : 0 ≤ circDist θ θ' := by
    unfold circDist
    refine le_min (abs_nonneg _) ?_
    rw [sub_nonneg, abs_le]; constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  have hd2 : circDist θ θ' ≤ 2 * π := by
    unfold circDist
    refine (min_le_left _ _).trans ?_
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  by_cases hfar : δ ≤ circDist θ θ'
  · calc min cmin (m / (2 * π)) * circDist θ θ' ≤ m / (2 * π) * (2 * π) :=
          mul_le_mul (min_le_right _ _) hd2 hd0 (by positivity)
      _ = m := by field_simp
      _ ≤ ‖γ θ - γ θ'‖ := hm (θ, θ') ⟨⟨hθ, hθ'⟩, hfar⟩
  · push_neg at hfar
    unfold circDist at hfar ⊢
    rcases min_lt_iff.mp hfar with h1 | h1
    · calc min cmin (m / (2 * π)) * min |θ - θ'| (2 * π - |θ - θ'|) ≤ cmin * |θ - θ'| :=
            mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min (abs_nonneg _) (by
              rw [sub_nonneg, abs_le]; constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]))
              hcmin0.le
        _ ≤ ‖γ θ - γ θ'‖ := hnear θ hθ θ' h1
    · obtain ⟨θ'', hγeq, habs⟩ : ∃ θ'', γ θ'' = γ θ' ∧ |θ - θ''| = 2 * π - |θ - θ'| := by
        rcases le_total θ θ' with hle | hle
        · refine ⟨θ' - 2 * π, hγ.periodic.sub_eq θ', ?_⟩
          rw [abs_of_nonneg (by linarith [hθ.1, hθ'.2]), abs_of_nonpos (by linarith)]
          ring
        · refine ⟨θ' + 2 * π, hγ.periodic θ', ?_⟩
          rw [abs_of_nonpos (by linarith [hθ.2, hθ'.1]), abs_of_nonneg (by linarith)]
          ring
      have := hnear θ hθ θ'' (by rw [habs]; exact h1)
      rw [hγeq, habs] at this
      calc min cmin (m / (2 * π)) * min |θ - θ'| (2 * π - |θ - θ'|)
          ≤ cmin * (2 * π - |θ - θ'|) :=
            mul_le_mul (min_le_left _ _) (min_le_right _ _) (le_min (abs_nonneg _) (by
              rw [sub_nonneg, abs_le]; constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]))
              hcmin0.le
        _ ≤ ‖γ θ - γ θ'‖ := this

/-- A closed Lipschitz function on `[0, 2π]` is Lipschitz for the circle distance. -/
lemma norm_sub_le_circDist {h : ℝ → ℂ} {K : NNReal} (hK : LipschitzOnWith K h (Icc 0 (2 * π)))
    (hper : h (2 * π) = h 0) {θ θ' : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) (hθ' : θ' ∈ Icc 0 (2 * π)) :
    ‖h θ - h θ'‖ ≤ K * circDist θ θ' := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hd : ∀ x ∈ Icc (0 : ℝ) (2 * π), ∀ y ∈ Icc (0 : ℝ) (2 * π), ‖h x - h y‖ ≤ K * |x - y| :=
    fun x hx y hy => by
      have := hK.dist_le_mul x hx y hy
      rwa [dist_eq_norm, Real.dist_eq] at this
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * π) := ⟨le_rfl, h2π.le⟩
  have h1 : 2 * π ∈ Icc (0 : ℝ) (2 * π) := ⟨h2π.le, le_rfl⟩
  unfold circDist
  rw [mul_min_of_nonneg _ _ (NNReal.coe_nonneg K)]
  refine le_min (hd θ hθ θ' hθ') ?_
  rcases le_total θ θ' with hle | hle
  · have e : h θ - h θ' = (h θ - h 0) + (h (2 * π) - h θ') := by rw [hper]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have a1 := hd θ hθ 0 h0
    have a2 := hd (2 * π) h1 θ' hθ'
    rw [abs_of_nonpos (by linarith)]
    rw [sub_zero, abs_of_nonneg hθ.1] at a1
    rw [abs_of_nonneg (by linarith [hθ'.2])] at a2
    nlinarith
  · have e : h θ - h θ' = (h θ - h (2 * π)) + (h 0 - h θ') := by rw [hper]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have a1 := hd θ hθ (2 * π) h1
    have a2 := hd 0 h0 θ' hθ'
    rw [abs_of_nonneg (by linarith)]
    rw [abs_of_nonpos (by linarith [hθ.2])] at a1
    rw [zero_sub, abs_neg, abs_of_nonneg hθ'.1] at a2
    nlinarith

/-- Every closed Lipschitz function on `[0, 2π]` is the trace along `γ` of a Lipschitz compactly
supported function on `ℂ`. -/
theorem exists_lipschitz_extension_of_trace {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {h : ℝ → ℂ}
    {K : NNReal} (hK : LipschitzOnWith K h (Icc 0 (2 * π))) (hper : h (2 * π) = h 0) :
    ∃ V : ℂ → ℂ, (∃ K' : NNReal, LipschitzWith K' V) ∧ HasCompactSupport V ∧
      ∀ θ ∈ Icc 0 (2 * π), V (γ θ) = h θ := by
  classical
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨c, hc, hca⟩ := chord_arc hL hγ
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set S : Set ℂ := γ '' Icc 0 (2 * π) with hS
  have hSc : IsCompact S := isCompact_Icc.image hKγ.continuous
  obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨Mh, hMh⟩ := isCompact_Icc.exists_bound_of_continuousOn hK.continuousOn
  -- `h` is Lipschitz with respect to the chord
  set Lc : ℝ := K / c with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  have hchord : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ' ∈ Icc (0 : ℝ) (2 * π),
      ‖h θ - h θ'‖ ≤ Lc * ‖γ θ - γ θ'‖ := by
    intro θ hθ θ' hθ'
    refine (norm_sub_le_circDist hK hper hθ hθ').trans ?_
    have := hca θ hθ θ' hθ'
    rw [hLc, div_mul_eq_mul_div, le_div_iff₀ hc]
    calc (K : ℝ) * circDist θ θ' * c = K * (c * circDist θ θ') := by ring
      _ ≤ K * ‖γ θ - γ θ'‖ := by gcongr
  choose! θof hθof using fun p (hp : p ∈ S) => hp
  have hval : ∀ θ ∈ Icc (0 : ℝ) (2 * π), h (θof (γ θ)) = h θ := by
    intro θ hθ
    have hm : γ θ ∈ S := mem_image_of_mem γ hθ
    have := hchord _ (hθof _ hm).1 θ hθ
    rw [(hθof _ hm).2, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  -- the function on `S ∪ {‖z‖ ≥ R + 1}`
  set T : Set ℂ := S ∪ {z | R + 1 ≤ ‖z‖} with hT
  set V0 : ℂ → ℂ := fun z => if z ∈ S then h (θof z) else 0 with hV0
  set L : ℝ := max Lc Mh with hL'
  have hL0 : 0 ≤ L := le_max_of_le_left hLc0
  have hfarS : ∀ z ∈ S, ∀ w : ℂ, R + 1 ≤ ‖w‖ → 1 ≤ ‖z - w‖ := by
    intro z hz w hw
    have := hR hz
    rw [mem_closedBall, dist_zero_right] at this
    have := norm_sub_norm_le w z
    rw [norm_sub_rev]; linarith
  have hnotS : ∀ w : ℂ, R + 1 ≤ ‖w‖ → w ∉ S := fun w hw hwS => by
    have := hfarS w hwS w hw; simp at this; linarith
  have hV0S : ∀ z ∈ S, ‖V0 z‖ ≤ Mh := by
    intro z hz
    simp only [hV0, if_pos hz]
    exact hMh _ (hθof z hz).1
  have hV0lip : ∀ z ∈ T, ∀ w ∈ T, ‖V0 z - V0 w‖ ≤ L * ‖z - w‖ := by
    intro z hz w hw
    rcases hz with hzS | hzF <;> rcases hw with hwS | hwF
    · simp only [hV0, if_pos hzS, if_pos hwS]
      obtain ⟨θ, hθ, rfl⟩ := hzS
      obtain ⟨θ', hθ', rfl⟩ := hwS
      rw [hval θ hθ, hval θ' hθ']
      exact (hchord θ hθ θ' hθ').trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · have e : V0 w = 0 := by simp only [hV0, if_neg (hnotS w hwF)]
      rw [e, sub_zero]
      calc ‖V0 z‖ ≤ Mh := hV0S z hzS
        _ ≤ L * 1 := by rw [mul_one]; exact le_max_right _ _
        _ ≤ L * ‖z - w‖ := mul_le_mul_of_nonneg_left (hfarS z hzS w hwF) hL0
    · have e : V0 z = 0 := by simp only [hV0, if_neg (hnotS z hzF)]
      rw [e, zero_sub, norm_neg]
      calc ‖V0 w‖ ≤ Mh := hV0S w hwS
        _ ≤ L * 1 := by rw [mul_one]; exact le_max_right _ _
        _ ≤ L * ‖z - w‖ := by
            rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left (hfarS w hwS z hzF) hL0
    · have e1 : V0 z = 0 := by simp only [hV0, if_neg (hnotS z hzF)]
      have e2 : V0 w = 0 := by simp only [hV0, if_neg (hnotS w hwF)]
      rw [e1, e2, sub_zero, norm_zero]
      positivity
  set Ln : NNReal := ⟨L, hL0⟩ with hLn
  have hre : LipschitzOnWith Ln (fun z => (V0 z).re) T := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [Real.dist_eq, dist_eq_norm, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (hV0lip z hz w hw)
  have him : LipschitzOnWith Ln (fun z => (V0 z).im) T := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [Real.dist_eq, dist_eq_norm, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans (hV0lip z hz w hw)
  obtain ⟨g1, hg1, hg1e⟩ := hre.extend_real
  obtain ⟨g2, hg2, hg2e⟩ := him.extend_real
  refine ⟨fun z => (g1 z : ℂ) + (g2 z : ℂ) * Complex.I, ⟨2 * Ln, ?_⟩, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_eq_norm]
    have e : (g1 z : ℂ) + (g2 z : ℂ) * Complex.I - ((g1 w : ℂ) + (g2 w : ℂ) * Complex.I) =
        ((g1 z - g1 w : ℝ) : ℂ) + ((g2 z - g2 w : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
    have a1 := hg1.dist_le_mul z w
    have a2 := hg2.dist_le_mul z w
    rw [Real.dist_eq] at a1 a2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    push_cast
    linarith
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) fun z hz => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    have hzT : z ∈ T := Or.inr hz.le
    have e1 := hg1e hzT
    have e2 := hg2e hzT
    simp only [hV0, if_neg (hnotS z hz.le), Complex.zero_re, Complex.zero_im] at e1 e2
    rw [← e1, ← e2]
    simp
  · intro θ hθ
    have hm : γ θ ∈ S := mem_image_of_mem γ hθ
    have hzT : γ θ ∈ T := Or.inl hm
    have e1 := hg1e hzT
    have e2 := hg2e hzT
    simp only [hV0, if_pos hm, hval θ hθ] at e1 e2
    show (g1 (γ θ) : ℂ) + (g2 (γ θ) : ℂ) * Complex.I = h θ
    rw [← e1, ← e2]
    exact Complex.re_add_im (h θ)

end PolyaNeumann
