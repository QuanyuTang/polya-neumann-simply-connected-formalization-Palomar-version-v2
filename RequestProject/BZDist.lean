module

public import RequestProject.BoundaryChart
public import RequestProject.LipschitzCover

/-!
# Signed distance and local transversality (towards External theorem BZ)

The signed distance `d_Ω(z) = dist(z, Ωᶜ) - dist(z, Ω)` is positive exactly on `Ω` (for open
`Ω ≠ ℂ`) and `2`-Lipschitz. In a Lipschitz chart at `p` with inward direction `n = conj(c) i`, it
increases at a definite rate along `n` near `p`: `d(z) + t/(2(K+1)) ≤ d(z + t n)`
(`signedDist_add_le_of_chart`).
-/

@[expose] public section

open Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- The signed distance to the boundary, positive inside: `dist(z, Ωᶜ) - dist(z, Ω)`. -/
def signedDist (Ω : Set ℂ) (z : ℂ) : ℝ := infDist z Ωᶜ - infDist z Ω

lemma lipschitzWith_signedDist (Ω : Set ℂ) : LipschitzWith 2 (signedDist Ω) := by
  have h := (lipschitz_infDist_pt (Ωᶜ)).sub (lipschitz_infDist_pt Ω)
  have : ((1 : NNReal) + 1) = 2 := by norm_num
  rw [this] at h
  exact h

lemma continuous_signedDist (Ω : Set ℂ) : Continuous (signedDist Ω) :=
  (lipschitzWith_signedDist Ω).continuous

lemma signedDist_of_mem {Ω : Set ℂ} {z : ℂ} (hz : z ∈ Ω) : signedDist Ω z = infDist z Ωᶜ := by
  simp [signedDist, infDist_zero_of_mem hz]

lemma signedDist_of_notMem {Ω : Set ℂ} {z : ℂ} (hz : z ∉ Ω) : signedDist Ω z = -infDist z Ω := by
  simp [signedDist, infDist_zero_of_mem (show z ∈ Ωᶜ from hz)]

lemma signedDist_nonpos_of_notMem {Ω : Set ℂ} {z : ℂ} (hz : z ∉ Ω) : signedDist Ω z ≤ 0 := by
  rw [signedDist_of_notMem hz]; exact neg_nonpos.mpr infDist_nonneg

lemma signedDist_pos_of_mem {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {z : ℂ}
    (hz : z ∈ Ω) : 0 < signedDist Ω z := by
  rw [signedDist_of_mem hz]
  exact (hΩo.isClosed_compl.notMem_iff_infDist_pos hΩu).mp (fun h => h hz)

lemma signedDist_pos_iff {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {z : ℂ} :
    0 < signedDist Ω z ↔ z ∈ Ω :=
  ⟨fun h => by_contra fun hz => absurd (signedDist_nonpos_of_notMem hz) (not_le.mpr h),
    signedDist_pos_of_mem hΩo hΩu⟩

lemma signedDist_eq_zero_of_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {z : ℂ}
    (hz : z ∈ frontier Ω) : signedDist Ω z = 0 := by
  have hz' : z ∉ Ω := fun h => (hΩo.frontier_eq ▸ hz).2 (hΩo.interior_eq.symm ▸ h)
  rw [signedDist_of_notMem hz', ← infDist_closure,
    infDist_zero_of_mem (frontier_subset_closure hz), neg_zero]

/-- `|d_Ω(z)| ≤ |z - p|` for a boundary point `p` (both distances are dominated). -/
lemma infDist_compl_le_of_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {p z : ℂ}
    (hp : p ∈ frontier Ω) : infDist z Ωᶜ ≤ ‖z - p‖ := by
  have hp' : p ∈ Ωᶜ := fun h => (hΩo.frontier_eq ▸ hp).2 (hΩo.interior_eq.symm ▸ h)
  rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hp'

lemma infDist_le_of_frontier {Ω : Set ℂ} {p z : ℂ} (hp : p ∈ frontier Ω) :
    infDist z Ω ≤ ‖z - p‖ := by
  rw [← infDist_closure, ← dist_eq_norm]; exact infDist_le_dist_of_mem (frontier_subset_closure hp)

/-- The cone property in a chart, in the form used below: a point `q ∈ Ω` of the half box,
shifted by `s` with `‖s - δ n‖ ≤ δ/(2(K+1))`, `n = conj(c) i`, stays in `Ω`. -/
lemma chart_shift_mem {Ω : Set ℂ} {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) {δ : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hδh : δ ≤ h / 3)
    {q : ℂ} (hq : q ∈ Ω) (hqp : ‖q - p‖ < min r h / 2) {s : ℂ}
    (hs : ‖s - δ * (conj c * Complex.I)‖ ≤ δ / (2 * (K + 1))) : q + s ∈ Ω := by
  obtain ⟨hc, hr, hh, hf, -, -, hΩ⟩ := hch
  have hn := norm_mul_sub hc q p
  have hX : |(c * (q - p)).re| < r / 2 :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) (by rw [hn]; linarith [min_le_left r h])
  have hY : |(c * (q - p)).im| < h / 2 :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) (by rw [hn]; linarith [min_le_right r h])
  have hz : -s ∈ closedBall (-(starRingEnd ℂ c) * Complex.I * δ) (δ / (2 * (K + 1))) := by
    rw [mem_closedBall, dist_eq_norm]
    have : -s - -(starRingEnd ℂ c) * Complex.I * δ = -(s - δ * (conj c * Complex.I)) := by ring
    rw [this, norm_neg]; exact hs
  have := chart_segment hc hf hΩ hδ hδr hδh hq hX hY hz (s := 1) ⟨zero_le_one, le_rfl⟩
  simpa using this

/-- Inside the domain: the signed distance increases along the inward direction. -/
lemma signedDist_add_le_of_chart_mem {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty)
    {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) (hp : p ∈ frontier Ω) {z : ℂ} (hzΩ : z ∈ Ω)
    (hz : ‖z - p‖ < min r h / 4) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) (hth : t ≤ h / 3) :
    signedDist Ω z + t / (2 * (K + 1)) ≤ signedDist Ω (z + t * (conj c * Complex.I)) := by
  set n : ℂ := conj c * Complex.I
  set κ : ℝ := 1 / (2 * (K + 1)) with hκ
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 / 2 := by
    rw [hκ]; apply div_le_div_of_nonneg_left <;> nlinarith
  set e := infDist z Ωᶜ with he
  have he0 : 0 < e := (hΩo.isClosed_compl.notMem_iff_infDist_pos hΩu).mp (fun h => h hzΩ)
  have hep : e ≤ ‖z - p‖ := infDist_compl_le_of_frontier hΩo hp
  have htdiv : t / (2 * (K + 1)) = κ * t := by rw [hκ]; ring
  rw [htdiv]
  -- the ball `B(z + t n, e + κ t)` lies in `Ω`
  have hball : ball (z + t * n) (e + κ * t) ⊆ Ω := by
    intro q hq
    rw [mem_ball, dist_eq_norm] at hq
    set u := q - (z + t * n)
    have hpos : 0 < e + κ * t := by positivity
    set q' := z + ((e / (e + κ * t) : ℝ) : ℂ) * u
    have hq'z : ‖q' - z‖ < e := by
      simp only [q', add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg he0.le hpos.le)]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
      exact mul_lt_mul_of_pos_left hq he0
    have hq'Ω : q' ∈ Ω := by
      by_contra hc'
      have := infDist_le_dist_of_mem (x := z) (show q' ∈ Ωᶜ from hc')
      rw [dist_comm, dist_eq_norm] at this
      linarith
    rcases ht0.eq_or_lt with rfl | htp
    · -- `t = 0`: the ball is `B(z, e)`
      have : q = q' := by
        simp only [q', u, Complex.ofReal_zero, zero_mul, add_zero, mul_zero] at *
        rw [div_self he0.ne']; simp
      rw [this]; exact hq'Ω
    have hq'p : ‖q' - p‖ < min r h / 2 := by
      have : ‖q' - p‖ ≤ ‖q' - z‖ + ‖z - p‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle _ _ _
      linarith
    have hs : ‖(q - q') - t * n‖ ≤ t / (2 * (K + 1)) := by
      have hqq : q - q' - t * n = ((κ * t / (e + κ * t) : ℝ) : ℂ) * u := by
        simp only [q', u]
        have : (e / (e + κ * t) : ℝ) = 1 - κ * t / (e + κ * t) := by field_simp; ring
        rw [this]; push_cast; ring
      rw [hqq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), htdiv, div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left hq.le (by positivity)
    have := chart_shift_mem hch htp htr hth hq'Ω hq'p hs
    simpa using this
  have hcen : z + t * n ∈ Ω := hball (mem_ball_self (by positivity))
  rw [signedDist_of_mem hzΩ, signedDist_of_mem hcen]
  rw [le_infDist hΩu]
  intro y hy
  by_contra hlt
  push_neg at hlt
  exact hy (hball (by rw [mem_ball, dist_comm]; exact hlt))

/-- Outside the domain (both ends outside): the signed distance increases along the inward
direction. -/
lemma signedDist_add_le_of_chart_notMem {Ω : Set ℂ} (hΩne : Ω.Nonempty)
    {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) (hp : p ∈ frontier Ω) {z : ℂ} {t : ℝ}
    (hzΩ : z ∉ Ω) (hwΩ : z + t * (conj c * Complex.I) ∉ Ω)
    (hz : ‖z - p‖ < min r h / 10) (ht0 : 0 ≤ t) (htr : t ≤ min r h / 10) :
    signedDist Ω z + t / (2 * (K + 1)) ≤ signedDist Ω (z + t * (conj c * Complex.I)) := by
  set n : ℂ := conj c * Complex.I
  have hn1 : ‖n‖ = 1 := by
    simp [n, hch.1]
  set κ : ℝ := 1 / (2 * (K + 1)) with hκ
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 / 2 := by
    rw [hκ]; apply div_le_div_of_nonneg_left <;> nlinarith
  have htdiv : t / (2 * (K + 1)) = κ * t := by rw [hκ]; ring
  rw [htdiv, signedDist_of_notMem hzΩ, signedDist_of_notMem hwΩ]
  rcases ht0.eq_or_lt with rfl | htp
  · simp
  set w := z + t * n
  set e := infDist w Ω with he
  have he0 : 0 ≤ e := infDist_nonneg
  have hwp : ‖w - p‖ ≤ ‖z - p‖ + t := by
    have : w - p = (z - p) + t * n := by simp only [w]; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hn1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, mul_one]
  have hep : e ≤ ‖w - p‖ := infDist_le_of_frontier hp
  have hpos : 0 < e + κ * t := by positivity
  -- the ball `B(z, e + κ t)` misses `Ω`
  have hball : ∀ q ∈ ball z (e + κ * t), q ∉ Ω := by
    intro q hq hqΩ
    rw [mem_ball, dist_eq_norm] at hq
    set u := q - z
    set q' := w + ((e / (e + κ * t) : ℝ) : ℂ) * u
    have hq'w : dist q' w < e ∨ e = 0 := by
      rcases he0.eq_or_lt with h0 | h0
      · exact Or.inr h0.symm
      left
      rw [dist_eq_norm]
      simp only [q', add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg he0 hpos.le)]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
      exact mul_lt_mul_of_pos_left hq h0
    have hq'Ω : q' ∉ Ω := by
      rcases hq'w with h1 | h1
      · intro hm
        have := infDist_le_dist_of_mem (x := w) hm
        rw [dist_comm] at this; linarith
      · have : q' = w := by simp [q', h1]
        rw [this]; exact hwΩ
    have hqp : ‖q - p‖ < min r h / 2 := by
      have : ‖q - p‖ ≤ ‖q - z‖ + ‖z - p‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle _ _ _
      have : e + κ * t ≤ ‖z - p‖ + t + t / 2 := by nlinarith
      linarith
    have hs : ‖(q' - q) - t * n‖ ≤ t / (2 * (K + 1)) := by
      have hqq : q' - q - t * n = -(((κ * t / (e + κ * t) : ℝ) : ℂ) * u) := by
        simp only [q', u, w]
        have : (e / (e + κ * t) : ℝ) = 1 - κ * t / (e + κ * t) := by field_simp; ring
        rw [this]; push_cast; ring
      rw [hqq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), htdiv, div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left hq.le (by positivity)
    have htr' : t ≤ r := by linarith [min_le_left r h]
    have hth' : t ≤ h / 3 := by linarith [min_le_right r h]
    have := chart_shift_mem hch htp htr' hth' hqΩ hqp hs
    simp only [add_sub_cancel] at this
    exact hq'Ω this
  have : e + κ * t ≤ infDist z Ω := by
    rw [le_infDist hΩne]
    intro y hy
    by_contra hlt
    push_neg at hlt
    exact hball y (by rw [mem_ball, dist_comm]; exact hlt) hy
  linarith

/-- **Local transversality.** In a Lipschitz chart at the boundary point `p` with inward
direction `n = conj(c) i`, for `‖z - p‖ < min r h / 10` and `0 ≤ t ≤ min r h / 10`,
`d_Ω(z) + t/(2(K+1)) ≤ d_Ω(z + t n)`. -/
theorem signedDist_add_le_of_chart {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩu : Ωᶜ.Nonempty) {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) (hp : p ∈ frontier Ω) {z : ℂ}
    (hz : ‖z - p‖ < min r h / 10) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ min r h / 10) :
    signedDist Ω z + t / (2 * (K + 1)) ≤ signedDist Ω (z + t * (conj c * Complex.I)) := by
  set n : ℂ := conj c * Complex.I
  have hn1 : ‖n‖ = 1 := by simp [n, hch.1]
  have hr := hch.2.1
  have hh := hch.2.2.1
  have hmin : 0 < min r h := lt_min hr hh
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hpt : ∀ s : ℝ, 0 ≤ s → ‖z + s * n - p‖ ≤ ‖z - p‖ + s := fun s hs => by
    have : z + s * n - p = (z - p) + s * n := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hn1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, mul_one]
  by_cases hzΩ : z ∈ Ω
  · exact signedDist_add_le_of_chart_mem hΩo hΩu hch hp hzΩ (by linarith) ht0
      (by linarith [min_le_left r h]) (by linarith [min_le_right r h])
  by_cases hwΩ : z + t * n ∈ Ω
  swap
  · exact signedDist_add_le_of_chart_notMem hΩne hch hp hzΩ hwΩ hz ht0 htr
  -- mixed case: cross the boundary at the last time `t₁` outside `Ω`
  set S : Set ℝ := {s | s ∈ Icc 0 t ∧ z + s * n ∉ Ω}
  have hSc : IsClosed S := by
    refine isClosed_Icc.inter ?_
    exact hΩo.isClosed_compl.preimage (by fun_prop)
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht0⟩, by simpa using hzΩ⟩
  have hSb : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
  set t₁ := sSup S
  have ht₁S : t₁ ∈ S := hSc.csSup_mem ⟨0, hS0⟩ hSb
  have ht₁0 : 0 ≤ t₁ := ht₁S.1.1
  have ht₁t : t₁ ≤ t := ht₁S.1.2
  have hlt : t₁ < t := lt_of_le_of_ne ht₁t (fun h => ht₁S.2 (h ▸ hwΩ))
  -- outside part
  have h1 : signedDist Ω z + t₁ / (2 * (K + 1)) ≤ signedDist Ω (z + t₁ * n) :=
    signedDist_add_le_of_chart_notMem hΩne hch hp hzΩ ht₁S.2 hz ht₁0 (by linarith)
  have h1' : signedDist Ω (z + t₁ * n) ≤ 0 := signedDist_nonpos_of_notMem ht₁S.2
  -- inside part: from every later time
  have h2 : ∀ s ∈ Ioc t₁ t, (t - s) / (2 * (K + 1)) ≤ signedDist Ω (z + t * n) := by
    intro s hs
    have hsΩ : z + s * n ∈ Ω := by
      by_contra hc'
      exact absurd (le_csSup hSb ⟨⟨by linarith [hs.1], hs.2⟩, hc'⟩) (not_le.mpr hs.1)
    have hm := signedDist_add_le_of_chart_mem hΩo hΩu hch hp hsΩ
      (by have := hpt s (by linarith [hs.1]); linarith [hs.2]) (t := t - s) (by linarith [hs.2])
      (by linarith [min_le_left r h, hs.1]) (by linarith [min_le_right r h, hs.1])
    have heq : z + s * n + ((t - s : ℝ) : ℂ) * n = z + t * n := by push_cast; ring
    rw [heq] at hm
    have := signedDist_pos_of_mem hΩo hΩu hsΩ
    linarith
  have h2' : (t - t₁) / (2 * (K + 1)) ≤ signedDist Ω (z + t * n) := by
    have hcont : ContinuousWithinAt (fun s : ℝ => (t - s) / (2 * (K + 1))) (Ioc t₁ t) t₁ :=
      (by fun_prop : Continuous fun s : ℝ => (t - s) / (2 * (K + 1))).continuousWithinAt
    have hcl : t₁ ∈ closure (Ioc t₁ t) := by
      rw [closure_Ioc hlt.ne]; exact ⟨le_rfl, ht₁t⟩
    exact ContinuousWithinAt.closure_le hcl hcont continuousWithinAt_const
      (fun s hs => h2 s hs)
  have : t / (2 * (K + 1)) = t₁ / (2 * (K + 1)) + (t - t₁) / (2 * (K + 1)) := by ring
  linarith

end PolyaNeumann

end
