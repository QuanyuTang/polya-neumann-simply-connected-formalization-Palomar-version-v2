module

public import RequestProject.BZFlow

/-!
# Monotonicity along flow lines and crossing times (towards External theorem BZ)

If a Lipschitz function `φ` increases at rate `κ` along the straight segments `t ↦ z + t X(z)`
for `z` in a region `U`, then it increases at rate `κ/2` along the flow lines of `X` that stay in
`U` (`IsShortFlow.le_of_transversal`). Consequently every level `λ` of `φ` is crossed exactly once
by such a flow line (`IsShortFlow.existsUnique_crossing`), and the crossing time depends in a
Lipschitz way on the initial point (`IsShortFlow.abs_crossing_sub_le`).
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

noncomputable section

namespace PolyaNeumann

variable {X : ℂ → ℂ} {LX : ℝ≥0} {M : ℝ} {Φ : ℝ → ℂ → ℂ}

/-- Straight-line transversality of `φ` along `X` in the region `U`, at rate `κ` up to time
`τ`. -/
def IsTransversalOn (φ : ℂ → ℝ) (X : ℂ → ℂ) (U : Set ℂ) (τ κ : ℝ) : Prop :=
  ∀ z ∈ U, ∀ t, 0 ≤ t → t ≤ τ → φ z + κ * t ≤ φ (z + t * X z)

/-- Monotonicity of a transversal function along flow lines. -/
theorem IsShortFlow.le_of_transversal (hΦ : IsShortFlow X Φ) (hX : LipschitzWith LX X)
    (hM : ∀ z, ‖X z‖ ≤ M) {φ : ℂ → ℝ} {Lφ : ℝ≥0} (hφ : LipschitzWith Lφ φ) {U : Set ℂ}
    {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hQ : IsTransversalOn φ X U τ κ) (x : ℂ) {s t : ℝ}
    (hs : -1 < s) (hst : s ≤ t) (ht : t < 1) (hU : ∀ u ∈ Icc s t, Φ u x ∈ U) :
    φ (Φ s x) + κ / 2 * (t - s) ≤ φ (Φ t x) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsub : Icc s t ⊆ Ioo (-3 : ℝ) 3 := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  set f : ℝ → ℝ := fun u => φ (Φ s x) - φ (Φ u x)
  have hfc : ContinuousOn f (Icc s t) :=
    continuousOn_const.sub (hφ.continuous.comp_continuousOn ((hΦ.continuousOn x).mono hsub))
  set C : ℝ := Lφ * LX * M
  have hC : 0 ≤ C := by positivity
  have hf' : ∀ u ∈ Ico s t, ∀ r, -κ < r → ∃ᶠ z in 𝓝[>] u, slope f u z < r := by
    intro u hu r hr
    refine Filter.Eventually.frequently ?_
    set δ : ℝ := min (min τ 1) ((r + κ) / (C + 1))
    have hδ : 0 < δ := lt_min (lt_min hτ one_pos) (div_pos (by linarith) (by positivity))
    filter_upwards [Ioo_mem_nhdsGT (show u < u + δ by linarith)] with z hz
    set h := z - u
    have hh0 : 0 < h := by simp only [h]; linarith [hz.1]
    have hhδ : h < δ := by simp only [h]; linarith [hz.2]
    have hhτ : h ≤ τ := hhδ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hh1 : h < 1 := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_right _ _))
    have hhr : (C + 1) * h < r + κ := by
      have := lt_of_lt_of_le hhδ (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at this; linarith
    set y := Φ u x
    have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hzy : Φ z x = Φ h y := by
      rw [hΦ.add hX x ⟨by linarith, by linarith⟩ hu1]; congr 1; simp [h]
    have hyU : y ∈ U := hU u (Ico_subset_Icc_self hu)
    have h1 := hQ y hyU h hh0.le hhτ
    have h2 : |φ (Φ h y) - φ (y + h * X y)| ≤ Lφ * ‖Φ h y - (y + h * X y)‖ := by
      rw [← Real.dist_eq, ← dist_eq_norm]; exact hφ.dist_le_mul _ _
    have h3 : ‖Φ h y - (y + h * X y)‖ ≤ LX * M * h ^ 2 := by
      have := hΦ.norm_sub_sub_le hX hM y (t := h) ⟨by linarith, by linarith⟩
      rwa [show Φ h y - y - h * X y = Φ h y - (y + h * X y) by ring] at this
    have h4 : φ (Φ h y) ≥ φ y + κ * h - C * h ^ 2 := by
      have := neg_abs_le (φ (Φ h y) - φ (y + h * X y))
      have h5 : Lφ * ‖Φ h y - (y + h * X y)‖ ≤ C * h ^ 2 := by
        simp only [C]; rw [mul_assoc (Lφ : ℝ), mul_assoc (Lφ : ℝ)]
        exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using h3) Lφ.2
      linarith
    rw [slope_def_field]
    simp only [f]
    rw [hzy, div_lt_iff₀ hh0]
    have : C * h ^ 2 < (r + κ) * h := by
      have : C * h ≤ (C + 1) * h := by nlinarith
      nlinarith
    nlinarith
  have := image_le_of_liminf_slope_right_lt_deriv_boundary' hfc hf'
    (B := fun u => -(κ / 2) * (u - s)) (B' := fun _ => -(κ / 2)) (by simp [f])
    (by fun_prop) (fun u _ => by
      simpa using ((hasDerivAt_id u).sub_const s |>.const_mul (-(κ / 2))).hasDerivWithinAt)
    (fun _ _ _ => by linarith) ⟨hst, le_rfl⟩
  simp only [f] at this
  linarith

/-- Strict monotonicity along a flow line staying in the region. -/
lemma IsShortFlow.lt_of_transversal (hΦ : IsShortFlow X Φ) (hX : LipschitzWith LX X)
    (hM : ∀ z, ‖X z‖ ≤ M) {φ : ℂ → ℝ} {Lφ : ℝ≥0} (hφ : LipschitzWith Lφ φ) {U : Set ℂ}
    {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hQ : IsTransversalOn φ X U τ κ) (x : ℂ) {s t : ℝ}
    (hs : -1 < s) (hst : s < t) (ht : t < 1) (hU : ∀ u ∈ Icc s t, Φ u x ∈ U) :
    φ (Φ s x) < φ (Φ t x) := by
  have := hΦ.le_of_transversal hX hM hφ hτ hκ hQ x hs hst.le ht hU
  have : 0 < κ / 2 * (t - s) := by have := sub_pos.mpr hst; positivity
  linarith

/-- Existence and uniqueness of the crossing time of a level. -/
theorem IsShortFlow.existsUnique_crossing (hΦ : IsShortFlow X Φ) (hX : LipschitzWith LX X)
    (hM : ∀ z, ‖X z‖ ≤ M) {φ : ℂ → ℝ} {Lφ : ℝ≥0} (hφ : LipschitzWith Lφ φ) {U : Set ℂ}
    {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hQ : IsTransversalOn φ X U τ κ) {T₁ : ℝ}
    (hT₁ : 0 < T₁) (hT₁1 : T₁ < 1) (x : ℂ) (hU : ∀ u ∈ Icc (-T₁) T₁, Φ u x ∈ U) {l : ℝ}
    (hlo : l - κ / 2 * T₁ ≤ φ x) (hhi : φ x ≤ l + κ / 2 * T₁) :
    ∃! u, u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l := by
  have hsub : Icc (-T₁) T₁ ⊆ Ioo (-3 : ℝ) 3 := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hg : ContinuousOn (fun u => φ (Φ u x)) (Icc (-T₁) T₁) :=
    hφ.continuous.comp_continuousOn ((hΦ.continuousOn x).mono hsub)
  have h1 := hΦ.le_of_transversal hX hM hφ hτ hκ hQ x (s := -T₁) (t := 0) (by linarith)
    (by linarith) (by norm_num) (fun u hu => hU u ⟨hu.1, by linarith [hu.2]⟩)
  have h2 := hΦ.le_of_transversal hX hM hφ hτ hκ hQ x (s := 0) (t := T₁) (by norm_num)
    hT₁.le hT₁1 (fun u hu => hU u ⟨by linarith [hu.1], hu.2⟩)
  rw [hΦ.zero] at h1 h2
  obtain ⟨u, hu, hul⟩ := intermediate_value_Icc (by linarith) hg
    (show l ∈ Icc (φ (Φ (-T₁) x)) (φ (Φ T₁ x)) from ⟨by linarith, by linarith⟩)
  refine ⟨u, ⟨hu, hul⟩, fun v ⟨hv, hvl⟩ => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hΦ.lt_of_transversal hX hM hφ hτ hκ hQ x (by linarith [hv.1]) h
      (by linarith [hu.2]) (fun w hw => hU w ⟨by linarith [hv.1, hw.1], by linarith [hu.2, hw.2]⟩)
    simp only at hul; linarith
  · have := hΦ.lt_of_transversal hX hM hφ hτ hκ hQ x (by linarith [hu.1]) h
      (by linarith [hv.2]) (fun w hw => hU w ⟨by linarith [hu.1, hw.1], by linarith [hv.2, hw.2]⟩)
    simp only at hul; linarith

/-- Lipschitz dependence of crossing times on the initial point. -/
theorem IsShortFlow.abs_crossing_sub_le (hΦ : IsShortFlow X Φ) (hX : LipschitzWith LX X)
    (hM : ∀ z, ‖X z‖ ≤ M) {φ : ℂ → ℝ} {Lφ : ℝ≥0} (hφ : LipschitzWith Lφ φ) {U : Set ℂ}
    {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hQ : IsTransversalOn φ X U τ κ) {T₁ : ℝ}
    (hT₁1 : T₁ < 1) {x y : ℂ} (hUy : ∀ u ∈ Icc (-T₁) T₁, Φ u y ∈ U) {l u v : ℝ}
    (hu : u ∈ Icc (-T₁) T₁) (hv : v ∈ Icc (-T₁) T₁) (hxu : φ (Φ u x) = l)
    (hyv : φ (Φ v y) = l) :
    κ / 2 * |u - v| ≤ Lφ * Real.exp LX * ‖x - y‖ := by
  have hd : |φ (Φ u y) - φ (Φ u x)| ≤ Lφ * Real.exp LX * ‖x - y‖ := by
    have h1 : |φ (Φ u y) - φ (Φ u x)| ≤ Lφ * dist (Φ u y) (Φ u x) := by
      rw [← Real.dist_eq]; exact hφ.dist_le_mul _ _
    have h2 := hΦ.dist_le hX y x (t := u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h3 : Real.exp (LX * |u|) ≤ Real.exp LX := by
      apply Real.exp_le_exp.mpr
      have hu1 : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
      exact mul_le_of_le_one_right LX.2 hu1
    rw [dist_comm y x, dist_eq_norm x y] at h2
    calc |φ (Φ u y) - φ (Φ u x)| ≤ Lφ * (‖x - y‖ * Real.exp (LX * |u|)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 Lφ.2)
      _ ≤ Lφ * (‖x - y‖ * Real.exp LX) := by gcongr
      _ = Lφ * Real.exp LX * ‖x - y‖ := by ring
  rcases le_total u v with h | h
  · have := hΦ.le_of_transversal hX hM hφ hτ hκ hQ y (by linarith [hu.1]) h (by linarith [hv.2])
      (fun w hw => hUy w ⟨by linarith [hu.1, hw.1], by linarith [hv.2, hw.2]⟩)
    rw [abs_of_nonpos (by linarith)]
    have := (abs_le.mp hd).1
    linarith
  · have := hΦ.le_of_transversal hX hM hφ hτ hκ hQ y (by linarith [hv.1]) h (by linarith [hu.2])
      (fun w hw => hUy w ⟨by linarith [hv.1, hw.1], by linarith [hu.2, hw.2]⟩)
    rw [abs_of_nonneg (by linarith)]
    have := (abs_le.mp hd).2
    linarith

end PolyaNeumann

end
