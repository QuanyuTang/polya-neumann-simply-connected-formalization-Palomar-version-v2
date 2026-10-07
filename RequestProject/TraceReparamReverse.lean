module

public import RequestProject.TraceReparam

/-!
# Two-sided ordinary trace bounds under a proved reparametrization

The upper Jacobian bound gives the reverse coordinate L² estimate.
Both estimates extend to the actual H¹ traces by density. In particular,
zero trace is independent of this change of parameter, without assuming
an inverse parameter map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Real

theorem integral_sq_traceReparam_reverse_le {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) {K : NNReal} (hK : LipschitzWith K τ)
    {q : ℝ → ℂ} (hq : Continuous q) :
    (∫ s in (0 : ℝ)..(2 * π), ‖q s‖ ^ 2) ≤
      (K : ℝ) * ∫ θ in (0 : ℝ)..(2 * π), ‖q (τ θ)‖ ^ 2 := by
  have hQ : Continuous (fun s => ‖q s‖ ^ 2) := hq.norm.pow 2
  have hQt : Continuous (fun θ => ‖q (τ θ)‖ ^ 2) := hQ.comp hτ.continuous
  have hd : Continuous (deriv τ) := hτ.contDiff.continuous_deriv_one
  have hJ : (∫ θ in (0 : ℝ)..(2 * π), ‖q (τ θ)‖ ^ 2 * deriv τ θ) =
      ∫ s in (0 : ℝ)..(2 * π), ‖q s‖ ^ 2 := by
    have h := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := 2 * π)
      (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt)
      hd.continuousOn hQ
    simpa only [Function.comp_apply, hτ.zero, hτ.endpoint] using h
  rw [← hJ, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * π)
    ((hQt.mul hd).intervalIntegrable _ _)
    ((continuous_const.mul hQt).intervalIntegrable _ _) ?_
  intro θ
  have hder : deriv τ θ ≤ (K : ℝ) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      (norm_deriv_le_of_lipschitz hK : ‖deriv τ θ‖ ≤ (K : ℝ)))
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hder (sq_nonneg ‖q (τ θ)‖)

theorem h1BoundaryTrace_sq_le_reparam {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    {K : NNReal} (hK : LipschitzWith K τ) (u : NeumannH1 Ω) :
    ‖h1BoundaryTrace hb hL hγ u‖ ^ 2 ≤
      (K : ℝ) * ‖h1ReparamBoundaryTrace hL hγ hτ u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => ‖h1BoundaryTrace hb hL hγ v‖ ^ 2 ≤
      (K : ℝ) * ‖h1ReparamBoundaryTrace hL hγ hτ v‖ ^ 2) u ?_ ?_
  · exact isClosed_le ((h1BoundaryTrace hb hL hγ).continuous.norm.pow 2)
      (continuous_const.mul ((h1ReparamBoundaryTrace hL hγ hτ).continuous.norm.pow 2))
  · intro f
    change ‖h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f)‖ ^ 2 ≤
      (K : ℝ) * ‖h1ReparamBoundaryTrace hL hγ hτ (smoothTraceH1 Ω f)‖ ^ 2
    rw [h1BoundaryTrace_smooth hb hL hγ, h1ReparamBoundaryTrace_smooth hb hL hγ hτ,
      norm_sq_smoothTraceBoundary, norm_sq_smoothReparamBoundary]
    obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
    exact integral_sq_traceReparam_reverse_le hτ hK (f.property.1.continuous.comp hKγ.continuous)

theorem h1ReparamBoundaryTrace_sq_le {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) (u : NeumannH1 Ω) :
    ‖h1ReparamBoundaryTrace hL hγ hτ u‖ ^ 2 ≤
      (1 / c) * ‖h1BoundaryTrace hb hL hγ u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => ‖h1ReparamBoundaryTrace hL hγ hτ v‖ ^ 2 ≤
      (1 / c) * ‖h1BoundaryTrace hb hL hγ v‖ ^ 2) u ?_ ?_
  · exact isClosed_le ((h1ReparamBoundaryTrace hL hγ hτ).continuous.norm.pow 2)
      (continuous_const.mul ((h1BoundaryTrace hb hL hγ).continuous.norm.pow 2))
  · intro f
    change ‖h1ReparamBoundaryTrace hL hγ hτ (smoothTraceH1 Ω f)‖ ^ 2 ≤
      (1 / c) * ‖h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f)‖ ^ 2
    rw [h1BoundaryTrace_smooth hb hL hγ, h1ReparamBoundaryTrace_smooth hb hL hγ hτ,
      norm_sq_smoothTraceBoundary, norm_sq_smoothReparamBoundary]
    obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
    exact integral_sq_comp_traceReparam_le hτ (f.property.1.continuous.comp hKγ.continuous)

theorem h1ReparamBoundaryTrace_eq_zero_iff {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) (u : NeumannH1 Ω) :
    h1ReparamBoundaryTrace hL hγ hτ u = 0 ↔ h1BoundaryTrace hb hL hγ u = 0 := by
  constructor
  · intro hu
    obtain ⟨K, hK⟩ := hτ.lipschitz
    have h := h1BoundaryTrace_sq_le_reparam hb hL hγ hτ hK u
    rw [hu, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (h1BoundaryTrace hb hL hγ u)])
  · intro hu
    have h := h1ReparamBoundaryTrace_sq_le hb hL hγ hτ u
    rw [hu, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (h1ReparamBoundaryTrace hL hγ hτ u)])

end PolyaNeumann

end
