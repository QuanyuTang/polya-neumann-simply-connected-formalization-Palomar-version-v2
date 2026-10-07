module

public import RequestProject.LocalConformalRegularPrincipal
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform bounds for the actual regular principal factor

The fixed-complement inverse is continuous on a genuine neighbourhood of
the reference energy. Restricting to a smaller closed interval bounds the
one-derivative factor of the actual regular Neumann operator uniformly.
The supplied conformal coordinates still require their separate existence
theorem. This file does not assert a boundary lower bound.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter
open scoped Topology

private theorem norm_bounded_on_smaller_neighbourhood
    {V : Type*} [NormedAddCommGroup V] {x : ℝ} {U : Set ℝ}
    (hU : U ∈ 𝓝 x) (f : ℝ → V) (hf : ContinuousOn f U) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧
      ∀ y, |y - x| < δ → y ∈ U ∧ ‖f y‖ ≤ M := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδe : δ < ε := by dsimp only [δ]; linarith
  have hsub : closedBall x δ ⊆ U := by
    intro y hy
    apply hεU
    exact mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hδe)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x δ).exists_bound_of_continuousOn
    (hf.mono hsub)
  refine ⟨δ, max M 0 + 1, hδ, by positivity, ?_⟩
  intro y hy
  have hyb : y ∈ closedBall x δ := by
    apply mem_closedBall.mpr
    simpa only [Real.dist_eq] using hy.le
  exact ⟨hsub hyb, (hM y hyb).trans (by linarith [le_max_left M 0])⟩

private theorem norm_bound_near_inverse
    {A : Type*} [MonoidWithZero A] [TopologicalSpace A]
    {V : Type*} [NormedAddCommGroup V] (B : ℝ → A) (E₀ : ℝ)
    (hnear : ∃ U ∈ 𝓝 E₀, (∀ E ∈ U, IsUnit (B E)) ∧
      ContinuousOn (fun E => Ring.inverse (B E)) U)
    (f : ℝ → V)
    (hcont : ∀ U : Set ℝ,
      ContinuousOn (fun E => Ring.inverse (B E)) U → ContinuousOn f U) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ E, |E - E₀| < δ →
      IsUnit (B E) ∧ ‖f E‖ ≤ M := by
  obtain ⟨U, hU, hu, hi⟩ := hnear
  obtain ⟨δ, M, hδ, hM, hbound⟩ :=
    norm_bounded_on_smaller_neighbourhood hU f (hcont U hi)
  exact ⟨δ, M, hδ, hM, fun E hE =>
    ⟨hu E (hbound E hE).1, (hbound E hE).2⟩⟩

/-- The actual regular principal factor stays bounded in operator norm
on a neighbourhood where the actual complement form is invertible. -/
theorem exists_localConformalRegularPrincipalFactor_bound
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) {K : ℝ}
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ E, |E - E₀| < δ →
      IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E) ∧
        ‖localConformalRegularPrincipalFactor hR F hFs hL hK E₀ E‖ ≤ M := by
  exact norm_bound_near_inverse (V := L2Z →L[ℂ] L2Z)
    (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀) E₀
    (h1ComplementForm_isUnit_near (Ω := F '' ball (0 : ℂ) 1) (E₀ := E₀) hb hL hE₀)
    (localConformalRegularPrincipalFactor hR F hFs hL hK E₀)
    (fun U hi => continuousOn_localConformalRegularPrincipalFactor
      hR F hFs hL hK (U := U) (E₀ := E₀) hi)

end PolyaNeumann

end
