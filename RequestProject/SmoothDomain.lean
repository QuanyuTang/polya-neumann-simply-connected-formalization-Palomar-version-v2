module

public import RequestProject.Defs

/-!
# Smooth domains

`IsSmoothDomain Ω`: a domain whose boundary is locally the graph of a `C^∞` function (with the
domain on one side); such domains are Lipschitz domains (`IsSmoothDomain.isLipschitzDomain`).
-/

@[expose] public section

open scoped Real ComplexConjugate
open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-- A smooth domain: a domain whose boundary is locally, after a rigid change of
coordinates, the graph of a `C^∞` function (which, after shrinking the chart, may be taken
to be globally Lipschitz), with the domain on one side. -/
def IsSmoothDomain (Ω : Set ℂ) : Prop :=
  IsDomain Ω ∧
  ∀ p ∈ frontier Ω, ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
    ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧ LipschitzWith K f ∧ f 0 = 0 ∧
    (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im)

lemma IsSmoothDomain.isLipschitzDomain {Ω : Set ℂ} (h : IsSmoothDomain Ω) :
    IsLipschitzDomain Ω := by
  refine ⟨h.1, fun p hp => ?_⟩
  obtain ⟨c, r, k, K, f, hc, hr, hk, -, hf, h0, hb, hΩ⟩ := h.2 p hp
  exact ⟨c, r, k, K, f, hc, hr, hk, hf, h0, hb, hΩ⟩

end PolyaNeumann

end
