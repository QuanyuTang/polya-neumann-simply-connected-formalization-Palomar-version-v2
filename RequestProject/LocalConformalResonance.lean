module

public import RequestProject.LocalConformalTrace
public import RequestProject.TraceReparamReverse
public import RequestProject.NeumannResidueRank

/-!
# Genuine Neumann resonance traces in given conformal coordinates

The actual half-order conformal trace vanishes precisely when the
ordinary conformal trace vanishes. A proved physical reparametrization
then identifies this condition with zero physical trace. The resulting
residue rank is the original complex Neumann spectral multiplicity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped Real

private theorem halfOrderFourier_eq_zero_iff (v : L2Z) (g : BoundaryL2)
    (hcoeff : ∀ n : ℤ, v n = (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
      boundaryFourier g n) : v = 0 ↔ g = 0 := by
  constructor
  · intro hv
    apply boundaryFourier.injective
    apply lp.ext
    funext n
    have hs : (Real.sqrt (1 + |(n : ℝ)|) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 1 + |(n : ℝ)|)).ne'
    have h := hcoeff n
    rw [hv] at h
    simp only [lp.coeFn_zero, Pi.zero_apply] at h
    have hn := (mul_eq_zero.mp h.symm).resolve_left hs
    simpa only [map_zero, lp.coeFn_zero, Pi.zero_apply] using hn
  · intro hg
    apply lp.ext
    funext n
    rw [hcoeff n, hg, map_zero]
    simp only [lp.coeFn_zero, Pi.zero_apply, mul_zero]

theorem localConformalDiskHalfTrace_eq_zero_iff {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    localConformalDiskHalfTrace hR F hFs hL u = 0 ↔
      localConformalDiskH1Trace hR F hFs hL u = 0 := by
  exact halfOrderFourier_eq_zero_iff _ _
    (fun n => localConformalDiskHalfTrace_apply hR F hFs hL u n)

section PhysicalCoordinate

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hb hhol hinj hC hγ hτ hcoord in
theorem localConformalDiskHalfTrace_eq_zero_iff_physical
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    localConformalDiskHalfTrace hR F hFs hL u = 0 ↔
      h1BoundaryTrace hb hL hγ u = 0 := by
  rw [localConformalDiskHalfTrace_eq_zero_iff,
    ← localConformalDiskH1Trace_eq_reparam hR F hFs hb hL hhol hinj hC hγ hτ hcoord]
  exact h1ReparamBoundaryTrace_eq_zero_iff hb hL hγ hτ u

def neumannLocalConformalResonantTrace (E : ℝ) :
    h1ResonantSpace (F '' ball (0 : ℂ) 1) E →L[ℂ] L2Z :=
  (localConformalDiskHalfTrace hR F hFs hL).comp
    (h1ResonantSpace (F '' ball (0 : ℂ) 1) E).subtypeL

include hb hhol hinj hC hγ hτ hcoord in
theorem neumannLocalConformalResonantTrace_injective {E : ℝ} (hE : 0 ≤ E) :
    Function.Injective (neumannLocalConformalResonantTrace hR F hFs hL E) := by
  intro u v huv
  apply neumannResonantTrace_injective_nonneg hb hL hγ hE
  change h1BoundaryTrace hb hL hγ (u : NeumannH1 (F '' ball (0 : ℂ) 1)) =
    h1BoundaryTrace hb hL hγ (v : NeumannH1 (F '' ball (0 : ℂ) 1))
  have hzero : localConformalDiskHalfTrace hR F hFs hL
      ((u : NeumannH1 (F '' ball (0 : ℂ) 1)) - (v : NeumannH1 (F '' ball (0 : ℂ) 1))) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr huv
  have hp := (localConformalDiskHalfTrace_eq_zero_iff_physical hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord _).mp hzero
  rw [map_sub] at hp
  exact sub_eq_zero.mp hp

def neumannLocalConformalResidue (E : ℝ) : L2Z →L[ℂ] L2Z :=
  ((E + 1 : ℝ) : ℂ) •
    ((localConformalDiskHalfTrace hR F hFs hL).comp
      ((h1ResonantSpace (F '' ball (0 : ℂ) 1) E).starProjection.comp
        (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL))))

include hb hhol hinj hC hγ hτ hcoord in
theorem neumannLocalConformalResidue_range_eq {E : ℝ} (hE : 0 ≤ E) :
    (neumannLocalConformalResidue hR F hFs hL E).range =
      (neumannLocalConformalResonantTrace hR F hFs hL E).range := by
  haveI := finiteDimensional_h1ResonantSpace hb hL E
  have hc : ((E + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show E + 1 ≠ 0 by linarith)
  exact range_scaled_projected_trace_gram (h1ResonantSpace (F '' ball (0 : ℂ) 1) E)
    (localConformalDiskHalfTrace hR F hFs hL)
    (neumannLocalConformalResonantTrace_injective hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE) hc

include hb hhol hinj hC hγ hτ hcoord in
theorem neumannLocalConformalResidue_multiplicity_eq {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (neumannLocalConformalResidue hR F hFs hL E).range : ℕ∞) =
      {j : ℕ | neumannEigenvalue (F '' ball (0 : ℂ) 1) j = ENNReal.ofReal E}.encard := by
  rw [neumannLocalConformalResidue_range_eq hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE,
    LinearMap.finrank_range_of_inj
      (neumannLocalConformalResonantTrace_injective hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE)]
  exact h1ResonantSpace_multiplicity_eq hb hL hE

end PhysicalCoordinate

end PolyaNeumann

end
