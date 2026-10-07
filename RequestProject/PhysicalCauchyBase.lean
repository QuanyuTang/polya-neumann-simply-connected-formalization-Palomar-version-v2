module

public import RequestProject.PhysicalMomentPrimitive

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory
open scoped ComplexConjugate

/-- The weighted integral with the same denominator sign as winding number. -/
def physicalWeightedCauchy (γ K : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv γ θ * K θ) / (γ θ - z)

/-- The ordinary transform previously used for exterior analyticity has the
opposite denominator.  This exact identity records both that sign and the
conjugation of its physical density. -/
theorem physicalOrdinaryCauchy_eq_neg_weighted (γ H : ℝ → ℂ) (w : ℂ) :
    physicalOrdinaryCauchy γ H w =
      -physicalWeightedCauchy γ (fun θ => conj (H θ)) w := by
  rw [physicalOrdinaryCauchy, physicalWeightedCauchy, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro θ _
  change (deriv γ θ * conj (H θ)) / (w - γ θ) =
    -((deriv γ θ * conj (H θ)) / (γ θ - w))
  rw [show w - γ θ = -(γ θ - w) by ring, div_neg]

end PolyaNeumann

end
