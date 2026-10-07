module

public import RequestProject.LocalConformalRegularObservation
public import RequestProject.Reconstruction

/-!
# Actual Herglotz conormal span and the remaining density obligation

The compatibility space below is the orthogonal complement of the
actual normalized traces of the original Neumann resonant space. Every
actual Herglotz conormal belongs to it, and so does their closed span.
The exact full-density assertion is equivalent to the reverse Cauchy
annihilator statement: every normalized vector annihilating all actual
Herglotz conormals must lie in the closure of that resonant trace range.

The repository's genuine Cauchy reconstruction theorem applies to
`compatibleTraces`, whose definition explicitly requires a Lipschitz
representative and periodic endpoints. It gives an injective map into
the original Neumann eigenspace. It does not identify all H1/2
annihilators, and its stated conclusion does not identify the general
reconstructed trace with the supplied trace. Thus no full H-minus-1/2
Herglotz density theorem is asserted in this file. In particular the
reverse implication isolated below remains a mathematical obligation,
not a premise silently added to the original Main theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory
open scoped Real InnerProductSpace ComplexConjugate

/-- The true full normalized compatibility space at the reference
energy, including every Fourier mode and the original complex resonance
multiplicity. -/
def normalizedNeumannCompatibility {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ : ℝ) : Submodule ℂ L2Z :=
  (Q.comp (h1ResonantSpace Ω E₀).subtypeL).rangeᗮ

theorem mem_normalizedNeumannCompatibility_iff {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ : ℝ) (b : L2Z) :
    b ∈ normalizedNeumannCompatibility Q E₀ ↔
      ∀ v : h1ResonantSpace Ω E₀, ⟪Q (v : NeumannH1 Ω), b⟫_ℂ = 0 := by
  constructor
  · intro hb v
    exact hb _ ⟨v, rfl⟩
  · intro hb y hy
    obtain ⟨v, rfl⟩ := hy
    exact hb v

theorem isClosed_normalizedNeumannCompatibility {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ : ℝ) :
    IsClosed (normalizedNeumannCompatibility Q E₀ : Set L2Z) :=
  (Q.comp (h1ResonantSpace Ω E₀).subtypeL).range.isClosed_orthogonal

section SuppliedCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

/-- The algebraic span of actual transformed physical Herglotz
conormals, rather than formal direction jets or a chosen Fourier subset. -/
def localConformalHerglotzLoadSpan (E₀ : ℝ) : Submodule ℂ L2Z :=
  Submodule.span ℂ {b | ∃ (a : ℝ → ℂ) (ha : IsDirDensity a),
    b = localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))}

include hb hL hhol hinj hC hcoord in
theorem localConformalHerglotzLoadSpan_le_compatibility {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    localConformalHerglotzLoadSpan F hγ hτ E₀ ≤ normalizedNeumannCompatibility QF E₀ := by
  apply Submodule.span_le.mpr
  rintro b ⟨a, ha, rfl⟩
  apply (mem_normalizedNeumannCompatibility_iff QF E₀ _).mpr
  exact localConformalHerglotz_load_compatible hR F hFs hb hL hhol hinj hC hγ hτ
    hcoord hE₀ ha

include hb hL hhol hinj hC hcoord in
theorem localConformalHerglotzLoadSpan_closure_le_compatibility
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    (localConformalHerglotzLoadSpan F hγ hτ E₀).topologicalClosure ≤
      normalizedNeumannCompatibility QF E₀ :=
  Submodule.topologicalClosure_minimal _
    (localConformalHerglotzLoadSpan_le_compatibility hR F hFs hb hL hhol hinj hC
      hγ hτ hcoord hE₀)
    (isClosed_normalizedNeumannCompatibility QF E₀)

/-- Exact density-to-annihilator equivalence. Both sides refer to the
actual normalized load space; no reverse Cauchy theorem is supplied as
an assumption. -/
theorem localConformalHerglotz_density_iff_annihilator {E₀ : ℝ} :
    (localConformalHerglotzLoadSpan F hγ hτ E₀).topologicalClosure =
        normalizedNeumannCompatibility QF E₀ ↔
      (localConformalHerglotzLoadSpan F hγ hτ E₀)ᗮ =
        ((localConformalDiskHalfTrace hR F hFs hL).comp
          (h1ResonantSpace ΩF E₀).subtypeL).range.topologicalClosure := by
  constructor
  · intro h
    have hh := congrArg (fun S : Submodule ℂ L2Z => Sᗮ) h
    simpa only [normalizedNeumannCompatibility, Submodule.orthogonal_closure,
      Submodule.orthogonal_orthogonal_eq_closure] using hh
  · intro h
    have hh := congrArg (fun S : Submodule ℂ L2Z => Sᗮ) h
    simpa only [normalizedNeumannCompatibility, Submodule.orthogonal_closure,
      Submodule.orthogonal_orthogonal_eq_closure] using hh

end SuppliedCoordinates

/-- What the existing true Cauchy reconstruction gives for a Lipschitz
annihilator. This is recorded with its actual regularity and conclusion;
it is not the full fractional-space annihilator theorem above. -/
theorem lipschitz_herglotz_annihilator_mem_compatible {γ h : ℝ → ℂ} {E : ℝ}
    (hLip : ∃ K, LipschitzOnWith K h (Icc 0 (2 * π)))
    (hclosed : h (2 * π) = h 0)
    (hcompat : ∀ (a : ℝ → ℂ), IsDirDensity a →
      IntervalIntegrable (fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * h s)
          volume 0 (2 * π) ∧
        ∫ s in (0 : ℝ)..(2 * π), conj (herglotzConormal (Real.sqrt E) a γ s) * h s = 0) :
    h ∈ compatibleTraces γ E :=
  ⟨hLip, hclosed, hcompat⟩

end PolyaNeumann

end
