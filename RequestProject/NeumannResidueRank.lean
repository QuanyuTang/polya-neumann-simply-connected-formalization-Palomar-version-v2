module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import RequestProject.NeumannTraceInjective
public import RequestProject.NeumannResonanceDimension
public import RequestProject.NeumannConstantTrace

/-!
# Rank of the genuine Neumann boundary residue

The residue is the trace Gram operator of the actual form resonance space.
Injectivity of the genuine boundary trace makes its rank equal to the complex
Neumann multiplicity. No independent boundary spectrum is introduced.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

private theorem adjoint_surjective_of_finiteDimensional_injective
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (T : H →L[ℂ] G) (hT : Function.Injective T) :
    Function.Surjective (ContinuousLinearMap.adjoint T) := by
  let B : H →L[ℂ] H := (ContinuousLinearMap.adjoint T).comp T
  have hB : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hT
    rw [map_zero]
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← ContinuousLinearMap.adjoint_inner_right T x (T x)]
    change ⟪x, B x⟫_ℂ = 0
    rw [hx, inner_zero_right]
  have hsurj : Function.Surjective B :=
    LinearMap.injective_iff_surjective.mp hB
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  exact ⟨T y, hy⟩

/-- A nonzero scalar multiple of the Gram operator of an injective map
from a finite-dimensional Hilbert space has exactly the range of that map. -/
theorem range_scaled_trace_gram
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (T : H →L[ℂ] G) (hT : Function.Injective T) {c : ℂ} (hc : c ≠ 0) :
    (c • (T.comp (ContinuousLinearMap.adjoint T))).range = T.range := by
  have hsurj := adjoint_surjective_of_finiteDimensional_injective T hT
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨c • ContinuousLinearMap.adjoint T g, ?_⟩
    change T (c • ContinuousLinearMap.adjoint T g) =
      c • T (ContinuousLinearMap.adjoint T g)
    exact map_smul T c _
  · rintro ⟨u, rfl⟩
    obtain ⟨g, hg⟩ := hsurj (c⁻¹ • u)
    refine ⟨g, ?_⟩
    change c • T (ContinuousLinearMap.adjoint T g) = T u
    rw [hg, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The projected trace form of the same Gram identity, before restricting
the source to the resonance subspace. -/
theorem range_scaled_projected_trace_gram
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (S : Submodule ℂ H) [CompleteSpace S] [FiniteDimensional ℂ S]
    (T : H →L[ℂ] G) (hT : Function.Injective (T.comp S.subtypeL))
    {c : ℂ} (hc : c ≠ 0) :
    (c • (T ∘L S.starProjection ∘L ContinuousLinearMap.adjoint T)).range =
      (T.comp S.subtypeL).range := by
  have hgram : c • (T ∘L S.starProjection ∘L ContinuousLinearMap.adjoint T) =
      c • ((T.comp S.subtypeL).comp
        (ContinuousLinearMap.adjoint (T.comp S.subtypeL))) := by
    simp only [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
      Submodule.starProjection, ContinuousLinearMap.comp_assoc]
  exact (congrArg (fun A : G →L[ℂ] G => A.range) hgram).trans
    (range_scaled_trace_gram (T.comp S.subtypeL) hT hc)

/-- The actual trace of genuine resonance vectors. -/
def neumannResonantTrace {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) :
    h1ResonantSpace Ω E →L[ℂ] BoundaryL2 :=
  (h1BoundaryTrace hb hL hγ).comp (h1ResonantSpace Ω E).subtypeL

theorem neumannResonantTrace_injective {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) :
    Function.Injective (neumannResonantTrace hb hL hγ E) :=
  h1BoundaryTrace_injective_neumannKernel hb hL hγ hE

/-- The residue is the actual trace Gram operator, with the factor dictated
by the shifted H¹ inner product. -/
theorem neumannBoundaryResidue_eq_trace_gram {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) :
    neumannBoundaryResidue hb hL hγ E = ((E + 1 : ℝ) : ℂ) •
      ((neumannResonantTrace hb hL hγ E).comp
        (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := h1ResonantSpace Ω E)
          (F := BoundaryL2) (neumannResonantTrace hb hL hγ E))) := by
  simp only [neumannResonantTrace, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, neumannBoundaryResidue, h1BoundaryLoad,
    Submodule.starProjection, ContinuousLinearMap.comp_assoc]

/-- The physical residue has exactly the span of the genuine eigenfunction
boundary traces as its range. -/
theorem neumannBoundaryResidue_range_eq {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) :
    (neumannBoundaryResidue hb hL hγ E).range =
      (neumannResonantTrace hb hL hγ E).range := by
  haveI := finiteDimensional_h1ResonantSpace hb hL E
  have hc : ((E + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show E + 1 ≠ 0 by linarith)
  exact range_scaled_projected_trace_gram (h1ResonantSpace Ω E)
    (h1BoundaryTrace hb hL hγ) (neumannResonantTrace_injective hb hL hγ hE) hc

/-- The rank of the actual boundary residue equals the complex dimension
of the actual weak form resonance space. -/
theorem neumannBoundaryResidue_finrank_eq {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) :
    Module.finrank ℂ (neumannBoundaryResidue hb hL hγ E).range =
      Module.finrank ℂ (h1ResonantSpace Ω E) := by
  rw [neumannBoundaryResidue_range_eq hb hL hγ hE]
  exact LinearMap.finrank_range_of_inj (neumannResonantTrace_injective hb hL hγ hE)

/-- The pole rank is the multiplicity in the original variational Neumann
sequence, rather than a separately postulated boundary multiplicity. -/
theorem neumannBoundaryResidue_multiplicity_eq {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) :
    (Module.finrank ℂ (neumannBoundaryResidue hb hL hγ E).range : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  rw [neumannBoundaryResidue_finrank_eq hb hL hγ hE]
  exact h1ResonantSpace_multiplicity_eq hb hL hE.le

/-- The actual zero mode is handled by its true constant trace; positive
energies are handled by the proved uniqueness of the Cauchy problem. -/
theorem neumannResonantTrace_injective_nonneg {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 ≤ E) :
    Function.Injective (neumannResonantTrace hb hL hγ E) := by
  by_cases hzero : E = 0
  · subst E
    exact h1BoundaryTrace_injective_neumannKernel_zero hb hL hγ
  · exact neumannResonantTrace_injective hb hL hγ
      (lt_of_le_of_ne hE (Ne.symm hzero))

theorem neumannBoundaryResidue_range_eq_nonneg {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 ≤ E) :
    (neumannBoundaryResidue hb hL hγ E).range =
      (neumannResonantTrace hb hL hγ E).range := by
  haveI := finiteDimensional_h1ResonantSpace hb hL E
  have hc : ((E + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show E + 1 ≠ 0 by linarith)
  exact range_scaled_projected_trace_gram (h1ResonantSpace Ω E)
    (h1BoundaryTrace hb hL hγ) (neumannResonantTrace_injective_nonneg hb hL hγ hE) hc

/-- The physical zero pole has rank one, from the actual connected-domain
constant eigenspace and its nonzero boundary trace. -/
theorem neumannBoundaryResidue_zero_finrank {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    Module.finrank ℂ (neumannBoundaryResidue hb hL hγ 0).range = 1 := by
  rw [neumannBoundaryResidue_range_eq_nonneg hb hL hγ le_rfl]
  have hdim : Module.finrank ℂ (neumannResonantTrace hb hL hγ 0).range =
      Module.finrank ℂ (h1ResonantSpace Ω 0) :=
    LinearMap.finrank_range_of_inj
      (neumannResonantTrace_injective_nonneg hb hL hγ le_rfl)
  rw [hdim, (h1ResonantEquiv hL.1.1 0).finrank_eq]
  exact neumannEigenspace_zero_finrank hL.1 hb

end PolyaNeumann

end
