module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import RequestProject.NeumannResidueRank

/-!
# The boundary pole in an L²-normalized Neumann basis

The factor `E + 1` in the H¹ projection formula is absorbed into the
L² normalization of the actual eigenfunctions. The resulting residue is
the sum of the rank-one operators of their actual boundary traces.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace ComplexConjugate

/-- A genuine resonance vector, normalized in L² rather than the shifted H¹ norm. -/
def neumannResonantL2Mode (Ω : Set ℂ) (E : ℝ) (u : h1ResonantSpace Ω E) : L2 Ω :=
  (Real.sqrt (E + 1) : ℂ) • h1Value Ω u

theorem neumannResonantL2Mode_mem (Ω : Set ℂ) (E : ℝ)
    (u : h1ResonantSpace Ω E) :
    neumannResonantL2Mode Ω E u ∈ neumannEigenspace Ω E := by
  exact (neumannEigenspace Ω E).smul_mem _ (h1ResonantInclusion Ω E u).property

theorem neumannResonantL2Mode_inner (Ω : Set ℂ) {E : ℝ} (hE : 0 ≤ E)
    (u v : h1ResonantSpace Ω E) :
    ⟪neumannResonantL2Mode Ω E u, neumannResonantL2Mode Ω E v⟫_ℂ =
      ⟪u, v⟫_ℂ := by
  have hs : (Real.sqrt (E + 1) : ℂ) * (Real.sqrt (E + 1) : ℂ) =
      ((E + 1 : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (show 0 ≤ E + 1 by linarith)
  calc
    _ = ((Real.sqrt (E + 1) : ℂ) * (Real.sqrt (E + 1) : ℂ)) *
        ⟪h1Value Ω u, h1Value Ω v⟫_ℂ := by
      simp only [neumannResonantL2Mode, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal]
      ring
    _ = ((E + 1 : ℝ) : ℂ) * ⟪h1Value Ω u, h1Value Ω v⟫_ℂ := by rw [hs]
    _ = _ := (h1ResonantSpace_inner Ω E u v).symm

/-- Any orthonormal H¹ basis of the actual kernel gives an orthonormal family
of the actual weak Neumann eigenfunctions after this forced normalization. -/
theorem orthonormal_neumannResonantL2Mode (Ω : Set ℂ) {E : ℝ} (hE : 0 ≤ E)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (h1ResonantSpace Ω E)) :
    Orthonormal ℂ (fun i => neumannResonantL2Mode Ω E (b i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [neumannResonantL2Mode_inner Ω hE]
  exact b.inner_eq_ite i j

private theorem trace_gram_eq_sum_rankOne
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] G) :
    T.comp (ContinuousLinearMap.adjoint T) =
      ∑ i, InnerProductSpace.rankOne ℂ (T (b i)) (T (b i)) := by
  classical
  apply ContinuousLinearMap.ext
  intro g
  calc
    T (ContinuousLinearMap.adjoint T g) =
        T (∑ i, ⟪b i, ContinuousLinearMap.adjoint T g⟫_ℂ • b i) :=
      congrArg T (b.sum_repr' (ContinuousLinearMap.adjoint T g)).symm
    _ = ∑ i, ⟪T (b i), g⟫_ℂ • T (b i) := by
      rw [map_sum]
      simp only [map_smul, ContinuousLinearMap.adjoint_inner_right]
    _ = _ := by simp only [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply]

private theorem projected_trace_gram_eq_sum_rankOne
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (S : Submodule ℂ H) [CompleteSpace S] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) (T : H →L[ℂ] G) (c : ℝ) (hc : 0 ≤ c) :
    (c : ℂ) • (T ∘L S.starProjection ∘L ContinuousLinearMap.adjoint T) =
      ∑ i, InnerProductSpace.rankOne ℂ ((Real.sqrt c : ℂ) • T (b i))
        ((Real.sqrt c : ℂ) • T (b i)) := by
  classical
  have hs : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = (c : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hc
  have hgram : (c : ℂ) • (T ∘L S.starProjection ∘L ContinuousLinearMap.adjoint T) =
      (c : ℂ) • ((T.comp S.subtypeL).comp
        (ContinuousLinearMap.adjoint (T.comp S.subtypeL))) := by
    simp only [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
      Submodule.starProjection, ContinuousLinearMap.comp_assoc]
  rw [hgram, trace_gram_eq_sum_rankOne b]
  apply ContinuousLinearMap.ext
  intro g
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Finset.smul_sum,
    InnerProductSpace.rankOne_apply, inner_smul_left, Complex.conj_ofReal, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun a : ℂ => a • T (b i))
  rw [mul_comm _ (Real.sqrt c : ℂ), ← mul_assoc, hs]

/-- The actual boundary trace of the L²-normalized resonance eigenfunction. -/
def neumannResonantBoundaryMode {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (E : ℝ) (u : h1ResonantSpace Ω E) : BoundaryL2 :=
  (Real.sqrt (E + 1) : ℂ) • neumannResonantTrace hb hL hγ E u

theorem neumannResonantBoundaryMode_eq_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) (u : h1ResonantSpace Ω E) :
    neumannResonantBoundaryMode hb hL hγ E u =
      h1BoundaryTrace hb hL hγ ((Real.sqrt (E + 1) : ℂ) • (u : NeumannH1 Ω)) := by
  simp only [neumannResonantBoundaryMode, neumannResonantTrace,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, map_smul]

/-- Exact residue formula in terms of actual L²-normalized eigenfunction
boundary traces. This is the coefficient of `-(E - E₀)⁻¹` in the NtD pole. -/
theorem neumannBoundaryResidue_eq_sum_rankOne {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 ≤ E)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (h1ResonantSpace Ω E)) :
    neumannBoundaryResidue hb hL hγ E = ∑ i,
      InnerProductSpace.rankOne ℂ (neumannResonantBoundaryMode hb hL hγ E (b i))
        (neumannResonantBoundaryMode hb hL hγ E (b i)) := by
  exact projected_trace_gram_eq_sum_rankOne (h1ResonantSpace Ω E) b
    (h1BoundaryTrace hb hL hγ) (E + 1) (by linarith)

end PolyaNeumann

end
