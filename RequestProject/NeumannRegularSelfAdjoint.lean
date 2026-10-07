module

public import RequestProject.NeumannNormalizedBoundary

/-! Self-adjointness of the genuine regular Neumann resolvent, including resonance. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann

private theorem regular_inverse_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) : IsSelfAdjoint (Ring.inverse A) := by
  rw [isSelfAdjoint_iff]
  exact (Ring.inverse_star A).symm.trans (congrArg Ring.inverse hA.star_eq)

private theorem regular_compression_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (S.orthogonalProjection ∘L A ∘L S.subtypeL) := by
  simpa only [Submodule.adjoint_subtypeL] using hA.adjoint_conj S.subtypeL

private theorem regular_extension_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S]
    (A : S →L[ℂ] S) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (S.subtypeL ∘L A ∘L S.orthogonalProjection) := by
  simpa only [Submodule.adjoint_subtypeL] using hA.conj_adjoint S.subtypeL

theorem h1ComplementMass_isSelfAdjoint (Ω : Set ℂ) (E₀ : ℝ) :
    IsSelfAdjoint (h1ComplementMass Ω E₀) :=
  regular_compression_selfAdjoint (h1ResonantSpace Ω E₀)ᗮ
    (h1MassOperator Ω) (h1MassOperator_isSelfAdjoint Ω)

theorem h1ComplementForm_isSelfAdjoint (Ω : Set ℂ) (E₀ E : ℝ) :
    IsSelfAdjoint (h1ComplementForm Ω E₀ E) := by
  have hc : IsSelfAdjoint ((E + 1 : ℝ) : ℂ) := by simp [IsSelfAdjoint]
  exact (IsSelfAdjoint.one _).sub (hc.smul (h1ComplementMass_isSelfAdjoint Ω E₀))

theorem h1RegularResolvent_isSelfAdjoint (Ω : Set ℂ) (E₀ E : ℝ) :
    IsSelfAdjoint (h1RegularResolvent Ω E₀ E) :=
  regular_extension_selfAdjoint (h1ResonantSpace Ω E₀)ᗮ
    (Ring.inverse (h1ComplementForm Ω E₀ E))
    (regular_inverse_selfAdjoint _ (h1ComplementForm_isSelfAdjoint Ω E₀ E))

theorem normalizedNeumannRegular_isSelfAdjoint {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ) :
    IsSelfAdjoint (normalizedNeumannRegular Q E₀ E) :=
  (h1RegularResolvent_isSelfAdjoint Ω E₀ E).conj_adjoint Q

end PolyaNeumann
end
