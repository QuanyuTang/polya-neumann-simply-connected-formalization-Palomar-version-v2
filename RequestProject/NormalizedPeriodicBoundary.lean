module

public import RequestProject.PeriodicRegularContinuity
public import RequestProject.PeriodicRegularSelfAdjoint
public import RequestProject.NeumannResidueBasis
public import RequestProject.NeumannRegularSolutionAtReference

/-! The genuine normalized periodic boundary family and its Neumann pole.
The decomposition includes a nonresonant reference energy itself. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate

private theorem periodic_projected_trace_gram
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (S : Submodule ℂ H) [CompleteSpace S] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) (Q : H →L[ℂ] G) (c : ℝ) (hc : 0 ≤ c) :
    (c : ℂ) • (Q ∘L S.starProjection ∘L adjoint Q) =
      ∑ i, InnerProductSpace.rankOne ℂ ((Real.sqrt c : ℂ) • Q (b i))
        ((Real.sqrt c : ℂ) • Q (b i)) := by
  classical
  have hs : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = (c : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hc
  have hgram : Q ∘L S.starProjection ∘L adjoint Q =
      (Q.comp S.subtypeL).comp (adjoint (Q.comp S.subtypeL)) := by
    simp only [adjoint_comp, Submodule.adjoint_subtypeL,
      Submodule.starProjection, comp_assoc]
  rw [hgram]
  apply ContinuousLinearMap.ext
  intro g
  have hre := b.sum_repr' (adjoint (Q.comp S.subtypeL) g)
  change (c : ℂ) • Q ((adjoint (Q.comp S.subtypeL) g : S) : H) = _
  simp_rw [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply, inner_smul_left,
    Complex.conj_ofReal, smul_smul]
  rw [← hre]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    adjoint_inner_right, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun a : ℂ => a • Q (b i))
  calc
    (c : ℂ) * ⟪Q (b i), g⟫_ℂ =
        ((Real.sqrt c : ℂ) * (Real.sqrt c : ℂ)) * ⟪Q (b i), g⟫_ℂ := by rw [hs]
    _ = ((Real.sqrt c : ℂ) * ⟪Q (b i), g⟫_ℂ) * (Real.sqrt c : ℂ) := by ring

theorem normalizedNeumannResidue_eq_sum_rankOne {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (h1ResonantSpace Ω E₀)) :
    normalizedNeumannResidue Q E₀ = ∑ i,
      InnerProductSpace.rankOne ℂ ((Real.sqrt (E₀ + 1) : ℂ) • Q (b i))
        ((Real.sqrt (E₀ + 1) : ℂ) • Q (b i)) := by
  exact periodic_projected_trace_gram (h1ResonantSpace Ω E₀) b Q (E₀ + 1)
    (by linarith)

theorem h1Resonant_starProjection_eq_zero_of_form_isUnit {Ω : Set ℂ} {E₀ : ℝ}
    (hunit : IsUnit (h1HelmholtzForm Ω E₀)) (u : NeumannH1 Ω) :
    (h1ResonantSpace Ω E₀).starProjection u = 0 := by
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).injective
  apply hinj
  rw [map_zero]
  exact ((h1ResonantSpace Ω E₀).orthogonalProjection u).property

theorem normalizedNeumannBoundary_eq_regular_at_nonresonant_reference {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1HelmholtzForm Ω E₀)) :
    normalizedNeumannBoundary Q E₀ = normalizedNeumannRegular Q E₀ E₀ := by
  apply ContinuousLinearMap.ext
  intro b
  have h := normalizedNeumannRegular_eq_trace_of_solution_at_reference Q hb hL hE₀
    b (normalizedNeumannPoisson Q E₀ b) (normalizedNeumannPoisson_isSolution Q hunit b)
  rw [h1Resonant_starProjection_eq_zero_of_form_isUnit hunit, map_zero, sub_zero] at h
  exact h.symm

theorem normalizedNeumannBoundary_eq_pole_add_regular_on_nonresonant_set
    {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hfull : IsUnit (h1HelmholtzForm Ω E))
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    normalizedNeumannBoundary Q E =
      (-((E - E₀ : ℝ) : ℂ)⁻¹) • normalizedNeumannResidue Q E₀ +
        normalizedNeumannRegular Q E₀ E := by
  by_cases hne : E ≠ E₀
  · exact normalizedNeumannBoundary_eq_pole_add_regular Q hb hL hE₀ hne hunit
  · have heq : E = E₀ := not_ne_iff.mp hne
    subst E
    simp only [sub_self, Complex.ofReal_zero, inv_zero, neg_zero, zero_smul, zero_add]
    rw [normalizedNeumannBoundary_eq_regular_at_nonresonant_reference Q hb hL hE₀ hfull]
    ext x
    simp

def normalizedPeriodicBoundaryFamily {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    (E : ℝ) : L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • (normalizedNeumannBoundary Q E - normalizedInverseAbsOperator) +
    principalNormalized + correctedRemainderOperator (Ws E) 0 0

theorem normalizedPeriodicBoundaryFamily_eq_regular_at_nonresonant_reference
    {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hunit : IsUnit (h1HelmholtzForm Ω E₀)) :
    normalizedPeriodicBoundaryFamily Q Ws E₀ = normalizedPeriodicRegularFamily Q E₀ Ws E₀ := by
  simp only [normalizedPeriodicBoundaryFamily, normalizedPeriodicRegularFamily,
    normalizedNeumannBoundary_eq_regular_at_nonresonant_reference Q hb hL hE₀ hunit]

theorem normalizedPeriodicBoundaryFamily_isSelfAdjoint {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {γ : ℝ → ℂ} {K : NNReal}
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E (Ws E))
    (hbase : Summable fun p => ‖correctedRemainderMatrix (Ws E) 0 0 p‖ ^ 2) :
    IsSelfAdjoint (normalizedPeriodicBoundaryFamily Q Ws E) := by
  rw [normalizedPeriodicBoundaryFamily, correctedRemainderOperator_eq _ _ _ hbase]
  have hm := hsMatrixOp_isSelfAdjoint _ hbase (correctedRemainderMatrix_zero_hermitian hK hW)
  have h1 := normalizedNeumannBoundary_isSelfAdjoint Q E
  have h2 := @normalizedInverseAbsOperator_isSelfAdjoint
  have h3 := @principalNormalized_isSelfAdjoint
  simp only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hm h1 h2 h3 ⊢
  rw [map_add, map_add, map_smulₛₗ, map_sub, h1, h2, h3, hm, map_ofNat]

theorem normalizedPeriodicBoundaryFamily_eq_pole_add_regular {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hfull : IsUnit (h1HelmholtzForm Ω E))
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    normalizedPeriodicBoundaryFamily Q Ws E =
      ((-2 / (E - E₀) : ℝ) : ℂ) • normalizedNeumannResidue Q E₀ +
        normalizedPeriodicRegularFamily Q E₀ Ws E := by
  have hc : (2 : ℂ) * (-((E - E₀ : ℝ) : ℂ)⁻¹) =
      ((-2 / (E - E₀) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [normalizedPeriodicBoundaryFamily,
    normalizedNeumannBoundary_eq_pole_add_regular_on_nonresonant_set Q hb hL hE₀ hfull hunit]
  simp only [normalizedPeriodicRegularFamily, smul_sub, smul_add, smul_smul, hc]
  abel

end PolyaNeumann
end
