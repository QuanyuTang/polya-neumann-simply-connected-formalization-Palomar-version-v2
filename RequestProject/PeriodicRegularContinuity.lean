module

public import RequestProject.NormalizedPeriodicRegular
public import RequestProject.CorrectedKernelEnergy

/-! Operator norm continuity of the genuine regular periodic family near a nonzero cut. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open Filter Topology Real Set

private theorem periodic_inverse_continuousAt_unit
    {A : Type*} [NormedRing A] [CompleteSpace A] {a : A} (ha : IsUnit a) :
    ContinuousAt (Ring.inverse : A → A) a := by
  obtain ⟨u, rfl⟩ := ha
  exact NormedRing.inverse_continuousAt u

theorem continuousAt_h1RegularResolvent {Ω : Set ℂ} {E₀ E : ℝ}
    (hu : IsUnit (h1ComplementForm Ω E₀ E)) :
    ContinuousAt (h1RegularResolvent Ω E₀) E := by
  have hi := (periodic_inverse_continuousAt_unit hu).comp
    (continuous_h1ComplementForm Ω E₀).continuousAt
  exact @ContinuousAt.clm_comp ℂ _ (NeumannH1 Ω) _ _ (h1ResonantSpace Ω E₀)ᗮ _
    (h1ComplementNormedSpace Ω E₀) (NeumannH1 Ω) _ _ ℝ _ _ _ E continuousAt_const
    (@ContinuousAt.clm_comp ℂ _ (NeumannH1 Ω) _ _ (h1ResonantSpace Ω E₀)ᗮ _
      (h1ComplementNormedSpace Ω E₀) (h1ResonantSpace Ω E₀)ᗮ _ (h1ComplementNormedSpace Ω E₀)
      ℝ _ _ _ E hi continuousAt_const)

theorem continuousAt_normalizedNeumannRegular {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ E : ℝ}
    (hu : IsUnit (h1ComplementForm Ω E₀ E)) :
    ContinuousAt (normalizedNeumannRegular Q E₀) E := by
  exact continuousAt_const.clm_comp
    ((continuousAt_h1RegularResolvent hu).clm_comp continuousAt_const)

/-- A total operator used to express a limit. Near a nonzero cut its
matrix is genuinely square summable, and it is exactly the actual matrix operator. -/
def correctedRemainderOperator (W : ℝ → Ell2 →L[ℂ] Ell2) (δ s : ℝ) : L2Z →L[ℂ] L2Z := by
  classical
  exact if h : Summable (fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2) then
    hsMatrixOp (correctedRemainderMatrix W δ s) h else 0

theorem correctedRemainderOperator_eq (W : ℝ → Ell2 →L[ℂ] Ell2) (δ s : ℝ)
    (h : Summable fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2) :
    correctedRemainderOperator W δ s = hsMatrixOp (correctedRemainderMatrix W δ s) h := by
  simp only [correctedRemainderOperator, dif_pos h]

theorem continuousAt_correctedRemainderOperator
    {γ : ℝ → ℂ} {K K' : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0)
    {δ s : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousAt (fun E => correctedRemainderOperator (Ws E) δ s) E₀ := by
  have href := summable_correctedRemainderMatrix hK hγ' (hWs E₀) hc hδ hδ' hs0 hs1
  obtain ⟨hsum, hlim⟩ := tendsto_correctedRemainder_energy hK hγ' hWs E₀ hc hδ hδ' hs0 hs1
  rw [ContinuousAt, correctedRemainderOperator_eq _ _ _ href]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hsum, hlim ε hε] with E hE hnorm
  rw [correctedRemainderOperator_eq _ _ _ hE, dist_eq_norm]
  exact hnorm hE

def normalizedPeriodicRegularFamily {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ : ℝ) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    (E : ℝ) : L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
    principalNormalized + correctedRemainderOperator (Ws E) 0 0

theorem normalizedPeriodicRegularFamily_eq {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    (h : Summable fun p => ‖correctedRemainderMatrix (Ws E) 0 0 p‖ ^ 2) :
    normalizedPeriodicRegularFamily Q E₀ Ws E =
      normalizedPeriodicRegularOperator Q E₀ E (Ws E) h := by
  simp only [normalizedPeriodicRegularFamily, normalizedPeriodicRegularOperator,
    correctedRemainderOperator_eq _ _ _ h]

theorem continuousAt_normalizedPeriodicRegularFamily {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ}
    (hu : IsUnit (h1ComplementForm Ω E₀ E₀))
    {γ : ℝ → ℂ} {K K' : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hWs : ∀ E, IsTransport γ E (Ws E))
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    ContinuousAt (normalizedPeriodicRegularFamily Q E₀ Ws) E₀ := by
  exact ((((continuousAt_normalizedNeumannRegular Q hu).sub continuousAt_const).const_smul
    (2 : ℂ)).add continuousAt_const).add
    (continuousAt_correctedRemainderOperator hK hγ' hWs E₀ hc
      (le_refl 0) (by norm_num) (le_refl 0) (by norm_num))

end PolyaNeumann
end
