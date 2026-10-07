module

public import RequestProject.NeumannRegularSelfAdjoint
public import RequestProject.MatrixHSSymmetry
public import RequestProject.NormalizedPeriodicRegular

/-! Self-adjointness of the actual corrected periodic regular boundary operator. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open Real
open scoped ComplexConjugate

theorem normalizedInverseAbsOperator_isSelfAdjoint :
    IsSelfAdjoint normalizedInverseAbsOperator := by
  apply diagOp_isSelfAdjoint
  intro n
  unfold normalizedInverseAbsSymbol
  split_ifs <;> simp

theorem principalNormalized_isSelfAdjoint : IsSelfAdjoint principalNormalized := by
  apply diagOp_isSelfAdjoint
  intro n
  unfold principalSymbol
  split_ifs
  · exact map_zero _
  · exact Complex.conj_ofReal _

theorem correctedRemainderMatrix_zero_hermitian
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (m n : ℤ) :
    correctedRemainderMatrix W 0 0 (m,n) =
      conj (correctedRemainderMatrix W 0 0 (n,m)) := by
  have hc := correctedKernelCoeff_conj_symm hK hW (-n) m
  simp only [neg_neg] at hc
  simp only [correctedRemainderMatrix]
  rw [hc]
  simp only [map_mul, Complex.conj_ofReal]
  congr 1
  norm_num
  ring

theorem normalizedPeriodicRegularOperator_isSelfAdjoint {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ)
    {γ : ℝ → ℂ} {K : NNReal} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    IsSelfAdjoint (normalizedPeriodicRegularOperator Q E₀ E W hbase) := by
  have hm := hsMatrixOp_isSelfAdjoint _ hbase (correctedRemainderMatrix_zero_hermitian hK hW)
  have h1 := normalizedNeumannRegular_isSelfAdjoint Q E₀ E
  have h2 := @normalizedInverseAbsOperator_isSelfAdjoint
  have h3 := @principalNormalized_isSelfAdjoint
  simp only [IsSelfAdjoint] at hm h1 h2 h3 ⊢
  unfold normalizedPeriodicRegularOperator
  simp only [ContinuousLinearMap.star_eq_adjoint] at hm h1 h2 h3 ⊢
  rw [map_add, map_add, map_smulₛₗ, map_sub, h1, h2, h3, hm, map_ofNat]

end PolyaNeumann
end
