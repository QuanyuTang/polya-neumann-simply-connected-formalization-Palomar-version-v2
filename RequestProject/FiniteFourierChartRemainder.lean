module

public import RequestProject.FourierFiniteRankRegularity

/-!
# The regular principal correction of a finite Fourier chart

The input and output vectors of the actual chart correction have finite
Fourier support. Expanding its adjoint proves that the correction to the
compressed positive principal part is regular at every Sobolev order.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

local notation "H₁" => nonpositiveFourierSubspaceᗮ

private theorem finite_chart_posProj_idempotent (b : L2Z) :
    posProj (posProj b) = posProj b := by
  apply lp.ext
  funext n
  simp only [posProj, diagOp_apply]
  split_ifs <;> simp

private theorem finite_chart_projection_correction_identity
    (z : H₁) (b a : L2Z) :
    a - (z : L2Z) = posProj (b - (z : L2Z)) + (a - posProj (posProj b)) := by
  have hpz : posProj (z : L2Z) = (z : L2Z) := by
    rw [← nonpositive_orthogonal_starProjection]
    exact Submodule.starProjection_mem_subspace_eq_self z
  rw [map_sub, hpz, finite_chart_posProj_idempotent]
  abel

def finiteFourierChart {d : ℕ} (u : Fin d → H₁) (v : Fin d → L2Z) :
    H₁ →L[ℂ] L2Z :=
  Submodule.subtypeL H₁ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)

theorem finiteFourierChart_correction_sobolev {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (s : ℝ) (z : H₁) :
    IsSobolevSeq s ((finiteFourierChart u v z - (z : L2Z) : L2Z) : ℤ → ℂ) := by
  have heq : finiteFourierChart u v z - (z : L2Z) =
      (∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) z := by
    simp only [finiteFourierChart, ContinuousLinearMap.add_apply,
      Submodule.subtypeL_apply, add_sub_cancel_left]
  rw [heq]
  change _ ∈ fourierSobolevSubmodule s
  rw [ContinuousLinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r _
  rw [InnerProductSpace.rankOne_apply]
  exact (fourierSobolevSubmodule s).smul_mem _
    (isSobolevSeq_of_finite_fourier_support s (hv r))

theorem finiteFourierChart_adjoint_decomposition {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z) (b : L2Z) :
    ((ContinuousLinearMap.adjoint (finiteFourierChart u v)) b : L2Z) =
      posProj b + ((∑ r, InnerProductSpace.rankOne ℂ (u r) (v r)) b : L2Z) := by
  simp only [finiteFourierChart, map_add, map_sum, InnerProductSpace.adjoint_rankOne,
    Submodule.adjoint_subtypeL, ContinuousLinearMap.add_apply, Submodule.coe_add,
    ← Submodule.starProjection_apply, nonpositive_orthogonal_starProjection]

theorem finiteFourierChart_adjoint_correction_sobolev {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    (s : ℝ) (b : L2Z) :
    IsSobolevSeq s
      ((((ContinuousLinearMap.adjoint (finiteFourierChart u v)) b : L2Z) - posProj b : L2Z) : ℤ → ℂ) := by
  rw [finiteFourierChart_adjoint_decomposition, add_sub_cancel_left]
  change _ ∈ fourierSobolevSubmodule s
  rw [ContinuousLinearMap.sum_apply, Submodule.coe_sum]
  apply Submodule.sum_mem
  intro r _
  rw [InnerProductSpace.rankOne_apply, Submodule.coe_smul]
  exact (fourierSobolevSubmodule s).smul_mem _
    (isSobolevSeq_of_finite_fourier_support s (hu r))

theorem finiteFourierChart_principal_correction_sobolev {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (s : ℝ) (z : H₁) :
    IsSobolevSeq s
      ((((ContinuousLinearMap.adjoint (finiteFourierChart u v))
        (posProj (finiteFourierChart u v z)) : L2Z) - (z : L2Z) : L2Z) : ℤ → ℂ) := by
  have hreg₁ := isSobolevSeq_posProj (finiteFourierChart_correction_sobolev u v hv s z)
  have hreg₂ := finiteFourierChart_adjoint_correction_sobolev u v hu s
    (posProj (finiteFourierChart u v z))
  have heq :
      ((ContinuousLinearMap.adjoint (finiteFourierChart u v))
        (posProj (finiteFourierChart u v z)) : L2Z) - (z : L2Z) =
      posProj (finiteFourierChart u v z - (z : L2Z)) +
        (((ContinuousLinearMap.adjoint (finiteFourierChart u v))
          (posProj (finiteFourierChart u v z)) : L2Z) -
            posProj (posProj (finiteFourierChart u v z))) := by
    exact finite_chart_projection_correction_identity z (finiteFourierChart u v z)
      ((ContinuousLinearMap.adjoint (finiteFourierChart u v))
        (posProj (finiteFourierChart u v z)))
  rw [heq]
  change _ ∈ fourierSobolevSubmodule s
  exact (fourierSobolevSubmodule s).add_mem hreg₁ hreg₂

end PolyaNeumann

end
