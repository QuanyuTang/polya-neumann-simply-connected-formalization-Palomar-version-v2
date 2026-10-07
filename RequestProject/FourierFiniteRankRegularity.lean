module

public import RequestProject.PositiveFourierBasis
public import RequestProject.ConormalNormalization
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Sobolev preservation by the actual finite Fourier correction

Finite Fourier output vectors make the chart correction regularizing.
The actual orthogonal compatibility projection preserves each Sobolev
order for which its finite collection of defining vectors is regular.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

def fourierSobolevSubmodule (s : ℝ) : Submodule ℂ L2Z where
  carrier := {b | IsSobolevSeq s (b : ℤ → ℂ)}
  zero_mem' := by simp [IsSobolevSeq]
  add_mem' := by
    intro b d hb hd
    show IsSobolevSeq s ((b + d : L2Z) : ℤ → ℂ)
    simpa only [lp.coeFn_add] using isSobolevSeq_add hb hd
  smul_mem' := by
    intro a b hb
    show IsSobolevSeq s ((a • b : L2Z) : ℤ → ℂ)
    simpa only [lp.coeFn_smul] using isSobolevSeq_smul a hb

theorem finiteFourierSubmodule_le_sobolev (s : ℝ) :
    finiteFourierSubmodule ≤ fourierSobolevSubmodule s := by
  intro b hb
  exact isSobolevSeq_of_finite_fourier_support s hb

theorem isSobolevSeq_posProj {s : ℝ} {b : L2Z}
    (hb : IsSobolevSeq s (b : ℤ → ℂ)) :
    IsSobolevSeq s (posProj b : ℤ → ℂ) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hb
  by_cases hn : 0 < n
  · simp [posProj, diagOp_apply, hn]
  · simpa [posProj, diagOp_apply, hn] using sq_nonneg (sobWeight n ^ s * ‖b n‖)

theorem nonpositive_orthogonal_starProjection :
    nonpositiveFourierSubspaceᗮ.starProjection = posProj := by
  ext1 b
  have h := nonpositiveFourierSubspace.starProjection_add_starProjection_orthogonal b
  rw [nonpositiveFourierSubspace_starProjection] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at h
  calc
    _ = b - (b - posProj b) := by
      rw [eq_sub_iff_add_eq]
      simpa only [add_comm] using h
    _ = _ := by abel

theorem finite_fourier_chart_preserves_sobolev {d : ℕ}
    (u : Fin d → nonpositiveFourierSubspaceᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    {s : ℝ} (z : nonpositiveFourierSubspaceᗮ)
    (hz : IsSobolevSeq s ((z : L2Z) : ℤ → ℂ)) :
    IsSobolevSeq s
      ((Submodule.subtypeL nonpositiveFourierSubspaceᗮ +
        ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) z : ℤ → ℂ) := by
  have hfin : (∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) z ∈
      finiteFourierSubmodule := by
    rw [ContinuousLinearMap.sum_apply]
    apply Submodule.sum_mem
    intro r _
    rw [InnerProductSpace.rankOne_apply]
    exact finiteFourierSubmodule.smul_mem _ (hv r)
  have hreg := finiteFourierSubmodule_le_sobolev s hfin
  simpa only [ContinuousLinearMap.add_apply, Submodule.subtypeL_apply, lp.coeFn_add] using
    isSobolevSeq_add hz hreg

theorem finite_fourier_chart_adjoint_preserves_sobolev {d : ℕ}
    (u : Fin d → nonpositiveFourierSubspaceᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {s : ℝ} (b : L2Z) (hb : IsSobolevSeq s (b : ℤ → ℂ)) :
    IsSobolevSeq s
      (((ContinuousLinearMap.adjoint
        (Submodule.subtypeL nonpositiveFourierSubspaceᗮ +
          ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r))) b : L2Z) : ℤ → ℂ) := by
  have hfin : ((∑ r, InnerProductSpace.rankOne ℂ (u r) (v r)) b : L2Z) ∈
      finiteFourierSubmodule := by
    rw [ContinuousLinearMap.sum_apply, Submodule.coe_sum]
    apply Submodule.sum_mem
    intro r _
    rw [InnerProductSpace.rankOne_apply, Submodule.coe_smul]
    exact finiteFourierSubmodule.smul_mem _ (hu r)
  have hreg := finiteFourierSubmodule_le_sobolev s hfin
  have hp := isSobolevSeq_posProj hb
  have heq :
      ((ContinuousLinearMap.adjoint
        (Submodule.subtypeL nonpositiveFourierSubspaceᗮ +
          ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r))) b : L2Z) =
      posProj b + ((∑ r, InnerProductSpace.rankOne ℂ (u r) (v r)) b : L2Z) := by
    simp only [map_add, map_sum, InnerProductSpace.adjoint_rankOne,
      Submodule.adjoint_subtypeL, ContinuousLinearMap.add_apply, Submodule.coe_add,
      ← Submodule.starProjection_apply, nonpositive_orthogonal_starProjection]
  rw [heq]
  simpa only [lp.coeFn_add] using isSobolevSeq_add hp hreg

instance (priority := 1000) finiteFourierCompatibilityOrthogonalProjection {m : ℕ}
    (η : Fin m → nonpositiveFourierSubspaceᗮ) :
    ((Submodule.span ℂ (range η))ᗮ).HasOrthogonalProjection := by
  letI : CompleteSpace ((Submodule.span ℂ (range η))ᗮ) :=
    (Submodule.span ℂ (range η)).isClosed_orthogonal.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

theorem compatibility_projection_preserves_sobolev {m : ℕ}
    (η : Fin m → nonpositiveFourierSubspaceᗮ) {s : ℝ}
    (hη : ∀ j, IsSobolevSeq s ((η j : L2Z) : ℤ → ℂ))
    (z : nonpositiveFourierSubspaceᗮ)
    (hz : IsSobolevSeq s ((z : L2Z) : ℤ → ℂ)) :
    IsSobolevSeq s
      (((Submodule.span ℂ (range η))ᗮ.starProjection z : L2Z) : ℤ → ℂ) := by
  let V : Submodule ℂ nonpositiveFourierSubspaceᗮ := Submodule.span ℂ (range η)
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (finite_range η)
  have hle : V ≤ (fourierSobolevSubmodule s).comap nonpositiveFourierSubspaceᗮ.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hη j
  have hp : IsSobolevSeq s ((V.starProjection z : L2Z) : ℤ → ℂ) :=
    hle (Submodule.starProjection_apply_mem V z)
  have heq : (Vᗮ.starProjection z : L2Z) = (z : L2Z) - (V.starProjection z : L2Z) := by
    have h : (V.starProjection z : L2Z) + (Vᗮ.starProjection z : L2Z) = (z : L2Z) := by
      simpa only [Submodule.coe_add] using
        congrArg (fun x : nonpositiveFourierSubspaceᗮ => (x : L2Z))
          (V.starProjection_add_starProjection_orthogonal z)
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using h
  change IsSobolevSeq s ((Vᗮ.starProjection z : L2Z) : ℤ → ℂ)
  rw [heq]
  simpa only [lp.coeFn_sub, lp.coeFn_add, lp.coeFn_neg, sub_eq_add_neg, neg_one_smul] using
    isSobolevSeq_add hz (isSobolevSeq_smul (-1 : ℂ) hp)

end PolyaNeumann

end
