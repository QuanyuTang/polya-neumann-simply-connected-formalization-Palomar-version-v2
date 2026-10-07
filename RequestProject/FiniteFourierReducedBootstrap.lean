module

public import RequestProject.FiniteFourierChartRemainder

/-!
# Two actual Sobolev gains for a compressed finite Fourier chart

The compressed remainder is defined from the given boundary operator and
the genuine finite Fourier chart. A projected null equation then supplies
the fixed-point relation. Its two regularity steps use the corresponding
two gains of that same remainder, and retain the finite compatibility
projection explicitly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

local notation "H₁" => nonpositiveFourierSubspaceᗮ

def finiteFourierReducedRemainder {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z) (P : L2Z →L[ℂ] L2Z) :
    H₁ →L[ℂ] H₁ :=
  (ContinuousLinearMap.adjoint (finiteFourierChart u v)).comp
      (P.comp (finiteFourierChart u v)) - (4 : ℂ) • (1 : H₁ →L[ℂ] H₁)

theorem finiteFourierReducedRemainder_sobolev {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (P : L2Z →L[ℂ] L2Z) {s t : ℝ}
    (hP : ∀ b : L2Z, IsSobolevSeq s (b : ℤ → ℂ) →
      IsSobolevSeq t ((P - (4 : ℂ) • posProj) b : ℤ → ℂ))
    (z : H₁) (hz : IsSobolevSeq s ((z : L2Z) : ℤ → ℂ)) :
    IsSobolevSeq t ((finiteFourierReducedRemainder u v P z : L2Z) : ℤ → ℂ) := by
  have hT := finite_fourier_chart_preserves_sobolev u v hv z hz
  have hrem := finite_fourier_chart_adjoint_preserves_sobolev u v hu
    ((P - (4 : ℂ) • posProj) (finiteFourierChart u v z)) (hP _ hT)
  have hfin := finiteFourierChart_principal_correction_sobolev u v hu hv t z
  have heq : (finiteFourierReducedRemainder u v P z : L2Z) =
      ((ContinuousLinearMap.adjoint (finiteFourierChart u v))
        ((P - (4 : ℂ) • posProj) (finiteFourierChart u v z)) : L2Z) +
      (4 : ℂ) •
        (((ContinuousLinearMap.adjoint (finiteFourierChart u v))
          (posProj (finiteFourierChart u v z)) : L2Z) - (z : L2Z)) := by
    simp only [finiteFourierReducedRemainder, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_sub, map_smul,
      Submodule.coe_sub, Submodule.coe_smul, smul_sub]
    abel
  rw [heq]
  change _ ∈ fourierSobolevSubmodule t
  exact (fourierSobolevSubmodule t).add_mem hrem
    ((fourierSobolevSubmodule t).smul_mem (4 : ℂ) hfin)

theorem finiteFourierReduced_projected_null_half_regular {d m : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (P : L2Z →L[ℂ] L2Z)
    (hP₀ : ∀ b : L2Z, IsSobolevSeq (1 / 4 : ℝ)
      ((P - (4 : ℂ) • posProj) b : ℤ → ℂ))
    (hP₁ : ∀ b : L2Z, IsSobolevSeq (1 / 4 : ℝ) (b : ℤ → ℂ) →
      IsSobolevSeq (1 / 2 : ℝ) ((P - (4 : ℂ) • posProj) b : ℤ → ℂ))
    (η : Fin m → H₁)
    (hη : ∀ j, IsSobolevSeq (1 / 2 : ℝ) ((η j : L2Z) : ℤ → ℂ))
    (z : H₁) (hz : z ∈ (Submodule.span ℂ (range η))ᗮ)
    (hnull : (Submodule.span ℂ (range η))ᗮ.starProjection
      ((ContinuousLinearMap.adjoint (finiteFourierChart u v))
        (P (finiteFourierChart u v z))) = 0) :
    IsSobolevSeq (1 / 2 : ℝ) ((z : L2Z) : ℤ → ℂ) := by
  let Z : Submodule ℂ H₁ := (Submodule.span ℂ (range η))ᗮ
  have hpz : Z.starProjection z = z := Submodule.starProjection_eq_self_iff.mpr hz
  have hfix :
      (-((1 / 4 : ℝ) : ℂ)) •
        Z.starProjection (finiteFourierReducedRemainder u v P z) = z := by
    have hproj : Z.starProjection (finiteFourierReducedRemainder u v P z) =
        -(4 : ℂ) • z := by
      simp only [finiteFourierReducedRemainder, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, map_sub, map_smul, hpz]
      rw [hnull]
      simp only [zero_sub, neg_smul]
    rw [hproj, smul_smul]
    norm_num
  have hz₀ : IsSobolevSeq 0 ((z : L2Z) : ℤ → ℂ) := by
    simpa only [IsSobolevSeq, Real.rpow_zero, one_mul] using summable_norm_sq_L2Z (z : L2Z)
  have hC₀ := finiteFourierReducedRemainder_sobolev u v hu hv P
    (s := 0) (t := (1 / 4 : ℝ)) (fun b _ => hP₀ b) z hz₀
  have hη₀ : ∀ j, IsSobolevSeq (1 / 4 : ℝ) ((η j : L2Z) : ℤ → ℂ) :=
    fun j => (sobNormSq_mono (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) (hη j)).1
  have hz₁ : IsSobolevSeq (1 / 4 : ℝ) ((z : L2Z) : ℤ → ℂ) := by
    have hprojReg := compatibility_projection_preserves_sobolev η hη₀
      (finiteFourierReducedRemainder u v P z) hC₀
    have hreg := isSobolevSeq_smul (-((1 / 4 : ℝ) : ℂ)) hprojReg
    have heq : ((-((1 / 4 : ℝ) : ℂ)) •
        ((Z.starProjection (finiteFourierReducedRemainder u v P z) : L2Z) : ℤ → ℂ)) =
        ((z : L2Z) : ℤ → ℂ) := by
      simpa only [Submodule.coe_smul, lp.coeFn_smul] using
        congrArg (fun x : H₁ => ((x : L2Z) : ℤ → ℂ)) hfix
    rwa [heq] at hreg
  have hC₁ := finiteFourierReducedRemainder_sobolev u v hu hv P hP₁ z hz₁
  have hprojReg := compatibility_projection_preserves_sobolev η hη
    (finiteFourierReducedRemainder u v P z) hC₁
  have hreg := isSobolevSeq_smul (-((1 / 4 : ℝ) : ℂ)) hprojReg
  have heq : ((-((1 / 4 : ℝ) : ℂ)) •
      ((Z.starProjection (finiteFourierReducedRemainder u v P z) : L2Z) : ℤ → ℂ)) =
      ((z : L2Z) : ℤ → ℂ) := by
    simpa only [Submodule.coe_smul, lp.coeFn_smul] using
      congrArg (fun x : H₁ => ((x : L2Z) : ℤ → ℂ)) hfix
  rwa [heq] at hreg

end PolyaNeumann

end
