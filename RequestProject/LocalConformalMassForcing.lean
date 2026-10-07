module

public import RequestProject.LocalConformalMass
public import RequestProject.LpBoundedMultiplierReal
public import RequestProject.DiskMassForcing

/-!
# The physical mass forcing in conformal coordinates

Multiplication by the Jacobian density is built on the actual L² pullback.
The mass pairing identifies it with the original weak equation. Its disk
moments gain one full Fourier derivative by the proved area Bessel estimate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate InnerProductSpace

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)

def localConformalMassForcing :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  (lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)).comp
      (localConformalMassPullback hR F hFs hL hK)

include hb hhol hinj hC in
theorem localConformal_mass_pairing
    (v u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ⟪h1Value (F '' ball (0 : ℂ) 1) v, h1Value (F '' ball (0 : ℂ) 1) u⟫_ℂ =
      ⟪h1Value (ball (0 : ℂ) 1) (localConformalH1Pullback hR F hFs hL v),
        localConformalMassForcing hR F hFs hL hK u⟫_ℂ := by
  rw [← localConformalMassPullback_inner hR F hFs hb hL hhol hinj hC hK v u]
  change ⟪lpBoundedMultiplier (localConformalMassDensity F)
      (localConformalMassDensity_aemeasurable hR F hFs)
      (localConformalMassDensity_ae_bound F hK)
      (h1Value (ball (0 : ℂ) 1) (localConformalH1Pullback hR F hFs hL v)),
      localConformalMassPullback hR F hFs hL hK u⟫_ℂ = _
  exact inner_lpBoundedMultiplier_real (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)
    (Eventually.of_forall fun z => Complex.conj_ofReal _) _ _

include hb hhol hinj hC in
theorem norm_localConformalMassForcing_le
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖localConformalMassForcing hR F hFs hL hK u‖ ≤
      K * ‖h1Value (F '' ball (0 : ℂ) 1) u‖ := by
  have hn : ‖localConformalMassPullback hR F hFs hL hK u‖ =
      ‖h1Value (F '' ball (0 : ℂ) 1) u‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (norm_sq_localConformalMassPullback hR F hFs hb hL hhol hinj hC hK u)
  calc
    _ ≤ K * ‖localConformalMassPullback hR F hFs hL hK u‖ :=
      norm_lpBoundedMulLin_le (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK) _
    _ = _ := by rw [hn]

def localConformalMassFourierH1 :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  diskMassForcingH1.comp (localConformalMassForcing hR F hFs hL hK)

@[simp] theorem localConformalMassFourierH1_apply
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) (n : ℤ) :
    localConformalMassFourierH1 hR F hFs hL hK u n =
      (sobWeight n : ℂ) *
        diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK u) n := rfl

include hb hhol hinj hC in
theorem norm_localConformalMassFourierH1_le
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖localConformalMassFourierH1 hR F hFs hL hK u‖ ≤
      (2 * K) * ‖h1Value (F '' ball (0 : ℂ) 1) u‖ := by
  calc
    _ ≤ 2 * ‖localConformalMassForcing hR F hFs hL hK u‖ :=
      norm_diskMassForcingH1Lin_le _
    _ ≤ 2 * (K * ‖h1Value (F '' ball (0 : ℂ) 1) u‖) :=
      mul_le_mul_of_nonneg_left
        (norm_localConformalMassForcing_le hR F hFs hb hL hhol hinj hC hK u) (by norm_num)
    _ = _ := by ring

end

end PolyaNeumann

end
