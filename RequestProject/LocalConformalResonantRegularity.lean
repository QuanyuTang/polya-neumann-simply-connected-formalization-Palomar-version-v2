module

public import RequestProject.LocalConformalRegularPrincipal
public import RequestProject.FourierFiniteRankRegularity

/-!
# Genuine resonant trace and compatibility-projection regularity

The original physical resonant weak equation has zero boundary load and
mass forcing E0*w. Actual conformal harmonic tests identify every nonzero
normalized trace coefficient with the genuine mass moments. The bounded
mass Fourier map and the actual zero-mode projection therefore give H1
regularity of Qw, including its unrestricted constant coefficient.

The adjoint of the actual finite Fourier chart preserves this regularity.
Thus its true compatibility vectors T*Qw and their finite-dimensional
orthogonal compatibility projection preserve the half and quarter orders
needed by the reduced bootstrap. Regularity of those vectors is derived,
not supplied as a compatibility premise. All geometry is supplied; no
initial conformal map existence is asserted. Source-only draft.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped InnerProductSpace

private theorem resonant_smoothing_one_apply (b : L2Z) (n : ℤ) :
    sobolevSmoothing 1 zero_le_one b n = (sobWeight n : ℂ)⁻¹ * b n := by
  simp only [sobolevSmoothing, diagOp_apply, Real.rpow_neg_one, Complex.ofReal_inv]

private theorem resonant_zeroMode_sobolev (s : ℝ) (b : L2Z) :
    IsSobolevSeq s (zeroModeProjection b : ℤ → ℂ) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Finset.mem_singleton] using hn
  simp only [zeroModeProjection_apply, if_neg hn0, zero_mul, norm_zero,
    mul_zero, zero_pow (by norm_num : 2 ≠ 0)]

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "MF" => localConformalMassFourierH1 hR F hFs hL hK
local notation "H₀" => nonpositiveFourierSubspace

include hb hhol hinj hC e he hsource hes in
/-- Every actual resonant vector has this exact one-derivative trace
factorization. Its zeroth coefficient is retained by the genuine P0. -/
theorem localConformal_resonant_halfTrace_factorization
    {E₀ : ℝ} {w : NeumannH1 ΩF} (hw : w ∈ h1ResonantSpace ΩF E₀) :
    QF w = sobolevSmoothing 1 zero_le_one (MF ((E₀ : ℂ) • w)) +
      zeroModeProjection (QF w) := by
  have hforced := localConformalResonant_isForcedSolution hR F hFs hL hw
  apply lp.ext
  funext n
  simp only [lp.coeFn_add, Pi.add_apply, resonant_smoothing_one_apply,
    localConformalMassFourierH1_apply, zeroModeProjection_apply]
  by_cases hn : n = 0
  · subst n
    simp only [diskMassForcingCoeff, mul_zero, if_true, one_mul, zero_add]
  · have hm := localConformal_forced_principal_mode_ne_zero hR F hFs hb hL hhol
      hinj hC hK e he hsource hes 0 w ((E₀ : ℂ) • w) hforced n hn
    simp only [lp.coeFn_zero, Pi.zero_apply, mul_zero, sub_zero] at hm
    rw [if_neg hn, zero_mul, add_zero, hm]
    have hwgt : (sobWeight n : ℂ) ≠ 0 := by exact_mod_cast (sobWeight_pos n).ne'
    rw [← mul_assoc, inv_mul_cancel₀ hwgt, one_mul]

include hb hhol hinj hC hK e he hsource hes in
/-- The normalized trace of a true original Neumann resonant vector
belongs to H1. No regularity of the resonant vector beyond actual H1 is
assumed, and no condition is imposed on its zero Fourier coefficient. -/
theorem localConformal_resonant_halfTrace_sobolev_one
    {E₀ : ℝ} {w : NeumannH1 ΩF} (hw : w ∈ h1ResonantSpace ΩF E₀) :
    IsSobolevSeq 1 (QF w : ℤ → ℂ) := by
  rw [localConformal_resonant_halfTrace_factorization hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hw]
  have hmass : IsSobolevSeq 1
      (sobolevSmoothing 1 zero_le_one (MF ((E₀ : ℂ) • w)) : ℤ → ℂ) :=
    isSobolevSeq_fromL2 1 _
  simpa only [lp.coeFn_add] using
    isSobolevSeq_add hmass (resonant_zeroMode_sobolev 1 (QF w))

/-- The actual compatibility vector, built from the genuine finite
Fourier chart adjoint and the original normalized resonant trace. -/
def localConformalResonantCompatibilityVector {d : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z) {E₀ : ℝ}
    (w : h1ResonantSpace ΩF E₀) : H₀ᗮ :=
  ContinuousLinearMap.adjoint
    (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r))
      (QF (w : NeumannH1 ΩF))

/-- The compatibility vector tests precisely the actual chart image
against the original resonant normalized trace. -/
theorem localConformalResonantCompatibilityVector_inner {d : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z) {E₀ : ℝ}
    (w : h1ResonantSpace ΩF E₀) (z : H₀ᗮ) :
    ⟪localConformalResonantCompatibilityVector hR F hFs hL u v w, z⟫_ℂ =
      ⟪QF (w : NeumannH1 ΩF),
        (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) z⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_left _ z _

include hb hhol hinj hC hK e he hsource hes in
theorem localConformalResonantCompatibilityVector_sobolev_one {d : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {E₀ : ℝ} (w : h1ResonantSpace ΩF E₀) :
    IsSobolevSeq 1
      ((localConformalResonantCompatibilityVector hR F hFs hL u v w : L2Z) : ℤ → ℂ) := by
  exact finite_fourier_chart_adjoint_preserves_sobolev u v hu _
    (localConformal_resonant_halfTrace_sobolev_one hR F hFs hb hL hhol hinj hC hK
      e he hsource hes w.property)

include hb hhol hinj hC hK e he hsource hes in
theorem localConformalResonantCompatibilityVector_sobolev_of_le_one {d : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {E₀ : ℝ} (w : h1ResonantSpace ΩF E₀) {s : ℝ} (hs : s ≤ 1) :
    IsSobolevSeq s
      ((localConformalResonantCompatibilityVector hR F hFs hL u v w : L2Z) : ℤ → ℂ) :=
  (sobNormSq_mono hs
    (localConformalResonantCompatibilityVector_sobolev_one hR F hFs hb hL hhol hinj hC hK
      e he hsource hes u v hu w)).1

include hb hhol hinj hC hK e he hsource hes in
theorem localConformalResonantCompatibilityVector_sobolev_half {d : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {E₀ : ℝ} (w : h1ResonantSpace ΩF E₀) :
    IsSobolevSeq (1 / 2 : ℝ)
      ((localConformalResonantCompatibilityVector hR F hFs hL u v w : L2Z) : ℤ → ℂ) :=
  localConformalResonantCompatibilityVector_sobolev_of_le_one hR F hFs hb hL hhol hinj hC hK
    e he hsource hes u v hu w (by norm_num)

include hb hhol hinj hC hK e he hsource hes in
theorem localConformalResonantCompatibilityVector_sobolev_quarter {d : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {E₀ : ℝ} (w : h1ResonantSpace ΩF E₀) :
    IsSobolevSeq (1 / 4 : ℝ)
      ((localConformalResonantCompatibilityVector hR F hFs hL u v w : L2Z) : ℤ → ℂ) :=
  localConformalResonantCompatibilityVector_sobolev_of_le_one hR F hFs hb hL hhol hinj hC hK
    e he hsource hes u v hu w (by norm_num)

include hb hhol hinj hC hK e he hsource hes in
/-- The genuine finite resonant compatibility projection preserves every
order at most one. The η vectors in this statement are the actual T*Qw,
not independently given vectors with assumed Sobolev regularity. -/
theorem localConformal_resonant_compatibility_projection_preserves_sobolev {d m : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {E₀ : ℝ} (w : Fin m → h1ResonantSpace ΩF E₀)
    {s : ℝ} (hs : s ≤ 1) (z : H₀ᗮ)
    (hz : IsSobolevSeq s ((z : L2Z) : ℤ → ℂ)) :
    IsSobolevSeq s
      (((Submodule.span ℂ (range fun j =>
        localConformalResonantCompatibilityVector hR F hFs hL u v (w j)))ᗮ.starProjection z :
          L2Z) : ℤ → ℂ) := by
  exact compatibility_projection_preserves_sobolev
    (fun j => localConformalResonantCompatibilityVector hR F hFs hL u v (w j))
    (fun j => localConformalResonantCompatibilityVector_sobolev_of_le_one hR F hFs hb hL
      hhol hinj hC hK e he hsource hes u v hu (w j) hs) z hz

include hb hhol hinj hC hK e he hsource hes in
theorem localConformal_resonant_compatibility_projection_preserves_one {d m : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {E₀ : ℝ} (w : Fin m → h1ResonantSpace ΩF E₀) (z : H₀ᗮ)
    (hz : IsSobolevSeq 1 ((z : L2Z) : ℤ → ℂ)) :
    IsSobolevSeq 1
      (((Submodule.span ℂ (range fun j =>
        localConformalResonantCompatibilityVector hR F hFs hL u v (w j)))ᗮ.starProjection z :
          L2Z) : ℤ → ℂ) :=
  localConformal_resonant_compatibility_projection_preserves_sobolev hR F hFs hb hL
    hhol hinj hC hK e he hsource hes u v hu w le_rfl z hz

include hb hhol hinj hC hK e he hsource hes in
theorem localConformal_resonant_compatibility_projection_preserves_half {d m : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {E₀ : ℝ} (w : Fin m → h1ResonantSpace ΩF E₀) (z : H₀ᗮ)
    (hz : IsSobolevSeq (1 / 2 : ℝ) ((z : L2Z) : ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ)
      (((Submodule.span ℂ (range fun j =>
        localConformalResonantCompatibilityVector hR F hFs hL u v (w j)))ᗮ.starProjection z :
          L2Z) : ℤ → ℂ) :=
  localConformal_resonant_compatibility_projection_preserves_sobolev hR F hFs hb hL
    hhol hinj hC hK e he hsource hes u v hu w (by norm_num) z hz

include hb hhol hinj hC hK e he hsource hes in
theorem localConformal_resonant_compatibility_projection_preserves_quarter {d m : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hu : ∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite)
    {E₀ : ℝ} (w : Fin m → h1ResonantSpace ΩF E₀) (z : H₀ᗮ)
    (hz : IsSobolevSeq (1 / 4 : ℝ) ((z : L2Z) : ℤ → ℂ)) :
    IsSobolevSeq (1 / 4 : ℝ)
      (((Submodule.span ℂ (range fun j =>
        localConformalResonantCompatibilityVector hR F hFs hL u v (w j)))ᗮ.starProjection z :
          L2Z) : ℤ → ℂ) :=
  localConformal_resonant_compatibility_projection_preserves_sobolev hR F hFs hb hL
    hhol hinj hC hK e he hsource hes u v hu w (by norm_num) z hz

end PhysicalCoordinates

end PolyaNeumann

end
