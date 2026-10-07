module

public import RequestProject.LocalConformalTests
public import RequestProject.LocalConformalTrace
public import RequestProject.LocalConformalMassForcing
public import RequestProject.DiskWeakModes
public import RequestProject.NeumannNormalizedBoundary

/-!
# Harmonic-mode identities for the genuine Neumann weak equation

The test vectors are obtained from a smooth local inverse. Both their
gradient pairing and their mass pairing come from the actual physical H¹
space. The boundary load is the constructed conformal half trace.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

theorem h1Value_diskHolomorphicH1Test (m : ℕ) :
    h1Value (ball (0 : ℂ) 1) (diskHolomorphicH1Test m) = diskHolomorphicArea m :=
  h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskHolomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)⟩

theorem h1Value_diskAntiholomorphicH1Test (m : ℕ) :
    h1Value (ball (0 : ℂ) 1) (diskAntiholomorphicH1Test m) = diskAntiholomorphicArea m :=
  h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

include hb hhol hinj hC e he hsource hes in
theorem localConformal_weak_holomorphic_mode
    (E : ℝ) (b : L2Z) (u : NeumannH1 (F '' ball (0 : ℂ) 1))
    (hu : IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E b u)
    (m : ℕ) :
    (2 * π : ℂ) * (m : ℂ) *
      fourierCoeffOn two_pi_pos (localConformalDiskH1Trace hR F hFs hL u : ℝ → ℂ) (m : ℤ) -
        (E : ℂ) * (∫ z in ball (0 : ℂ) 1,
          (localConformalMassForcing hR F hFs hL hK u : ℂ → ℂ) z * conj z ^ m) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * (Real.sqrt (2 * π) : ℂ)) * b (m : ℤ) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test hR F hFs hb hL hhol hinj hC
    e he hsource hes (contDiff_diskHolomorphicMode m)
  have hp' : localConformalH1Pullback hR F hFs hL
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) = diskHolomorphicH1Test m := hp
  have hg := localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC
    (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) u
  have hm := localConformal_mass_pairing hR F hFs hb hL hhol hinj hC hK
    (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) u
  have hq : localConformalDiskHalfTrace hR F hFs hL
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * (Real.sqrt (2 * π) : ℂ)) • stdBasisZ (m : ℤ) := by
    change diskHalfTrace (localConformalH1Pullback hR F hFs hL
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)) = _
    rw [hp']
    exact diskHalfTrace_holomorphicTest m
  have hw := hu (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)
  rw [← hg, hm, hp', disk_gradient_form_holomorphicTest,
    h1Value_diskHolomorphicH1Test, inner_diskHolomorphicArea_eq_integral, hq] at hw
  simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
  exact hw

include hb hhol hinj hC e he hsource hes in
theorem localConformal_weak_antiholomorphic_mode
    (E : ℝ) (b : L2Z) (u : NeumannH1 (F '' ball (0 : ℂ) 1))
    (hu : IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E b u)
    (m : ℕ) :
    (2 * π : ℂ) * (m : ℂ) *
      fourierCoeffOn two_pi_pos (localConformalDiskH1Trace hR F hFs hL u : ℝ → ℂ) (-(m : ℤ)) -
        (E : ℂ) * (∫ z in ball (0 : ℂ) 1,
          (localConformalMassForcing hR F hFs hL hK u : ℂ → ℂ) z * z ^ m) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt (2 * π) : ℂ)) * b (-(m : ℤ)) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test hR F hFs hb hL hhol hinj hC
    e he hsource hes (contDiff_diskAntiholomorphicMode m)
  have hp' : localConformalH1Pullback hR F hFs hL
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) = diskAntiholomorphicH1Test m := hp
  have hg := localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC
    (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) u
  have hm := localConformal_mass_pairing hR F hFs hb hL hhol hinj hC hK
    (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) u
  have hq : localConformalDiskHalfTrace hR F hFs hL
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt (2 * π) : ℂ)) • stdBasisZ (-(m : ℤ)) := by
    change diskHalfTrace (localConformalH1Pullback hR F hFs hL
      (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)) = _
    rw [hp']
    exact diskHalfTrace_antiholomorphicTest m
  have hw := hu (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)
  rw [← hg, hm, hp', disk_gradient_form_antiholomorphicTest,
    h1Value_diskAntiholomorphicH1Test, inner_diskAntiholomorphicArea_eq_integral, hq] at hw
  simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
  exact hw

end

end PolyaNeumann

end
