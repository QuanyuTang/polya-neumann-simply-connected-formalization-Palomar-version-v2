module

public import RequestProject.DiskHalfTrace

/-!
# Harmonic tests in the actual weak disk equation

The compact harmonic extensions are actual H¹ test vectors. Their weak
gradient pairing gives the Fourier coefficients of the genuine trace,
and their normalized half traces are single Fourier basis vectors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

local instance diskWeakModeTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

def diskHolomorphicH1Test (m : ℕ) : NeumannH1 (ball (0 : ℂ) 1) :=
  smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskHolomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)⟩

def diskAntiholomorphicH1Test (m : ℕ) : NeumannH1 (ball (0 : ℂ) 1) :=
  smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

theorem diskH1Gradient_holomorphicTest (m : ℕ) :
    diskH1Gradient (diskHolomorphicH1Test m) = diskHolomorphicGradient m := rfl

theorem diskH1Gradient_antiholomorphicTest (m : ℕ) :
    diskH1Gradient (diskAntiholomorphicH1Test m) = diskAntiholomorphicGradient m := rfl

theorem disk_gradient_form_holomorphicTest (m : ℕ)
    (u : NeumannH1 (ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ⟪h1Gradient (ball (0 : ℂ) 1) i (diskHolomorphicH1Test m),
      h1Gradient (ball (0 : ℂ) 1) i u⟫_ℂ) =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (m : ℤ) := by
  have h := disk_h1_fourier_green_pos m u
  rw [← diskH1Gradient_holomorphicTest, PiLp.inner_apply] at h
  exact h

theorem disk_gradient_form_antiholomorphicTest (m : ℕ)
    (u : NeumannH1 (ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ⟪h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m),
      h1Gradient (ball (0 : ℂ) 1) i u⟫_ℂ) =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (-(m : ℤ)) := by
  have h := disk_h1_fourier_green_neg m u
  rw [← diskH1Gradient_antiholomorphicTest, PiLp.inner_apply] at h
  exact h

private theorem twoPi_fourier_mode (n : ℤ) (θ : ℝ) :
    fourier (T := 2 * π) n (θ : AddCircle (2 * π)) =
      Complex.exp ((n : ℂ) * Complex.I * θ) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem fourierCoeffOn_twoPi_exp (n k : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => Complex.exp ((n : ℂ) * Complex.I * θ)) k =
      (Pi.single n (1 : ℂ) : ℤ → ℂ) k := by
  have hm : (fun θ : ℝ => Complex.exp ((n : ℂ) * Complex.I * θ)) =
      (fun θ : ℝ => fourier (T := 2 * π) n (θ : AddCircle (2 * π))) := by
    funext θ
    exact (twoPi_fourier_mode n θ).symm
  have hl : AddCircle.liftIoc (2 * π) 0
      (fun θ : ℝ => fourier (T := 2 * π) n (θ : AddCircle (2 * π))) =
      fourier (T := 2 * π) n := by
    funext q
    change fourier n (((AddCircle.equivIoc (2 * π) 0 q : ℝ)) : AddCircle (2 * π)) = _
    exact congrArg (fourier n) ((AddCircle.equivIoc (2 * π) 0).symm_apply_apply q)
  have hc := fourierCoeff_liftIoc_eq (T := 2 * π) (a := 0)
    (fun θ => Complex.exp ((n : ℂ) * Complex.I * θ)) k
  simp only [zero_add] at hc
  rw [← hc, hm, hl, fourierCoeff_fourier]

theorem diskHalfTrace_smooth_fourier_test (f : smoothTraceTests) (n : ℤ)
    (hf : ∀ θ, f (circleMap 0 1 θ) = Complex.exp ((n : ℂ) * Complex.I * θ)) :
    diskHalfTrace (smoothTraceH1 (ball (0 : ℂ) 1) f) =
      ((Real.sqrt (sobWeight n) : ℂ) * (Real.sqrt (2 * π) : ℂ)) • stdBasisZ n := by
  have hae : (diskH1Trace (smoothTraceH1 (ball (0 : ℂ) 1) f) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))]
      (fun θ => Complex.exp ((n : ℂ) * Complex.I * θ)) := by
    have h := h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
      unitCircle_isBoundaryParam f
    filter_upwards [h] with θ hθ
    exact hθ.trans (hf θ)
  have hc := fourierCoeffOn_congr_ae two_pi_pos hae
  apply lp.ext
  funext k
  simp only [diskHalfTrace_apply, boundaryFourier_apply,
    congrFun hc k, fourierCoeffOn_twoPi_exp, stdBasisZ_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases hkn : k = n
  · subst k
    simp [sobWeight]
  · simp [hkn]

theorem diskHalfTrace_holomorphicTest (m : ℕ) :
    diskHalfTrace (diskHolomorphicH1Test m) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * (Real.sqrt (2 * π) : ℂ)) •
        stdBasisZ (m : ℤ) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  change diskHarmonicCutoff (diskHolomorphicMode m) (circleMap 0 1 θ) = _
  rw [diskHarmonicCutoff_eq_closedDisk _
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num) θ)),
    diskHolomorphicMode_unitCircle]
  simp only [Int.cast_natCast]

theorem diskHalfTrace_antiholomorphicTest (m : ℕ) :
    diskHalfTrace (diskAntiholomorphicH1Test m) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt (2 * π) : ℂ)) •
        stdBasisZ (-(m : ℤ)) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  change diskHarmonicCutoff (diskAntiholomorphicMode m) (circleMap 0 1 θ) = _
  rw [diskHarmonicCutoff_eq_closedDisk _
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num) θ)),
    diskAntiholomorphicMode_unitCircle]
  simp only [Int.cast_neg, Int.cast_natCast]
  congr 1
  ring

end PolyaNeumann

end
