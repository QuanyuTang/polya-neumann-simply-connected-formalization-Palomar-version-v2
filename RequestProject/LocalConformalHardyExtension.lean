module

public import RequestProject.DiskHardyExtension
public import RequestProject.LocalConformalH1Equiv
public import RequestProject.LocalConformalTrace
public import RequestProject.LocalConformalCauchyRiemann

/-!
# The genuine supplied-coordinate Hardy extension in the physical domain

The disk harmonic extension is transported by the proved inverse of the actual
H¹ pullback. Every input produces a physical H¹ vector. Its normalized circle
trace is exactly the nonpositive Fourier projection, with the zero mode included.
The series converges in the physical H¹ norm, and the inverse-coordinate estimate
gives its norm bound. The initial conformal map is supplied explicitly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric

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

/-- The actual disk extension followed by the actual physical H¹ pushforward. -/
def localConformalHardyH1Extension :
    L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes).comp
    diskHardyExtension

@[simp] theorem localConformalH1Pullback_hardyExtension (b : L2Z) :
    localConformalH1Pullback hR F hFs hL
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) =
        diskHardyExtension b := by
  exact localConformalH1Pullback_pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes
    (diskHardyExtension b)

/-- The exact physical coordinate half trace of the completed extension. -/
theorem localConformalDiskHalfTrace_hardyExtension (b : L2Z) :
    localConformalDiskHalfTrace hR F hFs hL
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) =
        (1 - posProj) b := by
  change diskHalfTrace (localConformalH1Pullback hR F hFs hL
    (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b)) = _
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHalfTrace_diskHardyExtension b

theorem localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive (b : L2Z)
    (hneg : ∀ n : ℤ, 0 < n → b n = 0) :
    localConformalDiskHalfTrace hR F hFs hL
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) = b := by
  change diskHalfTrace (localConformalH1Pullback hR F hFs hL
    (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b)) = _
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hneg

theorem norm_localConformalHardyH1Extension_apply_le (b : L2Z) :
    ‖localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b‖ ≤
      Real.sqrt (max (K ^ 2) 1) * ‖b‖ := by
  calc
    _ ≤ Real.sqrt (max (K ^ 2) 1) * ‖diskHardyExtension b‖ :=
      norm_localConformalH1Pushforward_apply_le hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (diskHardyExtension b)
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_diskHardyExtension_apply_le b)
      (Real.sqrt_nonneg _)

theorem norm_localConformalHardyH1Extension_le :
    ‖localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes‖ ≤
      Real.sqrt (max (K ^ 2) 1) :=
  (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes).opNorm_le_bound
    (Real.sqrt_nonneg _)
    (norm_localConformalHardyH1Extension_apply_le hR F hFs hb hL hhol hinj hC hK e he hsource hes)

/-- The physical extension is a genuine H¹ limit of inverse-coordinate modes. -/
theorem localConformalHardyH1Extension_hasSum (b : L2Z) :
    HasSum (fun m : ℕ => (b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (diskAntiholomorphicH1Test m))
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) := by
  have h := (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes).hasSum
      (diskHardyExtension_hasSum b)
  simp only [map_smul] at h
  exact h

/-- The transported vector satisfies the actual physical weak CR equation. -/
theorem localConformalHardyH1Extension_cauchyRiemann (b : L2Z) :
    h1Gradient (F '' ball (0 : ℂ) 1) 0
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) =
      Complex.I • h1Gradient (F '' ball (0 : ℂ) 1) 1
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) := by
  apply (localConformalH1Pullback_antiholomorphic_iff hR F hFs hb hL hhol hinj hC
    (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b)).mp
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_cauchyRiemann b

/-- Distributional harmonicity holds for the physical completed H¹ vector. -/
theorem localConformalHardyH1Extension_weakHarmonic (b : L2Z) {φ : ℂ → ℂ}
    (hφ : TestFunction (F '' ball (0 : ℂ) 1) φ) :
    (∫ z in F '' ball (0 : ℂ) 1,
      (h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b)
        : ℂ → ℂ) z * lap φ z) = 0 :=
  h1_weakHarmonic_of_cauchyRiemann _
    (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK e he hsource hes b) hφ

end PolyaNeumann

end
