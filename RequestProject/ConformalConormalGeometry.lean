module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-!
# The physical conormal density in conformal circle coordinates

For `γ(θ) = F(r exp(iθ))`, the density `Du(γ(θ))(-iγ'(θ))`
is exactly the radial derivative of the conformal pullback in direction
`r exp(iθ)`. This includes the parameter Jacobian required by the physical
boundary integral. The statement only uses differentiability at the points
where the derivatives are evaluated.

On the disk the actual conormal derivative of `conj(z)^m` is `m conj(z)^m`,
the nonpositive Fourier-mode part of the harmonic principal symbol.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Complex
open scoped ComplexConjugate

/-- The conformal parametrization of a circle of radius `r`. -/
def conformalCircle (F : ℂ → ℂ) (r θ : ℝ) : ℂ :=
  F ((r : ℂ) * exp ((θ : ℂ) * I))

/-- The angular derivative of the actual conformal circle parametrization. -/
theorem hasDerivAt_conformalCircle {F : ℂ → ℂ} {r θ : ℝ}
    (hF : DifferentiableAt ℂ F ((r : ℂ) * exp ((θ : ℂ) * I))) :
    HasDerivAt (conformalCircle F r)
      (I * r * exp ((θ : ℂ) * I) * deriv F ((r : ℂ) * exp ((θ : ℂ) * I))) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (r : ℂ) * exp ((t : ℂ) * I))
      (r * (exp ((θ : ℂ) * I) * I)) θ := by
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    exact h2.cexp.const_mul (r : ℂ)
  have h := hF.hasDerivAt.comp θ h1
  convert h using 1
  ring

lemma deriv_conformalCircle {F : ℂ → ℂ} {r θ : ℝ}
    (hF : DifferentiableAt ℂ F ((r : ℂ) * exp ((θ : ℂ) * I))) :
    deriv (conformalCircle F r) θ =
      I * r * exp ((θ : ℂ) * I) * deriv F ((r : ℂ) * exp ((θ : ℂ) * I)) :=
  (hasDerivAt_conformalCircle hF).deriv

/-- Conformal pullback identifies the actual boundary conormal density
with the radial derivative in disk coordinates, including its full scale. -/
theorem conormal_conformalCircle_eq_pullback_radial
    {F u : ℂ → ℂ} {r θ : ℝ}
    (hF : DifferentiableAt ℂ F ((r : ℂ) * exp ((θ : ℂ) * I)))
    (hu : DifferentiableAt ℝ u (conformalCircle F r θ)) :
    fderiv ℝ u (conformalCircle F r θ) (-(I * deriv (conformalCircle F r) θ)) =
      fderiv ℝ (u ∘ F) ((r : ℂ) * exp ((θ : ℂ) * I))
        ((r : ℂ) * exp ((θ : ℂ) * I)) := by
  rw [fderiv_comp _ hu (hF.restrictScalars ℝ),
    ContinuousLinearMap.comp_apply, hF.fderiv_restrictScalars ℝ]
  change fderiv ℝ u (conformalCircle F r θ)
      (-(I * deriv (conformalCircle F r) θ)) =
    fderiv ℝ u (conformalCircle F r θ)
      ((fderiv ℂ F ((r : ℂ) * exp ((θ : ℂ) * I)))
        ((r : ℂ) * exp ((θ : ℂ) * I)))
  congr 1
  rw [deriv_conformalCircle hF, fderiv_eq_deriv_mul]
  calc
    _ = -(I * I) * ((r : ℂ) * exp ((θ : ℂ) * I) *
        deriv F ((r : ℂ) * exp ((θ : ℂ) * I))) := by ring
    _ = _ := by rw [I_mul_I]; ring

/-- Euler's radial identity for the actual antiholomorphic disk monomial. -/
theorem fderiv_conj_pow_radial (m : ℕ) (z : ℂ) :
    fderiv ℝ (fun w : ℂ => conj w ^ m) z z = (m : ℂ) * conj z ^ m := by
  rw [((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z)).pow m).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, nsmul_eq_mul, smul_eq_mul]
  cases m with
  | zero => simp
  | succ m =>
      simp only [Nat.succ_sub_one, pow_succ]
      ring

/-- On the actual unit-circle boundary, the physical conormal of the
nonpositive disk monomial has precisely its absolute-frequency multiplier. -/
theorem conormal_unitCircle_conj_pow (m : ℕ) (θ : ℝ) :
    fderiv ℝ (fun w : ℂ => conj w ^ m) (exp ((θ : ℂ) * I))
      (-(I * deriv (fun t : ℝ => exp ((t : ℂ) * I)) θ)) =
      (m : ℂ) * conj (exp ((θ : ℂ) * I)) ^ m := by
  have hd : HasDerivAt (fun t : ℝ => exp ((t : ℂ) * I))
      (exp ((θ : ℂ) * I) * I) θ := by
    have h : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    exact h.cexp
  have hnormal : -(I * deriv (fun t : ℝ => exp ((t : ℂ) * I)) θ) =
      exp ((θ : ℂ) * I) := by
    rw [hd.deriv]
    calc
      _ = -(I * I) * exp ((θ : ℂ) * I) := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [hnormal]
  exact fderiv_conj_pow_radial m _

/-- Zero tangential and conormal derivatives give the full zero
differential used in the classical Cauchy uniqueness theorem. -/
theorem clm_eq_zero_of_tangential_and_conormal_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : ℂ →L[ℝ] V) {d : ℂ} (hd : d ≠ 0)
    (hT : L d = 0) (hN : L (-(I * d)) = 0) : L = 0 := by
  have hI : L (I * d) = 0 := by
    rw [map_neg] at hN
    exact neg_eq_zero.mp hN
  ext w
  change L w = 0
  have hrep : w = (w / d).re • d + (w / d).im • (I * d) := by
    simp only [Complex.real_smul]
    calc
      w = (w / d) * d := (div_mul_cancel₀ w hd).symm
      _ = ((w / d).re + (w / d).im * I) * d := by rw [Complex.re_add_im]
      _ = _ := by ring
  rw [hrep, map_add, map_smul, map_smul, hT, hI, smul_zero, smul_zero, add_zero]

end PolyaNeumann
