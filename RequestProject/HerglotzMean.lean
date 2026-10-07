module

public import RequestProject.HerglotzPoincare
public import RequestProject.HerglotzForm
public import Mathlib.Analysis.Complex.Isometry

/-!
# Mean values of Herglotz coefficients over discs

The average of a plane wave over a disc is a fixed multiple of its value at the centre
(`integral_ball_planeWave`, by translation and rotation invariance of Lebesgue measure), hence
`∫_{B(z₁, r)} F_m = j(k, r) F_m(z₁)` for every Herglotz coefficient (`integral_ball_herglotzCoeff`).
In particular, if `F_m(z₁) = 0` then `F_m` has zero mean over every disc centred at `z₁`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- The disc integral `j(k, r) = ∫_{B(0, r)} e^{-ik Re u} du`. -/
def ballMean (k r : ℝ) : ℂ := ∫ u in ball (0 : ℂ) r, planeWave k u 0

lemma planeWave_rotate (k : ℝ) (u : ℂ) (φ : ℝ) :
    planeWave k u φ = planeWave k (u * Complex.exp (-(φ * Complex.I))) 0 := by
  unfold planeWave
  simp

lemma continuous_planeWave_uncurry (k : ℝ) :
    Continuous fun p : ℂ × ℝ => planeWave k p.1 p.2 := by
  unfold planeWave
  fun_prop

/-- Translation: `∫_{B(z₁, r)} f = ∫_{B(0, r)} f(z₁ + ·)`. -/
lemma setIntegral_ball_translate (f : ℂ → ℂ) (z₁ : ℂ) (r : ℝ) :
    ∫ z in ball z₁ r, f z = ∫ u in ball (0 : ℂ) r, f (z₁ + u) := by
  have hpre : (fun u => z₁ + u) ⁻¹' ball z₁ r = ball (0 : ℂ) r := by
    ext u; simp [dist_eq_norm]
  rw [← hpre, (measurePreserving_add_left volume z₁).setIntegral_preimage_emb
    (measurableEmbedding_addLeft z₁) f (ball z₁ r)]

/-- Rotation invariance of the disc integral of a plane wave. -/
lemma integral_ball_planeWave_zero (k r : ℝ) (φ : ℝ) :
    ∫ u in ball (0 : ℂ) r, planeWave k u φ = ballMean k r := by
  set c : Circle := Circle.exp (-φ)
  have hrot : ∀ u, rotation c u = u * Complex.exp (-(φ * Complex.I)) := fun u => by
    rw [rotation_apply, Circle.coe_exp]
    push_cast
    ring_nf
  have hpre : (rotation c) ⁻¹' ball (0 : ℂ) r = ball (0 : ℂ) r := by
    ext u; simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  have hmp := LinearIsometryEquiv.measurePreserving (rotation c)
  have hemb := (rotation c).toHomeomorph.measurableEmbedding
  unfold ballMean
  conv_lhs => rw [← hpre]
  simp_rw [planeWave_rotate k _ φ]
  have := hmp.setIntegral_preimage_emb hemb (fun v => planeWave k v 0) (ball (0 : ℂ) r)
  simp only [hrot] at this
  convert this using 2

/-- **Disc integral of a plane wave.** -/
lemma integral_ball_planeWave (k r : ℝ) (z₁ : ℂ) (φ : ℝ) :
    ∫ z in ball z₁ r, planeWave k z φ = planeWave k z₁ φ * ballMean k r := by
  rw [setIntegral_ball_translate, ← integral_ball_planeWave_zero k r φ, ← integral_const_mul]
  simp_rw [planeWave_add]

/-- **Mean value property of Herglotz coefficients.** -/
theorem integral_ball_herglotzCoeff {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π))
    (k : ℝ) (m : ℤ) (z₁ : ℂ) (r : ℝ) :
    ∫ z in ball z₁ r, herglotzCoeff k a m z = ballMean k r * herglotzCoeff k a m z₁ := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set e : ℝ → ℂ := fun φ => Complex.exp (-((m : ℂ) * φ * Complex.I)) with he
  have hec : Continuous e := by rw [he]; fun_prop
  have hen : ∀ φ, ‖e φ‖ = 1 := fun φ => by
    rw [he, Complex.norm_exp]; simp
  have hai : Integrable a (volume.restrict (Ioc 0 (2 * π))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mp ha
  haveI : IsFiniteMeasure (volume.restrict (ball z₁ r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  set F : ℂ → ℝ → ℂ := fun z φ => e φ * (a φ * planeWave k z φ) with hF
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (ball z₁ r)).prod (volume.restrict (Ioc 0 (2 * π)))) := by
    have hg : Integrable (fun p : ℂ × ℝ => (1 : ℝ) * ‖a p.2‖)
        ((volume.restrict (ball z₁ r)).prod (volume.restrict (Ioc 0 (2 * π)))) :=
      (integrable_const (1 : ℝ)).mul_prod hai.norm
    refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : ℂ × ℝ => a p.2)
          ((volume.restrict (ball z₁ r)).prod (volume.restrict (Ioc 0 (2 * π)))) :=
        hai.aestronglyMeasurable.comp_snd
      have h2 : Continuous fun p : ℂ × ℝ => e p.2 := hec.comp continuous_snd
      have h3 := continuous_planeWave_uncurry k
      exact h2.aestronglyMeasurable.mul (h1.mul h3.aestronglyMeasurable)
    · simp only [Function.uncurry, hF, norm_mul, hen, norm_planeWave, one_mul, mul_one, le_refl]
  have hswap := integral_integral_swap hFi
  unfold herglotzCoeff
  simp_rw [intervalIntegral.integral_of_le h2π]
  rw [integral_const_mul, hswap]
  have hin : ∀ φ, ∫ z in ball z₁ r, F z φ = e φ * (a φ * (planeWave k z₁ φ * ballMean k r)) :=
    fun φ => by
      simp only [hF]
      rw [integral_const_mul, integral_const_mul, integral_ball_planeWave]
  have hre : ∀ φ, e φ * (a φ * (planeWave k z₁ φ * ballMean k r)) =
      (e φ * (a φ * planeWave k z₁ φ)) * ballMean k r := fun φ => by ring
  simp_rw [hin, hre, integral_mul_const]
  simp only [he]
  ring

end PolyaNeumann
