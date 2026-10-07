module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import RequestProject.LocalConformalH1
public import RequestProject.SmoothCompactExtension
public import RequestProject.RiemannMappingInterior

/-!
# Finite energy of the actual interior Riemann map

Only holomorphicity and injectivity on the open disk are used below.
The area change of variables gives an integrable squared derivative for
a bounded image. Bounded values and those derivatives give an element
of the actual weak-gradient H¹ space. Integration by parts is localized
near each compact interior test support; no closed-disk continuity or
extension across the circle is an input or a conclusion.

The complex Dirichlet energy is the area of the image. The sum of the
two real gradient energies is twice that area.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

/-- Local smoothness suffices for the actual weak-gradient identities:
each test is supported in a compact subset of the open domain. -/
theorem isWeakGradient_of_contDiffOn {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hu : MemLp F 2 (volume.restrict U))
    (hg : ∀ i : Fin 2, MemLp (fun z => fderiv ℝ F z (coordDir i)) 2
      (volume.restrict U)) :
    IsWeakGradient U (hu.toLp F) (fun i => (hg i).toLp _) := by
  intro φ hφ i
  obtain ⟨G, hG, hGF⟩ := exists_smooth_compact_extension
    hφ.2.1 hU hφ.2.2 hFs
  have hGu : MemLp G 2 (volume.restrict U) := hG.memLp' 2
  have hGg : ∀ j : Fin 2, MemLp (fun z => fderiv ℝ G z (coordDir j)) 2
      (volume.restrict U) := fun j => (hG.dirD (coordDir j)).memLp' 2
  have hweak := isWeakGradient_of_smooth hG.1 hGu hGg φ hφ i
  have hleft :
      (fun z => ((hGu.toLp G : L2 U) : ℂ → ℂ) z *
          fderiv ℝ φ z (coordDir i)) =ᵐ[volume.restrict U]
        fun z => F z * fderiv ℝ φ z (coordDir i) := by
    filter_upwards [hGu.coeFn_toLp] with z hz
    rw [hz]
    by_cases hzs : z ∈ tsupport φ
    · rw [(hGF z hzs).self_of_nhds]
    · simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hzs,
        ContinuousLinearMap.zero_apply, mul_zero]
  have hright :
      (fun z => (((hGg i).toLp _ : L2 U) : ℂ → ℂ) z * φ z)
        =ᵐ[volume.restrict U]
        fun z => fderiv ℝ F z (coordDir i) * φ z := by
    filter_upwards [(hGg i).coeFn_toLp] with z hz
    rw [hz]
    by_cases hzs : z ∈ tsupport φ
    · rw [(hGF z hzs).fderiv_eq (𝕜 := ℝ)]
    · simp only [image_eq_zero_of_notMem_tsupport hzs, mul_zero]
  rw [integral_congr_ae hleft, integral_congr_ae hright] at hweak
  have huleft :
      (fun z => ((hu.toLp F : L2 U) : ℂ → ℂ) z *
          fderiv ℝ φ z (coordDir i)) =ᵐ[volume.restrict U]
        fun z => F z * fderiv ℝ φ z (coordDir i) := by
    filter_upwards [hu.coeFn_toLp] with z hz
    rw [hz]
  have hgright :
      (fun z => (((hg i).toLp _ : L2 U) : ℂ → ℂ) z * φ z)
        =ᵐ[volume.restrict U]
        fun z => fderiv ℝ F z (coordDir i) * φ z := by
    filter_upwards [(hg i).coeFn_toLp] with z hz
    rw [hz]
  rw [integral_congr_ae huleft, integral_congr_ae hgright]
  exact hweak

/-- Change of variables on the open disk gives the genuine complex
Dirichlet energy, without any assertion about values on the circle. -/
theorem interiorConformal_deriv_energy (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) :
    (∫ z in ball (0 : ℂ) 1, ‖deriv F z‖ ^ 2) =
      (volume (F '' ball (0 : ℂ) 1)).toReal := by
  have h := localConformal_integral_image isOpen_ball hF hinj (fun _ : ℂ => (1 : ℝ))
  simpa only [mul_one, integral_const, measureReal_def,
    Measure.restrict_apply_univ, smul_eq_mul] using h.symm

/-- Bounded image makes the area weight genuinely integrable. -/
theorem interiorConformal_deriv_sq_integrable (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    IntegrableOn (fun z => ‖deriv F z‖ ^ 2) (ball (0 : ℂ) 1) := by
  have hconst : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (F '' ball (0 : ℂ) 1) :=
    integrableOn_const hb.measure_lt_top.ne
  simpa only [mul_one] using localConformal_integrable_weight isOpen_ball hF hinj hconst

theorem interiorConformal_deriv_memLp (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    MemLp (deriv F) 2 (volume.restrict (ball (0 : ℂ) 1)) := by
  have hm : AEStronglyMeasurable (deriv F) (volume.restrict (ball (0 : ℂ) 1)) :=
    (hF.deriv isOpen_ball).continuousOn.aestronglyMeasurable measurableSet_ball
  exact (memLp_two_iff_integrable_sq_norm hm).mpr
    (interiorConformal_deriv_sq_integrable F hF hinj hb)

/-- A bounded holomorphic image gives the actual L² value class. -/
theorem interiorConformal_value_memLp (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    MemLp F 2 (volume.restrict (ball (0 : ℂ) 1)) := by
  letI : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1)).measure_lt_top⟩
  obtain ⟨B, _, hB⟩ := hb.subset_ball_lt 0 (0 : ℂ)
  apply MemLp.of_bound (hF.continuousOn.aestronglyMeasurable measurableSet_ball) B
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hzB := hB (show F z ∈ F '' ball (0 : ℂ) 1 from ⟨z, hz, rfl⟩)
  have hnorm : ‖F z‖ < B := by
    simpa only [mem_ball, dist_zero_right] using hzB
  exact hnorm.le

/-- The two real derivatives of a holomorphic map are `F′` and `i F′`. -/
theorem interiorConformal_fderiv (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (v : ℂ) :
    fderiv ℝ F z v = deriv F z * v := by
  rw [(hF.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  change fderiv ℂ F z v = _
  exact fderiv_eq_deriv_mul

theorem interiorConformal_realGradient_memLp (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) (i : Fin 2) :
    MemLp (fun z => fderiv ℝ F z (coordDir i)) 2
      (volume.restrict (ball (0 : ℂ) 1)) := by
  have hd := (interiorConformal_deriv_memLp F hF hinj hb).mul_const (coordDir i)
  refine MemLp.ae_eq ?_ hd
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact (interiorConformal_fderiv F hF hz (coordDir i)).symm

theorem interiorConformal_isWeakGradient (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    IsWeakGradient (ball (0 : ℂ) 1)
      ((interiorConformal_value_memLp F hF hb).toLp F)
      (fun i => (interiorConformal_realGradient_memLp F hF hinj hb i).toLp _) := by
  have hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) 1) :=
    (hF.contDiffOn isOpen_ball).restrict_scalars ℝ
  exact isWeakGradient_of_contDiffOn isOpen_ball hFs
    (interiorConformal_value_memLp F hF hb)
    (interiorConformal_realGradient_memLp F hF hinj hb)

/-- The genuine H¹ vector of the interior conformal map. -/
def interiorConformalH1 (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    NeumannH1 (ball (0 : ℂ) 1) :=
  h1Vector (interiorConformal_isWeakGradient F hF hinj hb)

theorem h1Value_interiorConformalH1 (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    h1Value (ball (0 : ℂ) 1) (interiorConformalH1 F hF hinj hb) =
      (interiorConformal_value_memLp F hF hb).toLp F :=
  h1Value_h1Vector (interiorConformal_isWeakGradient F hF hinj hb)

theorem h1Gradient_interiorConformalH1 (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) (i : Fin 2) :
    h1Gradient (ball (0 : ℂ) 1) i (interiorConformalH1 F hF hinj hb) =
      (interiorConformal_realGradient_memLp F hF hinj hb i).toLp _ :=
  h1Gradient_h1Vector (interiorConformal_isWeakGradient F hF hinj hb) i

theorem h1Value_interiorConformalH1_ae (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    (h1Value (ball (0 : ℂ) 1) (interiorConformalH1 F hF hinj hb) : ℂ → ℂ)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)] F := by
  rw [h1Value_interiorConformalH1]
  exact (interiorConformal_value_memLp F hF hb).coeFn_toLp

theorem h1Gradient_interiorConformalH1_ae (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) (i : Fin 2) :
    (h1Gradient (ball (0 : ℂ) 1) i (interiorConformalH1 F hF hinj hb) : ℂ → ℂ)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)] fun z => deriv F z * coordDir i := by
  rw [h1Gradient_interiorConformalH1]
  filter_upwards [(interiorConformal_realGradient_memLp F hF hinj hb i).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  rw [hz, interiorConformal_fderiv F hF hzD]

theorem norm_sq_h1Value_interiorConformalH1 (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    ‖h1Value (ball (0 : ℂ) 1) (interiorConformalH1 F hF hinj hb)‖ ^ 2 =
      ∫ z in ball (0 : ℂ) 1, ‖F z‖ ^ 2 := by
  rw [h1Value_interiorConformalH1, norm_sq_toLp_eq_integral]

theorem norm_sq_h1Gradient_interiorConformalH1 (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) (i : Fin 2) :
    ‖h1Gradient (ball (0 : ℂ) 1) i (interiorConformalH1 F hF hinj hb)‖ ^ 2 =
      (volume (F '' ball (0 : ℂ) 1)).toReal := by
  rw [h1Gradient_interiorConformalH1, norm_sq_toLp_eq_integral]
  calc
    (∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ F z (coordDir i)‖ ^ 2) =
        ∫ z in ball (0 : ℂ) 1, ‖deriv F z‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      have hi : ‖coordDir i‖ = 1 := by fin_cases i <;> simp [coordDir]
      change ‖fderiv ℝ F z (coordDir i)‖ ^ 2 = ‖deriv F z‖ ^ 2
      rw [interiorConformal_fderiv F hF hz, norm_mul, hi, mul_one]
    _ = _ := interiorConformal_deriv_energy F hF hinj

/-- The real two-coordinate Dirichlet energy has the required factor two. -/
theorem gradientEnergy_interiorConformalH1 (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i
      (interiorConformalH1 F hF hinj hb)‖ ^ 2) =
      2 * (volume (F '' ball (0 : ℂ) 1)).toReal := by
  rw [Fin.sum_univ_two, norm_sq_h1Gradient_interiorConformalH1,
    norm_sq_h1Gradient_interiorConformalH1]
  ring

theorem norm_sq_interiorConformalH1 (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    ‖interiorConformalH1 F hF hinj hb‖ ^ 2 =
      (∫ z in ball (0 : ℂ) 1, ‖F z‖ ^ 2) +
        2 * (volume (F '' ball (0 : ℂ) 1)).toReal := by
  rw [h1_norm_sq, norm_sq_h1Value_interiorConformalH1,
    gradientEnergy_interiorConformalH1]

/-- The energy of a supplied actual map onto the physical domain. -/
theorem riemannMapping_deriv_energy {Ω : Set ℂ} (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (himage : F '' ball (0 : ℂ) 1 = Ω) :
    (∫ z in ball (0 : ℂ) 1, ‖deriv F z‖ ^ 2) = (volume Ω).toReal := by
  simpa only [himage] using interiorConformal_deriv_energy F hF hinj

/-- The genuine interior existence theorem supplies a map of finite
energy and its actual H¹ vector. No boundary conclusion is added. -/
theorem exists_interior_conformal_map_h1 {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ (F : ℂ → ℂ) (u : NeumannH1 (ball (0 : ℂ) 1)),
      DifferentiableOn ℂ F (ball (0 : ℂ) 1) ∧
      InjOn F (ball (0 : ℂ) 1) ∧ F '' ball (0 : ℂ) 1 = Ω ∧
      (h1Value (ball (0 : ℂ) 1) u : ℂ → ℂ)
        =ᵐ[volume.restrict (ball (0 : ℂ) 1)] F ∧
      (∀ i : Fin 2, (h1Gradient (ball (0 : ℂ) 1) i u : ℂ → ℂ)
        =ᵐ[volume.restrict (ball (0 : ℂ) 1)] fun z => deriv F z * coordDir i) ∧
      (∫ z in ball (0 : ℂ) 1, ‖deriv F z‖ ^ 2) = (volume Ω).toReal ∧
      (∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i u‖ ^ 2) =
        2 * (volume Ω).toReal := by
  obtain ⟨F, hF, hinj, himage⟩ := exists_interior_conformal_map Ω hΩ hb hsc
  have hbF : Bornology.IsBounded (F '' ball (0 : ℂ) 1) := himage.symm ▸ hb
  refine ⟨F, interiorConformalH1 F hF hinj hbF, hF, hinj, himage,
    h1Value_interiorConformalH1_ae F hF hinj hbF,
    h1Gradient_interiorConformalH1_ae F hF hinj hbF,
    riemannMapping_deriv_energy F hF hinj himage, ?_⟩
  simpa only [himage] using gradientEnergy_interiorConformalH1 F hF hinj hbF

end PolyaNeumann

end
