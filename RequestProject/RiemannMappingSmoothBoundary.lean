module

public import RequestProject.RiemannMappingCaratheodory
public import RequestProject.RiemannMappingEnergy
public import RequestProject.SmoothDomain
public import RequestProject.LocalConformalH1
public import RequestProject.DiskGeometry
public import RequestProject.SmoothCompactExtension
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual physical Green function for boundary regularity

This file constructs the continuous physical inverse of the actual
closed-disk Riemann map. Its negative log modulus is the genuine
positive, zero-boundary Green function away from the actual pole.
Removing that logarithmic pole produces a harmonic function on the
whole physical domain whose actual boundary data are smooth. The
correction has a genuine H¹ realization. Actual smooth graph geometry
and the Schwarz lemma also supply positive interior tangent-ball
Green barriers, without assuming boundary derivatives.

These are consequences of the original physical domain assumptions.
They do not assert Kellogg--Warschawski regularity or a real smooth
collar extension. Smooth Dirichlet boundary regularity and real jet
extension remain necessary for those conclusions. The proved barrier
is available to exclude a zero boundary derivative once genuine
boundary differentiability has been constructed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff InnerProductSpace

/-- The actual inverse of the closed-disk extension on its physical
compact image. Its values outside that image are immaterial. -/
def riemannMappingClosedInverse (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.invFunOn (riemannMappingClosedExtension F) (closedBall (0 : ℂ) 1)

/-- The Green function with pole at the actual interior point `F 0`.
The total-function value at the pole is immaterial. -/
def riemannMappingGreen (F : ℂ → ℂ) (w : ℂ) : ℝ :=
  -Real.log ‖riemannMappingClosedInverse F w‖

/-- The actual analytic divided difference of the inverse at the pole;
its value at the pole is the genuine inverse derivative. -/
def riemannMappingInversePoleQuotient (F : ℂ → ℂ) : ℂ → ℂ :=
  dslope (riemannMappingClosedInverse F) (F 0)

/-- The logarithmic pole removed from the actual Green function. -/
def riemannMappingGreenCorrection (F : ℂ → ℂ) (w : ℂ) : ℝ :=
  -Real.log ‖riemannMappingInversePoleQuotient F w‖

private theorem fderiv_neg_log_norm_holomorphic
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun w => -Real.log ‖f w‖) z v =
      -⟪f z, deriv f z * v⟫_ℝ / ‖f z‖ ^ 2 := by
  have hr : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
  have hn : ‖f z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have ht := (hr.hasFDerivAt.norm_sq.log hn).const_mul (-(1 / 2 : ℝ))
  have heq : (fun w => -(1 / 2 : ℝ) * Real.log (‖f w‖ ^ 2)) =
      (fun w => -Real.log ‖f w‖) := by
    funext w
    rw [Real.log_pow]
    ring
  rw [heq] at ht
  have hh := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) ht.fderiv
  have hfv : fderiv ℝ f z v = deriv f z * v := by
    rw [hf.fderiv_restrictScalars ℝ]
    change fderiv ℂ f z v = _
    exact fderiv_eq_deriv_mul
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul, hfv] at hh
  calc
    _ = -(1 / 2 : ℝ) * ((‖f z‖ ^ 2)⁻¹ * (2 * ⟪f z, deriv f z * v⟫_ℝ)) := by
      simpa only [two_smul, two_mul] using hh
    _ = _ := by rw [div_eq_mul_inv]; ring

private theorem norm_fderiv_neg_log_norm_holomorphic_le
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) (v : ℂ) :
    ‖fderiv ℝ (fun w => -Real.log ‖f w‖) z v‖ ≤
      ‖deriv f z‖ * ‖v‖ / ‖f z‖ := by
  have hn : 0 < ‖f z‖ := norm_pos_iff.mpr hne
  rw [fderiv_neg_log_norm_holomorphic hf hne, norm_div, norm_neg,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (‖f z‖ * ‖deriv f z * v‖) / ‖f z‖ ^ 2 :=
      div_le_div_of_nonneg_right (norm_inner_le_norm _ _) (sq_nonneg _)
    _ = _ := by rw [norm_mul]; field_simp [hn.ne']

private theorem disk_mobius_norm_sq_difference (a b : ℂ) :
    ‖1 - star a * b‖ ^ 2 - ‖b - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, star_def]
  ring

private theorem disk_mobius_denominator_and_norm {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    1 - star a * b ≠ 0 ∧ ‖(b - a) / (1 - star a * b)‖ < 1 := by
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hb2 : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have hh := disk_mobius_norm_sq_difference a b
  have hprod := mul_pos ha2 hb2
  have hsq : ‖b - a‖ ^ 2 < ‖1 - star a * b‖ ^ 2 := by linarith
  have hnorm : ‖b - a‖ < ‖1 - star a * b‖ :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hd : 0 < ‖1 - star a * b‖ := (norm_nonneg _).trans_lt hnorm
  refine ⟨norm_ne_zero_iff.mp hd.ne', ?_⟩
  rw [norm_div]
  exact (div_lt_one hd).mpr hnorm

private theorem disk_mobius_norm_defect {a b : ℂ} {t : ℝ}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hbound : ‖(b - a) / (1 - star a * b)‖ ≤ t) :
    (1 - ‖a‖) ^ 2 / 2 * (1 - t) ≤ 1 - ‖b‖ := by
  let d : ℝ := ‖1 - star a * b‖
  have hdpos : 0 < d := norm_pos_iff.mpr (disk_mobius_denominator_and_norm ha hb).1
  have hnle : ‖b - a‖ ≤ t * d := by
    rw [norm_div] at hbound
    exact (div_le_iff₀ hdpos).mp hbound
  have hn2 : ‖b - a‖ ^ 2 ≤ t ^ 2 * d ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht0 hdpos.le)).mpr hnle
  have hlow : 1 - ‖a‖ ≤ d := by
    have ht := norm_sub_norm_le (1 : ℂ) (star a * b)
    rw [norm_one, norm_mul, norm_star] at ht
    have hp : ‖a‖ * ‖b‖ ≤ ‖a‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.le (norm_nonneg a)
    dsimp [d]
    simp only [star_def] at ht ⊢
    linarith
  have ht2 : t ^ 2 ≤ t := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left ht1 ht0
  have ht2one : t ^ 2 ≤ 1 := ht2.trans ht1
  have hsq : (1 - ‖a‖) ^ 2 ≤ d ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr ha.le) hdpos.le).mpr hlow
  have hmul := mul_le_mul_of_nonneg_right hsq (sub_nonneg.mpr ht2one)
  have hid := disk_mobius_norm_sq_difference a b
  have hb2 : 0 ≤ 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have hup : (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) ≤ 1 - ‖b‖ ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show 1 - ‖a‖ ^ 2 ≤ 1 by nlinarith [sq_nonneg ‖a‖]) hb2
  have hlast : (1 - ‖a‖) ^ 2 * (1 - t) ≤ (1 - ‖a‖) ^ 2 * (1 - t ^ 2) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left ht2 1) (sq_nonneg _)
  have hfirst : (1 - ‖a‖) ^ 2 * (1 - t ^ 2) ≤ 1 - ‖b‖ ^ 2 := by
    have hmiddle : d ^ 2 * (1 - t ^ 2) ≤ (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
      dsimp [d] at hn2 ⊢
      simp only [star_def] at hn2 hid ⊢
      nlinarith only [hn2, hid]
    exact hmul.trans (hmiddle.trans hup)
  have htwo : 1 - ‖b‖ ^ 2 ≤ 2 * (1 - ‖b‖) := by nlinarith [sq_nonneg (1 - ‖b‖)]
  have hh := hlast.trans (hfirst.trans htwo)
  nlinarith only [hh]

section ActualMap

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)

-- These physical hypotheses occur in proofs of the inverse and Green
-- identities even when they do not occur in the displayed conclusion.
include hb hS hsc hF hinj himage

local notation "G" => riemannMappingClosedExtension F
local notation "J" => riemannMappingClosedInverse F

omit hb hS hsc hF hinj in
theorem riemannMapping_pole_mem : F 0 ∈ Ω := by
  rw [← himage]
  exact mem_image_of_mem F (mem_ball_self zero_lt_one)

theorem riemannMappingClosedInverse_mem_right {w : ℂ} (hw : w ∈ closure Ω) :
    J w ∈ closedBall (0 : ℂ) 1 ∧ G (J w) = w := by
  have hwim : w ∈ G '' closedBall (0 : ℂ) 1 := by
    rw [riemannMappingClosedExtension_closed_image hb hS.isLipschitzDomain hsc F hF hinj himage]
    exact hw
  exact Function.invFunOn_pos hwim

theorem riemannMappingClosedInverse_left {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    J (G z) = z := by
  have hx := Function.invFunOn_pos (show G z ∈ G '' closedBall (0 : ℂ) 1 from ⟨z, hz, rfl⟩)
  exact riemannMappingClosedExtension_injOn hb hS.isLipschitzDomain hsc F hF hinj himage
    hx.1 hz hx.2

theorem riemannMappingClosedInverse_left_interior {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    J (F z) = z := by
  rw [← riemannMappingClosedExtension_eqOn F hF hz]
  exact riemannMappingClosedInverse_left hb hS hsc F hF hinj himage (ball_subset_closedBall hz)

theorem riemannMappingClosedInverse_zero : J (F 0) = 0 :=
  riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage (mem_ball_self zero_lt_one)

/-- The actual physical inverse is continuous on the whole physical
closure, derived from the genuine closed-disk homeomorphism. -/
theorem riemannMappingClosedInverse_continuousOn : ContinuousOn J (closure Ω) := by
  obtain ⟨e, he⟩ := exists_riemannMapping_closedDisk_homeomorph
    hb hS.isLipschitzDomain hsc F hF hinj himage
  have hJe (w : closure Ω) : J w = (e.symm w : ℂ) := by
    have hG : G (e.symm w) = (w : ℂ) := by
      rw [← he (e.symm w), e.apply_symm_apply]
    calc
      J w = J (G (e.symm w)) := congrArg J hG.symm
      _ = (e.symm w : ℂ) :=
        riemannMappingClosedInverse_left hb hS hsc F hF hinj himage (e.symm w).property
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_subtype_val.comp e.symm.continuous).congr (fun w => (hJe w).symm)

theorem riemannMappingClosedInverse_injOn : InjOn J (closure Ω) := by
  intro w hw v hv he
  exact (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage hw).2.symm.trans
    ((congrArg G he).trans (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage hv).2)

theorem riemannMappingClosedInverse_mem_disk {w : ℂ} (hw : w ∈ Ω) :
    J w ∈ ball (0 : ℂ) 1 := by
  have hj := riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (subset_closure hw)
  apply (riemannMappingClosedExtension_mem_domain_iff
    hb hS.isLipschitzDomain hsc F hF hinj himage hj.1).mp
  exact hj.2.symm ▸ hw

/-- The continuous physical inverse retains the actual holomorphic
interior inverse. No boundary derivative is assumed. -/
theorem riemannMappingClosedInverse_differentiableOn : DifferentiableOn ℂ J Ω := by
  obtain ⟨K, hK, hKm, hKF, hFK⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected hF hinj
  rw [himage] at hK hKm hFK
  apply hK.congr
  intro w hw
  calc
    J w = J (F (K w)) := congrArg J (hFK w hw).symm
    _ = K w := riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage (hKm hw)

theorem riemannMappingClosedInverse_image : J '' Ω = ball (0 : ℂ) 1 := by
  apply Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    exact riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage hw
  · intro z hz
    refine ⟨F z, ?_, riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage hz⟩
    rw [← himage]
    exact mem_image_of_mem F hz

theorem riemannMappingClosedInverse_nonzero {w : ℂ} (hw : w ∈ closure Ω) (hne : w ≠ F 0) :
    J w ≠ 0 := by
  intro hj0
  have he := (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage hw).2
  rw [hj0, riemannMappingClosedExtension_eqOn F hF (mem_ball_self zero_lt_one)] at he
  exact hne he.symm

theorem riemannMappingClosedInverse_norm_frontier {w : ℂ} (hw : w ∈ frontier Ω) : ‖J w‖ = 1 := by
  have hj := riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (frontier_subset_closure hw)
  apply le_antisymm (mem_closedBall_zero_iff.mp hj.1)
  apply le_of_not_gt
  intro hn
  have hwΩ : w ∈ Ω := by
    rw [← hj.2]
    exact (riemannMappingClosedExtension_mem_domain_iff
      hb hS.isLipschitzDomain hsc F hF hinj himage hj.1).mpr (mem_ball_zero_iff.mpr hn)
  rw [hS.1.1.frontier_eq] at hw
  exact hw.2 hwΩ

theorem riemannMappingClosedInverse_deriv_nonzero {w : ℂ} (hw : w ∈ Ω) : deriv J w ≠ 0 :=
  RiemannInterior.deriv_ne_zero_of_injOn hS.1.1
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure) hw

/-- The genuine physical inverse has finite conformal energy, even
before any boundary derivative regularity has been proved. -/
theorem riemannMappingClosedInverse_deriv_sq_integrable :
    IntegrableOn (fun w => ‖deriv J w‖ ^ 2) Ω := by
  have hc : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (J '' Ω) := by
    rw [riemannMappingClosedInverse_image hb hS hsc F hF hinj himage]
    exact integrableOn_const unitDisk_bounded.measure_lt_top.ne
  simpa only [mul_one] using localConformal_integrable_weight hS.1.1
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure) hc

/-- The physical inverse's actual Dirichlet energy is exactly the disk
area. This follows from change of variables on the open domain. -/
theorem riemannMappingClosedInverse_deriv_energy :
    (∫ w in Ω, ‖deriv J w‖ ^ 2) = Real.pi := by
  have hi := localConformal_integral_image hS.1.1
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure)
    (fun _ : ℂ => (1 : ℝ))
  rw [riemannMappingClosedInverse_image hb hS hsc F hF hinj himage] at hi
  calc
    _ = (volume (ball (0 : ℂ) 1)).toReal := by
      simpa only [mul_one, integral_const, measureReal_def, Measure.restrict_apply_univ,
        smul_eq_mul] using hi.symm
    _ = Real.pi := unitDisk_volume_toReal

/-- The actual Green function has zero boundary values. -/
theorem riemannMappingGreen_frontier {w : ℂ} (hw : w ∈ frontier Ω) : riemannMappingGreen F w = 0 := by
  rw [riemannMappingGreen, riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hw,
    Real.log_one, neg_zero]

theorem riemannMappingGreen_continuousOn :
    ContinuousOn (riemannMappingGreen F) (closure Ω \ {F 0}) := by
  have hj : ContinuousOn J (closure Ω \ {F 0}) :=
    (riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage).mono diff_subset
  exact (hj.norm.log (fun _ hw => norm_ne_zero_iff.mpr
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage hw.1 hw.2))).neg

theorem riemannMappingGreen_pos {w : ℂ} (hw : w ∈ Ω) (hne : w ≠ F 0) :
    0 < riemannMappingGreen F w := by
  apply neg_pos.mpr
  exact Real.log_neg
    (norm_pos_iff.mpr (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage
      (subset_closure hw) hne))
    (mem_ball_zero_iff.mp (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage hw))

/-- The genuine physical Green function is harmonic away from its
actual interior pole. This is local interior analyticity, and does not
claim smoothness up to the physical boundary. -/
theorem riemannMappingGreen_harmonicOnNhd :
    HarmonicOnNhd (riemannMappingGreen F) (Ω \ {F 0}) := by
  intro w hw
  have hj : AnalyticAt ℂ J w :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd
      hS.1.1 w hw.1
  have ha := hj.harmonicAt_log_norm
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure hw.1) hw.2)
  have he : (-1 : ℝ) • (fun x : ℂ => Real.log ‖J x‖) = riemannMappingGreen F := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul, riemannMappingGreen]
  have hh := ha.const_smul (c := (-1 : ℝ))
  rw [he] at hh
  exact hh

theorem riemannMappingGreen_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingGreen F) (Ω \ {F 0}) := by
  intro w hw
  have hj : AnalyticAt ℂ J w :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd
      hS.1.1 w hw.1
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) J w :=
    (hj.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hne : J w ≠ 0 := riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage
    (subset_closure hw.1) hw.2
  exact ((hs.norm ℝ hne).log (norm_ne_zero_iff.mpr hne)).neg.contDiffWithinAt

/-- The Green function's disk-coordinate value has its exact logarithm
and sign, without any asserted physical boundary differentiability. -/
theorem riemannMappingGreen_comp {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    riemannMappingGreen F (F z) = -Real.log ‖z‖ := by
  rw [riemannMappingGreen, riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage hz]

/-- The actual physical Green derivative, derived by the real chain
rule. This identity is asserted only at actual interior points. -/
theorem riemannMappingGreen_fderiv {w : ℂ} (hw : w ∈ Ω) (hne : w ≠ F 0) (v : ℂ) :
    fderiv ℝ (riemannMappingGreen F) w v = -⟪J w, deriv J w * v⟫_ℝ / ‖J w‖ ^ 2 := by
  have hj : DifferentiableAt ℂ J w :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
      (hS.1.1.mem_nhds hw)
  exact fderiv_neg_log_norm_holomorphic hj
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure hw) hne) v

/-- The true interior Green gradient never vanishes. Boundary gradient
nonvanishing still requires a genuine boundary regularity/Hopf proof. -/
theorem riemannMappingGreen_fderiv_nonzero {w : ℂ} (hw : w ∈ Ω) (hne : w ≠ F 0) :
    fderiv ℝ (riemannMappingGreen F) w ≠ 0 := by
  have hJne := riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure hw) hne
  have hdne := riemannMappingClosedInverse_deriv_nonzero hb hS hsc F hF hinj himage hw
  have hm : deriv J w * (J w / deriv J w) = J w := by
    field_simp [hdne]
  have he : fderiv ℝ (riemannMappingGreen F) w (J w / deriv J w) = -1 := by
    rw [riemannMappingGreen_fderiv hb hS hsc F hF hinj himage hw hne, hm,
      real_inner_self_eq_norm_sq, neg_div, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hJne))]
  intro hz
  rw [hz, ContinuousLinearMap.zero_apply] at he
  norm_num at he

/-- The actual inverse and the Schwarz lemma give a quantitative
Green lower barrier on every genuine interior ball. Boundary
differentiability and a PDE Hopf lemma are not inputs. -/
theorem exists_riemannMappingGreen_ball_lower_barrier {v : ℂ} {R : ℝ}
    (hR : 0 < R) (hball : ball v R ⊆ Ω) :
    ∃ A : ℝ, 0 < A ∧ ∀ w ∈ ball v R, w ≠ F 0 →
      A * (R - ‖w - v‖) ≤ riemannMappingGreen F w := by
  let a : ℂ := J v
  have hv : v ∈ Ω := hball (mem_ball_self hR)
  have ha : ‖a‖ < 1 := mem_ball_zero_iff.mp
    (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage hv)
  let M : ℂ → ℂ := fun w => (J w - a) / (1 - star a * J w)
  have hJb : DifferentiableOn ℂ J (ball v R) :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).mono hball
  have hM : DifferentiableOn ℂ M (ball v R) := by
    have hconst : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (ball v R) :=
      differentiableOn_const (1 : ℂ)
    have haconst : DifferentiableOn ℂ (fun _ : ℂ => star a) (ball v R) :=
      differentiableOn_const (star a)
    apply (hJb.sub_const a).div (hconst.sub (haconst.mul hJb))
    intro w hw
    exact (disk_mobius_denominator_and_norm ha (mem_ball_zero_iff.mp
      (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw)))).1
  have hM0 : M v = 0 := by dsimp [M, a]; rw [sub_self, zero_div]
  have hmaps : MapsTo M (ball v R) (closedBall (M v) 1) := by
    rw [hM0]
    intro w hw
    exact mem_closedBall_zero_iff.mpr
      (disk_mobius_denominator_and_norm ha (mem_ball_zero_iff.mp
        (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw)))).2.le
  let A : ℝ := (1 - ‖a‖) ^ 2 / (2 * R)
  have hA : 0 < A := div_pos (sq_pos_of_pos (sub_pos.mpr ha)) (by positivity)
  refine ⟨A, hA, ?_⟩
  intro w hw hne
  have hn : ‖J w‖ < 1 := mem_ball_zero_iff.mp
    (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw))
  have hd : ‖w - v‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hM hmaps hw
  rw [hM0, dist_zero_right, dist_eq_norm] at hschwarz
  have hbound : ‖(J w - a) / (1 - star a * J w)‖ ≤ ‖w - v‖ / R := by
    simpa only [M, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hschwarz
  have hdefect := disk_mobius_norm_defect ha hn (div_nonneg (norm_nonneg _) hR.le)
    ((div_lt_one hR).mpr hd).le hbound
  have hJe : 0 < ‖J w‖ := norm_pos_iff.mpr
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure (hball hw)) hne)
  have hlog := Real.log_le_sub_one_of_pos hJe
  have halg : A * (R - ‖w - v‖) = (1 - ‖a‖) ^ 2 / 2 * (1 - ‖w - v‖ / R) := by
    dsimp [A]
    field_simp [hR.ne']
  rw [halg, riemannMappingGreen]
  exact hdefect.trans (by linarith)

/-- The actual quotient removes the inverse's simple zero at the pole
by the complex removable-singularity theorem. -/
theorem riemannMappingInversePoleQuotient_differentiableOn :
    DifferentiableOn ℂ (riemannMappingInversePoleQuotient F) Ω := by
  change DifferentiableOn ℂ (dslope J (F 0)) Ω
  exact (Complex.differentiableOn_dslope
    (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage))).mpr
      (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)

theorem riemannMappingInversePoleQuotient_continuousOn :
    ContinuousOn (riemannMappingInversePoleQuotient F) (closure Ω) := by
  have hcl : closure Ω ∈ 𝓝 (F 0) := mem_of_superset
    (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage)) subset_closure
  have hj : DifferentiableAt ℂ J (F 0) :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
      (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage))
  change ContinuousOn (dslope J (F 0)) (closure Ω)
  exact (continuousOn_dslope hcl).mpr
    ⟨riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage, hj⟩

theorem riemannMappingInversePoleQuotient_nonzero {w : ℂ} (hw : w ∈ closure Ω) :
    riemannMappingInversePoleQuotient F w ≠ 0 := by
  by_cases he : w = F 0
  · subst w
    rw [riemannMappingInversePoleQuotient, dslope_same]
    exact riemannMappingClosedInverse_deriv_nonzero hb hS hsc F hF hinj himage
      (riemannMapping_pole_mem F himage)
  · rw [riemannMappingInversePoleQuotient, dslope_of_ne _ he, slope,
      riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage,
      vsub_eq_sub, sub_zero, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr he))
      (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage hw he)

/-- The actual pole-subtracted harmonic function is continuous on the
whole physical closure, including at the pole. -/
theorem riemannMappingGreenCorrection_continuousOn :
    ContinuousOn (riemannMappingGreenCorrection F) (closure Ω) :=
  ((riemannMappingInversePoleQuotient_continuousOn hb hS hsc F hF hinj himage).norm.log
    (fun _ hw => norm_ne_zero_iff.mpr
      (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage hw))).neg

/-- Removing the true logarithmic pole gives a genuine harmonic
function throughout the domain. No elliptic boundary theorem is used. -/
theorem riemannMappingGreenCorrection_harmonicOnNhd :
    HarmonicOnNhd (riemannMappingGreenCorrection F) Ω := by
  intro w hw
  have hq : AnalyticAt ℂ (riemannMappingInversePoleQuotient F) w :=
    (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd
      hS.1.1 w hw
  have ha := hq.harmonicAt_log_norm
    (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage (subset_closure hw))
  have he : (-1 : ℝ) • (fun x : ℂ => Real.log ‖riemannMappingInversePoleQuotient F x‖) =
      riemannMappingGreenCorrection F := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul, riemannMappingGreenCorrection]
  have hh := ha.const_smul (c := (-1 : ℝ))
  rw [he] at hh
  exact hh

theorem riemannMappingGreenCorrection_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingGreenCorrection F) Ω := by
  intro w hw
  have hq : AnalyticAt ℂ (riemannMappingInversePoleQuotient F) w :=
    (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd
      hS.1.1 w hw
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (riemannMappingInversePoleQuotient F) w :=
    (hq.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hne := riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage
    (subset_closure hw)
  exact ((hs.norm ℝ hne).log (norm_ne_zero_iff.mpr hne)).neg.contDiffWithinAt

/-- The actual divided-difference derivative away from the physical
pole. Its numerator and both powers of the physical distance are kept
explicit for the finite-energy estimate. -/
theorem riemannMappingInversePoleQuotient_deriv {w : ℂ} (hw : w ∈ Ω) (hne : w ≠ F 0) :
    deriv (riemannMappingInversePoleQuotient F) w =
      (deriv J w * (w - F 0) - J w) / (w - F 0) ^ 2 := by
  have heq : riemannMappingInversePoleQuotient F =ᶠ[𝓝 w]
      (fun z => J z / (z - F 0)) := by
    filter_upwards [eventually_ne_nhds hne] with z hz
    rw [riemannMappingInversePoleQuotient, dslope_of_ne _ hz, slope,
      riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage,
      vsub_eq_sub, sub_zero, smul_eq_mul]
    simp only [div_eq_mul_inv, mul_comm]
  rw [heq.deriv_eq]
  have hdj : DifferentiableAt ℂ J w :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
      (hS.1.1.mem_nhds hw)
  have hj := hdj.hasDerivAt
  have h := (hj.div ((hasDerivAt_id w).sub_const (F 0)) (sub_ne_zero.mpr hne)).deriv
  simp only [mul_one, id] at h
  exact h

/-- The actual pole quotient has an L² derivative on the whole
physical domain. The removable pole is handled on a genuine compact
interior ball; outside it only the previously proved inverse energy
and the bounded values of the closed inverse are used. -/
theorem riemannMappingInversePoleQuotient_deriv_memLp :
    MemLp (deriv (riemannMappingInversePoleQuotient F)) 2 (volume.restrict Ω) := by
  let Q := riemannMappingInversePoleQuotient F
  have hQ := riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage
  have hQc : ContinuousOn (deriv Q) Ω := (hQ.deriv hS.1.1).continuousOn
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage))
  have hDbounded : Bornology.IsBounded ((deriv Q) '' closedBall (F 0) r) :=
    ((isCompact_closedBall (F 0) r).image_of_continuousOn (hQc.mono hball)).isBounded
  obtain ⟨B, hBpos, hB⟩ := hDbounded.subset_ball_lt 0 (0 : ℂ)
  have hlocal (w : ℂ) (hw : w ∈ closedBall (F 0) r) : ‖deriv Q w‖ ≤ B := by
    have hh := hB (mem_image_of_mem (deriv Q) hw)
    exact (show ‖deriv Q w‖ < B by simpa only [mem_ball, dist_zero_right] using hh).le
  have hJm : MemLp (deriv J) 2 (volume.restrict Ω) := by
    have hJc : ContinuousOn (deriv J) Ω :=
      ((riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).deriv
        hS.1.1).continuousOn
    apply (memLp_two_iff_integrable_sq_norm
      (hJc.aestronglyMeasurable hS.1.1.measurableSet)).mpr
    exact riemannMappingClosedInverse_deriv_sq_integrable hb hS hsc F hF hinj himage
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top⟩
  have hmajor : MemLp (fun w => r⁻¹ * ‖deriv J w‖ + (B + r⁻¹ ^ 2)) 2
      (volume.restrict Ω) :=
    (hJm.norm.const_mul r⁻¹).add (memLp_const (B + r⁻¹ ^ 2))
  apply hmajor.mono' (hQc.aestronglyMeasurable hS.1.1.measurableSet)
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  by_cases hwball : w ∈ closedBall (F 0) r
  · have hp : 0 ≤ r⁻¹ * ‖deriv J w‖ + r⁻¹ ^ 2 := by positivity
    exact (hlocal w hwball).trans (by linarith)
  · have hdist : r ≤ ‖w - F 0‖ := by
      have hh : r < dist w (F 0) := lt_of_not_ge hwball
      have hh' : r < ‖w - F 0‖ := by simpa only [dist_eq_norm] using hh
      exact hh'.le
    have hdpos : 0 < ‖w - F 0‖ := hr.trans_le hdist
    have hne : w ≠ F 0 := sub_ne_zero.mp (norm_ne_zero_iff.mp hdpos.ne')
    have hJn : ‖J w‖ ≤ 1 := mem_closedBall_zero_iff.mp
      (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (subset_closure hw)).1
    have hstep : ‖deriv Q w‖ ≤ ‖deriv J w‖ / r + 1 / r ^ 2 := by
      rw [riemannMappingInversePoleQuotient_deriv hb hS hsc F hF hinj himage hw hne,
        norm_div, norm_pow]
      calc
        _ ≤ (‖deriv J w * (w - F 0)‖ + ‖J w‖) / ‖w - F 0‖ ^ 2 :=
          div_le_div_of_nonneg_right (norm_sub_le _ _) (sq_nonneg _)
        _ = ‖deriv J w‖ / ‖w - F 0‖ + ‖J w‖ / ‖w - F 0‖ ^ 2 := by
          rw [norm_mul]
          field_simp [hdpos.ne']
        _ ≤ ‖deriv J w‖ / r + 1 / r ^ 2 := add_le_add
          (div_le_div_of_nonneg_left (norm_nonneg _) hr hdist)
          ((div_le_div_of_nonneg_right hJn (sq_nonneg _)).trans
            (div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hr)
              ((sq_le_sq₀ hr.le hdpos.le).mpr hdist)))
    have heq : ‖deriv J w‖ / r + 1 / r ^ 2 = r⁻¹ * ‖deriv J w‖ + r⁻¹ ^ 2 := by
      rw [div_eq_mul_inv, one_div, inv_pow]
      ring
    exact hstep.trans (by rw [heq]; linarith)

/-- The actual pole quotient has a strictly positive modulus bound on
the entire physical closure, including the removable pole. -/
theorem exists_riemannMappingInversePoleQuotient_norm_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ closure Ω, c ≤ ‖riemannMappingInversePoleQuotient F w‖ :=
  hb.isCompact_closure.exists_forall_le'
    (riemannMappingInversePoleQuotient_continuousOn hb hS hsc F hF hinj himage).norm
    (fun _ hw => norm_pos_iff.mpr
      (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage hw))

/-- Every genuine real coordinate derivative of the constructed
harmonic correction belongs to L². This is an energy conclusion, not
a boundary smoothness assumption. -/
theorem riemannMappingGreenCorrection_realGradient_memLp (i : Fin 2) :
    MemLp (fun w => fderiv ℝ (riemannMappingGreenCorrection F) w (coordDir i)) 2
      (volume.restrict Ω) := by
  obtain ⟨c, hc, hcn⟩ := exists_riemannMappingInversePoleQuotient_norm_lower_bound
    hb hS hsc F hF hinj himage
  have hQm := riemannMappingInversePoleQuotient_deriv_memLp hb hS hsc F hF hinj himage
  have hmajor := hQm.norm.const_mul c⁻¹
  have hcont : ContinuousOn (fun w => fderiv ℝ (riemannMappingGreenCorrection F) w (coordDir i)) Ω :=
    ((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).continuousOn_fderiv_of_isOpen
      hS.1.1 (by simp)).clm_apply continuousOn_const
  apply hmajor.mono' (hcont.aestronglyMeasurable hS.1.1.measurableSet)
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  have hQ := (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
    (hS.1.1.mem_nhds hw)
  have hne := riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage (subset_closure hw)
  calc
    _ ≤ ‖deriv (riemannMappingInversePoleQuotient F) w‖ * ‖coordDir i‖ /
        ‖riemannMappingInversePoleQuotient F w‖ :=
      norm_fderiv_neg_log_norm_holomorphic_le hQ hne _
    _ ≤ ‖deriv (riemannMappingInversePoleQuotient F) w‖ / c := by
      rw [norm_coordDir, mul_one]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hc (hcn w (subset_closure hw))
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- The true harmonic correction also has an L² value class because
it is continuous on the actual compact physical closure. -/
theorem riemannMappingGreenCorrection_value_memLp :
    MemLp (riemannMappingGreenCorrection F) 2 (volume.restrict Ω) := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top⟩
  have hcont := riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage
  have hbounded : Bornology.IsBounded (riemannMappingGreenCorrection F '' closure Ω) :=
    (hb.isCompact_closure.image_of_continuousOn hcont).isBounded
  obtain ⟨B, _, hB⟩ := hbounded.subset_ball_lt 0 (0 : ℝ)
  apply MemLp.of_bound ((hcont.mono subset_closure).aestronglyMeasurable hS.1.1.measurableSet) B
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  exact (show ‖riemannMappingGreenCorrection F w‖ < B by
    simpa only [mem_ball, dist_zero_right] using hB
      (mem_image_of_mem (riemannMappingGreenCorrection F) (subset_closure hw))).le

private theorem riemannMappingGreenCorrection_complex_fderiv {w : ℂ} (hw : w ∈ Ω) (v : ℂ) :
    fderiv ℝ (fun z => (riemannMappingGreenCorrection F z : ℂ)) w v =
      (fderiv ℝ (riemannMappingGreenCorrection F) w v : ℂ) := by
  have hd : DifferentiableAt ℝ (riemannMappingGreenCorrection F) w :=
    ((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).differentiableOn
      (by simp)).differentiableAt (hS.1.1.mem_nhds hw)
  change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreenCorrection F) w v = _
  rw [fderiv_comp w Complex.ofRealCLM.differentiableAt hd]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply]

private theorem riemannMappingGreenCorrection_complex_value_memLp :
    MemLp (fun w => (riemannMappingGreenCorrection F w : ℂ)) 2 (volume.restrict Ω) := by
  have hm := riemannMappingGreenCorrection_value_memLp hb hS hsc F hF hinj himage
  have hc : ContinuousOn (fun w => (riemannMappingGreenCorrection F w : ℂ)) Ω :=
    Complex.ofRealCLM.continuous.comp_continuousOn
      ((riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage).mono subset_closure)
  apply hm.congr_norm (hc.aestronglyMeasurable hS.1.1.measurableSet)
  exact Eventually.of_forall (fun w => by simp only [Complex.norm_real, Real.norm_eq_abs])

private theorem riemannMappingGreenCorrection_complex_gradient_memLp (i : Fin 2) :
    MemLp (fun w => fderiv ℝ (fun z => (riemannMappingGreenCorrection F z : ℂ)) w (coordDir i)) 2
      (volume.restrict Ω) := by
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (riemannMappingGreenCorrection F z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hc := (hs.continuousOn_fderiv_of_isOpen hS.1.1 (by simp)).clm_apply
    (show ContinuousOn (fun _ : ℂ => coordDir i) Ω from continuousOn_const)
  have hm := riemannMappingGreenCorrection_realGradient_memLp hb hS hsc F hF hinj himage i
  apply hm.congr_norm (hc.aestronglyMeasurable hS.1.1.measurableSet)
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  rw [riemannMappingGreenCorrection_complex_fderiv hb hS hsc F hF hinj himage hw]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The pole-subtracted physical Green function is an actual weak
H¹ vector, represented by its constructed harmonic solution and its
true real derivatives. No boundary elliptic regularity is an input. -/
theorem exists_riemannMappingGreenCorrectionH1 :
    ∃ u : NeumannH1 Ω,
      (h1Value Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
        (fun w => (riemannMappingGreenCorrection F w : ℂ)) ∧
      ∀ i : Fin 2, (h1Gradient Ω i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
        (fun w => (fderiv ℝ (riemannMappingGreenCorrection F) w (coordDir i) : ℂ)) := by
  have hu := riemannMappingGreenCorrection_complex_value_memLp hb hS hsc F hF hinj himage
  have hg := riemannMappingGreenCorrection_complex_gradient_memLp hb hS hsc F hF hinj himage
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (riemannMappingGreenCorrection F z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hweak := isWeakGradient_of_contDiffOn hS.1.1 hs hu hg
  refine ⟨h1Vector hweak, ?_, ?_⟩
  · rw [h1Value_h1Vector]
    exact hu.coeFn_toLp
  · intro i
    rw [h1Gradient_h1Vector]
    filter_upwards [(hg i).coeFn_toLp, ae_restrict_mem hS.1.1.measurableSet] with w hw hwΩ
    rw [hw, riemannMappingGreenCorrection_complex_fderiv hb hS hsc F hF hinj himage hwΩ]

/-- The physical correction is exactly the Green function plus the
fundamental logarithmic singularity away from the actual pole. -/
theorem riemannMappingGreenCorrection_eq {w : ℂ} (hw : w ∈ closure Ω) (hne : w ≠ F 0) :
    riemannMappingGreenCorrection F w = riemannMappingGreen F w + Real.log ‖w - F 0‖ := by
  have hnJ : ‖J w‖ ≠ 0 := norm_ne_zero_iff.mpr
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage hw hne)
  have hnd : ‖w - F 0‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [riemannMappingGreenCorrection, riemannMappingInversePoleQuotient,
    dslope_of_ne _ hne, slope, riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage,
    vsub_eq_sub, sub_zero, smul_eq_mul, norm_mul, norm_inv, Real.log_mul (inv_ne_zero hnd) hnJ, Real.log_inv,
    riemannMappingGreen]
  ring

/-- The actual Dirichlet boundary data of the pole-subtracted harmonic
function are the smooth physical function `log ‖w - F 0‖`. -/
theorem riemannMappingGreenCorrection_frontier {w : ℂ} (hw : w ∈ frontier Ω) :
    riemannMappingGreenCorrection F w = Real.log ‖w - F 0‖ := by
  have hne : w ≠ F 0 := by
    intro he
    rw [he, hS.1.1.frontier_eq] at hw
    exact hw.2 (riemannMapping_pole_mem F himage)
  rw [riemannMappingGreenCorrection_eq hb hS hsc F hF hinj himage
    (frontier_subset_closure hw) hne,
    riemannMappingGreen_frontier hb hS hsc F hF hinj himage hw, zero_add]

omit hb hS hsc hF hinj himage in
/-- The actual physical Dirichlet data are smooth on an open
neighborhood of the entire frontier, because the pole is interior. -/
theorem riemannMappingGreenBoundaryData_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => Real.log ‖w - F 0‖) {F 0}ᶜ := by
  intro w hw
  have hne : w - F 0 ≠ 0 := sub_ne_zero.mpr hw
  exact (((contDiffAt_id.sub contDiffAt_const).norm ℝ hne).log
    (norm_ne_zero_iff.mpr hne)).contDiffWithinAt

/-- A genuine globally smooth, compactly supported physical test
function has exactly the pole-subtracted Green function's boundary
data. The cutoff extends already smooth logarithmic data near the
frontier, not the unknown Riemann-map boundary jets. -/
theorem exists_riemannMappingGreenCorrection_smooth_boundary_data :
    ∃ b : smoothTraceTests, ∀ w ∈ frontier Ω,
      riemannMappingGreenCorrection F w = (b w).re := by
  have hk : IsCompact (frontier Ω) := hb.isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  have hku : frontier Ω ⊆ ({F 0} : Set ℂ)ᶜ := by
    intro w hw he
    have hwe : w = F 0 := he
    rw [hwe, hS.1.1.frontier_eq] at hw
    exact hw.2 (riemannMapping_pole_mem F himage)
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => (Real.log ‖w - F 0‖ : ℂ)) {F 0}ᶜ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (riemannMappingGreenBoundaryData_contDiffOn F)
  obtain ⟨b, hbtest, hbe⟩ := exists_smooth_compact_extension hk isOpen_compl_singleton hku hs
  refine ⟨⟨b, hbtest⟩, ?_⟩
  intro w hw
  change riemannMappingGreenCorrection F w = (b w).re
  rw [(hbe w hw).self_of_nhds, Complex.ofReal_re]
  exact riemannMappingGreenCorrection_frontier hb hS hsc F hF hinj himage hw

/-- The actual harmonic Dirichlet problem whose boundary regularity
would give the smooth conformal boundary jets: both the solution and
its smooth physical data are already constructed. -/
theorem exists_riemannMappingGreenCorrection_dirichlet_data :
    ∃ b : smoothTraceTests,
      HarmonicOnNhd (riemannMappingGreenCorrection F) Ω ∧
      ContinuousOn (riemannMappingGreenCorrection F) (closure Ω) ∧
      ∀ w ∈ frontier Ω, riemannMappingGreenCorrection F w = (b w).re := by
  obtain ⟨b, hbdata⟩ := exists_riemannMappingGreenCorrection_smooth_boundary_data
    hb hS hsc F hF hinj himage
  exact ⟨b, riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage,
    riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage, hbdata⟩

end ActualMap

private theorem exists_quadratic_smooth_graph_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |x| ≤ 1 →
      |f x - f 0 - deriv f 0 * x| ≤ M * x ^ 2 := by
  have hf2 : ContDiff ℝ (1 + 1 : ℕ) f :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : ContDiff ℝ 1 (deriv f) := hf2.deriv'
  obtain ⟨K, hK⟩ := hd.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (-1 : ℝ) 1) (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro x hx
  have hxI : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  have h0I : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hsub : uIcc (0 : ℝ) x ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h0I hxI
  have hsmall (y : ℝ) (hy : y ∈ uIcc (0 : ℝ) x) : |y| ≤ |x| := by
    apply abs_le.mpr
    have hxlo := neg_abs_le x
    have hxhi := le_abs_self x
    rcases mem_uIcc.mp hy with hy | hy <;> constructor <;> linarith [abs_nonneg x]
  let g : ℝ → ℝ := fun y => f y - f 0 - deriv f 0 * y
  have hg (y : ℝ) : HasDerivAt g (deriv f y - deriv f 0) y := by
    have h := ((hf.differentiable (by simp) y).hasDerivAt.sub_const (f 0)).sub
        ((hasDerivAt_id y).const_mul (deriv f 0))
    simp only [mul_one] at h
    exact h
  have hb (y : ℝ) (hy : y ∈ uIcc (0 : ℝ) x) :
      ‖deriv g y‖ ≤ (K : ℝ) * |x| := by
    rw [(hg y).deriv]
    have hh := hK.dist_le_mul y (hsub hy) 0 h0I
    have hh' : ‖deriv f y - deriv f 0‖ ≤ (K : ℝ) * |y| := by
      simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (hsmall y hy) K.coe_nonneg)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y (_ : y ∈ uIcc (0 : ℝ) x) => (hg y).differentiableAt) hb
    (convex_uIcc (0 : ℝ) x) left_mem_uIcc right_mem_uIcc
  simpa only [g, mul_zero, sub_self, sub_zero, Real.norm_eq_abs, mul_assoc,
    ← pow_two, sq_abs] using hm

/-- The genuine smooth graph definition supplies an actual interior
tangent ball at each physical boundary point. This gives geometric
input for a Hopf barrier; it does not assume or assert a Hopf lemma. -/
theorem exists_smoothDomain_interior_tangent_ball {Ω : Set ℂ} (hS : IsSmoothDomain Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ v : ℂ, ∃ R : ℝ, 0 < R ∧ ball v R ⊆ Ω ∧ p ∈ sphere v R := by
  obtain ⟨c, r, h, K, f, hc, hr, hh, hf, _, hf0, _, hgraph⟩ := hS.2 p hp
  obtain ⟨M, hM, hquad⟩ := exists_quadratic_smooth_graph_bound hf
  let a : ℝ := deriv f 0
  let n : ℂ := -(a : ℂ) + Complex.I
  let C : ℝ := ‖n‖
  have hC : 0 < C := by
    apply norm_pos_iff.mpr
    intro he
    have him := congrArg Complex.im he
    norm_num [n] at him
  have hCsq : C ^ 2 = a ^ 2 + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [n, Complex.normSq_apply, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.I_re, add_zero, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
      neg_zero, Complex.I_im, zero_add]
    ring
  let e : ℝ := min (min (r / (2 * C)) (h / (2 * C)))
    (min (1 / (2 * C)) (1 / (2 * (M + 1))))
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨ρ, hρ, hρe⟩ := exists_between he
  have hρr : 2 * ρ * C < r := by
    have ht := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (lt_of_lt_of_le hρe ((min_le_left _ _).trans (min_le_left _ _)))
    nlinarith
  have hρh : 2 * ρ * C < h := by
    have ht := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (lt_of_lt_of_le hρe ((min_le_left _ _).trans (min_le_right _ _)))
    nlinarith
  have hρ1 : 2 * ρ * C < 1 := by
    have ht := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (lt_of_lt_of_le hρe ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hρM : 2 * ρ * M ≤ 1 := by
    have ht := (lt_div_iff₀ (show 0 < 2 * (M + 1) by positivity)).mp
      (lt_of_lt_of_le hρe ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith
  let v : ℂ := p + (ρ : ℂ) * n / c
  let R : ℝ := ρ * C
  have hR : 0 < R := mul_pos hρ hC
  have hvc : ‖v - p‖ = R := by
    simp only [v, add_sub_cancel_left, norm_div, norm_mul, hc, div_one,
      Complex.norm_real, Real.norm_of_nonneg hρ.le, R, C]
  have hcne : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  refine ⟨v, R, hR, ?_, ?_⟩
  · intro w hw
    have hwR : ‖w - v‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
    have hwp : ‖w - p‖ < 2 * ρ * C := by
      calc
        _ ≤ ‖w - v‖ + ‖v - p‖ := norm_sub_le_norm_sub_add_norm_sub w v p
        _ < R + R := by rw [hvc]; linarith only [hwR]
        _ = _ := by dsimp [R]; ring
    let z : ℂ := c * (w - p)
    have hz : ‖z‖ = ‖w - p‖ := by dsimp [z]; rw [norm_mul, hc, one_mul]
    have hzr : |z.re| < r := (Complex.abs_re_le_norm z).trans_lt (by rw [hz]; exact hwp.trans hρr)
    have hzh : |z.im| < h := (Complex.abs_im_le_norm z).trans_lt (by rw [hz]; exact hwp.trans hρh)
    apply (hgraph w hzr hzh).mpr
    have hx1 : |z.re| ≤ 1 :=
      ((Complex.abs_re_le_norm z).trans_lt (by rw [hz]; exact hwp.trans hρ1)).le
    have hfx : f z.re ≤ a * z.re + M * z.re ^ 2 := by
      have ht := (abs_le.mp (hquad z.re hx1)).2
      rw [hf0] at ht
      dsimp [a]
      linarith
    have hball : ‖z - (ρ : ℂ) * n‖ < R := by
      have hzv : z - (ρ : ℂ) * n = c * (w - v) := by
        dsimp [z, v]
        field_simp [hcne]; ring
      rw [hzv, norm_mul, hc, one_mul]
      exact hwR
    have hs : (z.re + ρ * a) ^ 2 + (z.im - ρ) ^ 2 < ρ ^ 2 * (a ^ 2 + 1) := by
      have ht := (sq_lt_sq₀ (norm_nonneg _) hR.le).mpr hball
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at ht
      have hre : (z - (ρ : ℂ) * n).re = z.re + ρ * a := by simp [n]
      have him : (z - (ρ : ℂ) * n).im = z.im - ρ := by simp [n]
      rw [hre, him] at ht
      have hRsq : R ^ 2 = ρ ^ 2 * (a ^ 2 + 1) := by dsimp [R]; rw [mul_pow, hCsq]
      rw [hRsq] at ht
      nlinarith
    have hprod := mul_nonneg (show 0 ≤ 1 - 2 * ρ * M by linarith) (sq_nonneg z.re)
    have hy : a * z.re + M * z.re ^ 2 < z.im := by
      by_contra hn
      have hny : z.im ≤ a * z.re + M * z.re ^ 2 := le_of_not_gt hn
      have hmul := mul_le_mul_of_nonneg_left hny (show 0 ≤ 2 * ρ by positivity)
      nlinarith [sq_nonneg z.im]
    exact hfx.trans_lt hy
  · simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hvc

/-- Each actual physical frontier point has a strictly positive Green
lower barrier on a true tangent ball. Both the ball and the barrier
are derived from the original smooth domain and interior conformal
map; no boundary derivative or desired boundary regularity occurs in
the hypotheses. -/
theorem exists_riemannMappingGreen_boundary_lower_barrier {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ v : ℂ, ∃ R A : ℝ, 0 < R ∧ 0 < A ∧ ball v R ⊆ Ω ∧ p ∈ sphere v R ∧
      ∀ w ∈ ball v R, w ≠ F 0 → A * (R - ‖w - v‖) ≤ riemannMappingGreen F w := by
  obtain ⟨v, R, hR, hball, hpR⟩ := exists_smoothDomain_interior_tangent_ball hS hp
  obtain ⟨A, hA, hbarrier⟩ := exists_riemannMappingGreen_ball_lower_barrier
    hb hS hsc F hF hinj himage hR hball
  exact ⟨v, R, A, hR, hA, hball, hpR, hbarrier⟩

/-- A genuine unit inward ray has a strictly positive Green slope
lower bound at every physical frontier point. The whole short ray
avoids the actual Green pole. This is a proved boundary estimate,
without any assumed existence of boundary derivatives. -/
theorem exists_riemannMappingGreen_inward_ray_lower {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ b : ℂ, ∃ δ A : ℝ, ‖b‖ = 1 ∧ 0 < δ ∧ 0 < A ∧
      ∀ t : ℝ, 0 < t → t < δ → p + (t : ℂ) * b ∈ Ω ∧
        p + (t : ℂ) * b ≠ F 0 ∧ A * t ≤ riemannMappingGreen F (p + (t : ℂ) * b) := by
  obtain ⟨v, R, A, hR, hA, hball, hpR, hbarrier⟩ :=
    exists_riemannMappingGreen_boundary_lower_barrier hb hS hsc F hF hinj himage hp
  have hvp : ‖v - p‖ = R := by simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hpR
  let b : ℂ := (R : ℂ)⁻¹ * (v - p)
  have hb1 : ‖b‖ = 1 := by
    dsimp [b]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le, hvp,
      inv_mul_cancel₀ hR.ne']
  have hpne : p ≠ F 0 := by
    intro he
    rw [he, hS.1.1.frontier_eq] at hp
    exact hp.2 (riemannMapping_pole_mem F himage)
  let δ : ℝ := min R (‖p - F 0‖ / 2)
  have hδ : 0 < δ := lt_min hR (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hpne)) (by norm_num))
  refine ⟨b, δ, A, hb1, hδ, hA, ?_⟩
  intro t ht htδ
  have htR : t < R := lt_of_lt_of_le htδ (min_le_left _ _)
  have htP : t < ‖p - F 0‖ / 2 := lt_of_lt_of_le htδ (min_le_right _ _)
  have htd : t / R < 1 := (div_lt_one hR).mpr htR
  have hdist : ‖p + (t : ℂ) * b - v‖ = R - t := by
    have he : p + (t : ℂ) * b - v = ((t / R - 1 : ℝ) : ℂ) * (v - p) := by
      dsimp [b]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hR.ne']; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr htd.le), hvp]
    field_simp [hR.ne']; ring
  have hwball : p + (t : ℂ) * b ∈ ball v R := by
    rw [mem_ball, dist_eq_norm, hdist]
    linarith
  have hwne : p + (t : ℂ) * b ≠ F 0 := by
    have hn : ‖p + (t : ℂ) * b - p‖ = t := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, hb1, mul_one]
    intro he
    rw [he, norm_sub_rev] at hn
    nlinarith
  refine ⟨hball hwball, hwne, ?_⟩
  have hh := hbarrier _ hwball hwne
  rw [hdist] at hh
  simpa only [sub_sub_cancel] using hh

end PolyaNeumann

end
