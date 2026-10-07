module

public import RequestProject.RiemannMappingSmoothBoundary
public import RequestProject.ReconBasic
public import RequestProject.ChainRule
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The actual local Dirichlet problem for conformal boundary regularity

The constructed physical Green correction is reduced to zero physical
boundary values by subtracting its genuine smooth boundary datum. The
result is an actual H¹ vector, smooth in the open domain and continuous
on its closure. Its weak Poisson equation and smooth forcing are proved
from interior harmonicity, by localizing each compact test.

The actual smooth-domain graph constructs real smooth bi-Lipschitz
coordinates, preserves genuine H¹ energy, and gives true zero values
on a flat boundary interval. The graph differential gives the actual
elliptic energy form. Fubini and the endpoint FTC then prove that the
mass of a shrinking boundary strip, divided by its squared thickness,
tends to zero. This justifies the energy estimate needed for normal
cutoffs; it is not a boundary second-derivative theorem.

No boundary H² estimate, higher boundary regularity, or smooth conformal
collar is assumed or asserted by these initial construction lemmas.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff

/-- The project's coordinate Laplacian equals the genuine Euclidean
Laplacian at every point of twice continuous differentiability. -/
theorem lap_eq_euclidean_laplacian {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) : lap f z = Laplacian.laplacian f z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (v : ℂ) : dirD (dirD f v) v z = fderiv ℝ (fderiv ℝ f) z v v := by
    change fderiv ℝ (fun w => fderiv ℝ f w v) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp only [fderiv_const_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply, map_zero, zero_add]
  rw [lap, he, he, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A local equality transports both actual coordinate second
derivatives. No assumed differential equation is used. -/
theorem eventuallyEq_lap_eq {f g : ℂ → ℂ} {z : ℂ} (hfg : f =ᶠ[𝓝 z] g) :
    lap f z = lap g z := by
  have hd (v : ℂ) : dirD f v =ᶠ[𝓝 z] dirD g v :=
    (hfg.fderiv (𝕜 := ℝ)).fun_comp (fun A : ℂ →L[ℝ] ℂ => A v)
  have hdd (v : ℂ) : dirD (dirD f v) v z = dirD (dirD g v) v z :=
    congrArg (fun A : ℂ →L[ℝ] ℂ => A v) ((hd v).fderiv_eq (𝕜 := ℝ))
  exact congrArg₂ (· + ·) (hdd 1) (hdd Complex.I)

theorem smooth_integral_dirD_mul_test {U : Set ℂ} {G φ : ℂ → ℂ}
    (hG : TestFunction univ G) (hφ : TestFunction U φ) (i : Fin 2) :
    (∫ z in U, dirD G (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD (dirD G (coordDir i)) (coordDir i) z * φ z) := by
  have hu := (hG.dirD (coordDir i)).memLp' 2 (μ := volume.restrict U)
  have hg (j : Fin 2) := ((hG.dirD (coordDir i)).dirD (coordDir j)).memLp' 2
    (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth (hG.dirD (coordDir i)).1 hu hg φ hφ i
  change (∫ z in U, (hu.toLp _ : L2 U) z * dirD φ (coordDir i) z) =
    -(∫ z in U, ((hg i).toLp _ : L2 U) z * φ z) at hw
  have hl : (fun z => (hu.toLp _ : L2 U) z * dirD φ (coordDir i) z) =ᵐ[volume.restrict U]
      (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) := by
    filter_upwards [hu.coeFn_toLp] with z hz
    rw [hz]
  have hr : (fun z => ((hg i).toLp _ : L2 U) z * φ z) =ᵐ[volume.restrict U]
      (fun z => dirD (dirD G (coordDir i)) (coordDir i) z * φ z) := by
    filter_upwards [(hg i).coeFn_toLp] with z hz
    rw [hz]
  rw [integral_congr_ae hl, integral_congr_ae hr] at hw
  exact hw

/-- The true weak Poisson identity for a function smooth only in the
open domain. The compact test is localized before integration by
parts, so no boundary derivatives or global second-derivative energy
are needed. -/
theorem local_smooth_gradient_test_eq_neg_lap {U : Set ℂ} (hU : IsOpen U)
    {v φ : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (hφ : TestFunction U φ) :
    (∫ z in U, ∑ i : Fin 2, dirD v (coordDir i) z * dirD φ (coordDir i) z) =
      -(∫ z in U, lap v z * φ z) := by
  obtain ⟨G, hG, hGv⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hv
  have hfirst (i : Fin 2) :
      (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) =
        (fun z => dirD v (coordDir i) z * dirD φ (coordDir i) z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [show dirD G (coordDir i) z = dirD v (coordDir i) z from
        congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i)) ((hGv z hz).fderiv_eq (𝕜 := ℝ))]
    · simp only [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz,
        ContinuousLinearMap.zero_apply, mul_zero]
  have hsecond : (fun z => lap G z * φ z) = (fun z => lap v z * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [eventuallyEq_lap_eq (hGv z hz)]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hint (i : Fin 2) :
      IntegrableOn (fun z => dirD G (coordDir i) z * dirD φ (coordDir i) z) U :=
    ((hG.dirD (coordDir i)).memLp' 2).integrable_mul ((hφ.dirD (coordDir i)).memLp' 2)
  have hxx : IntegrableOn (fun z => dirD (dirD G 1) 1 z * φ z) U :=
    (((hG.dirD 1).dirD 1).memLp' 2).integrable_mul (hφ.memLp' 2)
  have hyy : IntegrableOn (fun z => dirD (dirD G Complex.I) Complex.I z * φ z) U :=
    (((hG.dirD Complex.I).dirD Complex.I).memLp' 2).integrable_mul (hφ.memLp' 2)
  have hlap :
      (∫ z in U, lap G z * φ z) =
        (∫ z in U, dirD (dirD G 1) 1 z * φ z) +
          ∫ z in U, dirD (dirD G Complex.I) Complex.I z * φ z := by
    simp_rw [lap, add_mul]
    exact integral_add hxx hyy
  calc
    _ = ∫ z in U, ∑ i : Fin 2, dirD G (coordDir i) z * dirD φ (coordDir i) z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => Finset.sum_congr rfl (fun i _ =>
        congrFun (hfirst i).symm z))
    _ = ∑ i : Fin 2, ∫ z in U, dirD G (coordDir i) z * dirD φ (coordDir i) z :=
      integral_finset_sum _ (fun i _ => hint i)
    _ = -(∫ z in U, lap G z * φ z) := by
      simp_rw [smooth_integral_dirD_mul_test hG hφ]
      rw [Fin.sum_univ_two, hlap]
      simp only [coordDir, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    _ = _ := by rw [hsecond]

/-- The real projection of a genuine globally smooth boundary datum
is itself a genuine globally smooth compactly supported datum. -/
def smoothTraceRealPart (b : smoothTraceTests) : smoothTraceTests := by
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  refine ⟨fun z => ((b z).re : ℂ), ?_⟩
  refine ⟨L.contDiff.comp b.property.1, ?_, subset_univ _⟩
  exact b.property.2.1.comp_left (show L (0 : ℂ) = 0 by simp [L])

@[simp] theorem smoothTraceRealPart_apply (b : smoothTraceTests) (z : ℂ) :
    smoothTraceRealPart b z = ((b z).re : ℂ) := rfl

/-- The actual physical Dirichlet remainder after subtracting the
constructed smooth real boundary datum. -/
def riemannMappingDirichletRemainder (F : ℂ → ℂ) (b : smoothTraceTests) (z : ℂ) : ℂ :=
  (riemannMappingGreenCorrection F z : ℂ) - b z

theorem lap_sub_of_contDiffAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    lap (fun w => f w - g w) z = lap f z - lap g z := by
  have heq : (fun w => f w - g w) = f + (-1 : ℝ) • g := by
    funext w
    change f w - g w = f w + (-1 : ℝ) • g w
    rw [neg_one_smul, sub_eq_add_neg]
  have hadd : Laplacian.laplacian (f + (-1 : ℝ) • g) z =
      Laplacian.laplacian f z + Laplacian.laplacian ((-1 : ℝ) • g) z :=
    hf.laplacian_add (hg.const_smul (-1 : ℝ))
  have hsmul : Laplacian.laplacian ((-1 : ℝ) • g) z =
      (-1 : ℝ) • Laplacian.laplacian g z := laplacian_smul (-1 : ℝ) hg
  rw [lap_eq_euclidean_laplacian (hf.sub hg), heq, hadd, hsmul,
    ← lap_eq_euclidean_laplacian hf, ← lap_eq_euclidean_laplacian hg]
  simp only [neg_one_smul, sub_eq_add_neg]

/-- The actual zero-boundary H¹ Poisson problem needed for boundary
regularity. Its function, smooth forcing, boundary values, H¹ vector,
and compact-test equation are derived from the constructed Green
correction. No zero-trace or boundary regularity premise is added. -/
theorem exists_riemannMapping_zero_boundary_poisson_problem {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω) :
    ∃ b : smoothTraceTests, ∃ u : NeumannH1 Ω,
      ContinuousOn (riemannMappingDirichletRemainder F b) (closure Ω) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingDirichletRemainder F b) Ω ∧
      (∀ z ∈ frontier Ω, riemannMappingDirichletRemainder F b z = 0) ∧
      (h1Value Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω] riemannMappingDirichletRemainder F b ∧
      (∀ i : Fin 2, (h1Gradient Ω i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
        dirD (riemannMappingDirichletRemainder F b) (coordDir i)) ∧
      (∀ z ∈ Ω, lap (riemannMappingDirichletRemainder F b) z = -lap (b : ℂ → ℂ) z) ∧
      ∀ φ : ℂ → ℂ, TestFunction Ω φ →
        (∫ z in Ω, ∑ i : Fin 2, dirD (riemannMappingDirichletRemainder F b) (coordDir i) z *
          dirD φ (coordDir i) z) = ∫ z in Ω, lap (b : ℂ → ℂ) z * φ z := by
  obtain ⟨b₀, hbdata⟩ := exists_riemannMappingGreenCorrection_smooth_boundary_data
    hb hS hsc F hF hinj himage
  let b := smoothTraceRealPart b₀
  obtain ⟨u₀, hu₀, hgu₀⟩ := exists_riemannMappingGreenCorrectionH1 hb hS hsc F hF hinj himage
  let h : ℂ → ℂ := fun z => (riemannMappingGreenCorrection F z : ℂ)
  have hharm : HarmonicOnNhd h Ω :=
    (riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage).comp_CLM
      Complex.ofRealCLM
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) h Ω := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingDirichletRemainder F b) Ω :=
    hs.sub b.property.1.contDiffOn
  have hΔ (z : ℂ) (hz : z ∈ Ω) :
      lap (riemannMappingDirichletRemainder F b) z = -lap (b : ℂ → ℂ) z := by
    have hh : ContDiffAt ℝ 2 h z := (hharm z hz).1
    have hb : ContDiffAt ℝ 2 (b : ℂ → ℂ) z := b.property.1.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
    exact (lap_sub_of_contDiffAt hh hb).trans (by
      rw [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds]
      simp only [Pi.zero_apply, zero_sub])
  refine ⟨b, u₀ - smoothTraceH1 Ω b, ?_, hv, ?_, ?_, ?_, hΔ, ?_⟩
  · exact (Complex.ofRealCLM.continuous.comp_continuousOn
      (riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage)).sub
        b.property.1.continuous.continuousOn
  · intro z hz
    change (riemannMappingGreenCorrection F z : ℂ) - ((b₀ z).re : ℂ) = 0
    rw [hbdata z hz, sub_self]
  · rw [map_sub]
    filter_upwards [Lp.coeFn_sub (h1Value Ω u₀) (h1Value Ω (smoothTraceH1 Ω b)), hu₀,
      (smoothTraceTests_memLp Ω b).coeFn_toLp] with z hz hu hbz
    rw [hz, Pi.sub_apply, hu, h1Value_smoothTraceH1, hbz]
    rfl
  · intro i
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (h1Gradient Ω i u₀)
      (h1Gradient Ω i (smoothTraceH1 Ω b)), hgu₀ i,
      (smoothTraceTests_memLp_deriv Ω b i).coeFn_toLp,
      ae_restrict_mem hS.1.1.measurableSet] with z hz hu hbz hzΩ
    have hd : DifferentiableAt ℝ (riemannMappingGreenCorrection F) z :=
      ((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).differentiableOn
        (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ)
    have hc : fderiv ℝ h z =
        Complex.ofRealCLM.comp (fderiv ℝ (riemannMappingGreenCorrection F) z) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreenCorrection F) z = _
      rw [fderiv_comp z Complex.ofRealCLM.differentiableAt hd,
        ContinuousLinearMap.fderiv]
    have hh : DifferentiableAt ℝ h z :=
      (hs.differentiableOn (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ)
    rw [hz, Pi.sub_apply, hu, h1Gradient_smoothTraceH1, hbz]
    change _ = fderiv ℝ (h - (b : ℂ → ℂ)) z (coordDir i)
    rw [fderiv_sub hh ((b.property.1.differentiable (by simp)) z), hc]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply]
  · intro φ hφ
    rw [local_smooth_gradient_test_eq_neg_lap hS.1.1 hv hφ]
    have hl : (fun z => lap (riemannMappingDirichletRemainder F b) z * φ z)
        =ᵐ[volume.restrict Ω] (fun z => -(lap (b : ℂ → ℂ) z * φ z)) := by
      filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with z hz
      rw [hΔ z hz, neg_mul]
    rw [integral_congr_ae hl, integral_neg, neg_neg]

/-! ## Actual smooth graph coordinates -/

/-- The genuine graph shear. Its inverse subtracts the same graph
height, because the shear preserves the real coordinate. -/
def smoothDirichletGraphShear (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  z + (f z.re : ℂ) * Complex.I

@[simp] theorem smoothDirichletGraphShear_re (f : ℝ → ℝ) (z : ℂ) :
    (smoothDirichletGraphShear f z).re = z.re := by
  simp [smoothDirichletGraphShear]

@[simp] theorem smoothDirichletGraphShear_im (f : ℝ → ℝ) (z : ℂ) :
    (smoothDirichletGraphShear f z).im = z.im + f z.re := by
  simp [smoothDirichletGraphShear]

/-- This is a global real homeomorphism, built from the supplied
continuous graph, rather than an assumed boundary coordinate map. -/
def smoothDirichletGraphShearHomeomorph (f : ℝ → ℝ) (hf : Continuous f) : ℂ ≃ₜ ℂ where
  toFun := smoothDirichletGraphShear f
  invFun := fun z => z - (f z.re : ℂ) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp [smoothDirichletGraphShear]
  right_inv z := by
    apply Complex.ext <;> simp [smoothDirichletGraphShear]
  continuous_toFun := continuous_id.add
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)
  continuous_invFun := continuous_id.sub
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)

@[simp] theorem smoothDirichletGraphShearHomeomorph_apply (f : ℝ → ℝ)
    (hf : Continuous f) (z : ℂ) :
    smoothDirichletGraphShearHomeomorph f hf z = smoothDirichletGraphShear f z := rfl

@[simp] theorem smoothDirichletGraphShearHomeomorph_symm_apply (f : ℝ → ℝ)
    (hf : Continuous f) (z : ℂ) :
    (smoothDirichletGraphShearHomeomorph f hf).symm z =
      z - (f z.re : ℂ) * Complex.I := rfl

theorem smoothDirichletGraphShear_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDirichletGraphShear f) :=
  contDiff_id.add ((Complex.ofRealCLM.contDiff.comp
    (hf.comp Complex.reCLM.contDiff)).mul contDiff_const)

theorem smoothDirichletGraphShear_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : LipschitzWith (K + 1) (smoothDirichletGraphShear f) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
  have hfw : ‖((f z.re - f w.re : ℝ) : ℂ) * Complex.I‖ ≤ (K : ℝ) * ‖z - w‖ := by
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    have hre : ‖z.re - w.re‖ ≤ ‖z - w‖ := by
      simpa only [Real.norm_eq_abs, Complex.sub_re] using Complex.abs_re_le_norm (z - w)
    exact (hf.norm_sub_le z.re w.re).trans
      (mul_le_mul_of_nonneg_left hre K.coe_nonneg)
  calc
    ‖smoothDirichletGraphShear f z - smoothDirichletGraphShear f w‖ =
        ‖(z - w) + ((f z.re - f w.re : ℝ) : ℂ) * Complex.I‖ := by
      congr 1
      simp only [smoothDirichletGraphShear, Complex.ofReal_sub]
      ring
    _ ≤ ‖z - w‖ + ‖((f z.re - f w.re : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ ‖z - w‖ + (K : ℝ) * ‖z - w‖ := add_le_add le_rfl hfw
    _ = ((K : ℝ) + 1) * ‖z - w‖ := by ring

theorem smoothDirichletGraphShearHomeomorph_symm_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (smoothDirichletGraphShearHomeomorph f hf.continuous).symm := by
  have heq : (smoothDirichletGraphShearHomeomorph f hf.continuous).symm =
      smoothDirichletGraphShear (fun x => -f x) := by
    funext z
    simp only [smoothDirichletGraphShearHomeomorph_symm_apply, smoothDirichletGraphShear,
      Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
  rw [heq]
  exact smoothDirichletGraphShear_lipschitz hf.neg

/-- The graph shear followed by the actual rigid coordinates of the
smooth-domain chart. Only continuity of the supplied graph and a
nonzero rigid factor are required to construct this homeomorphism. -/
def smoothDirichletGraphChart (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) :
    ℂ ≃ₜ ℂ :=
  (smoothDirichletGraphShearHomeomorph f hf).trans
    ((Homeomorph.mulRight₀ c hc).symm.trans (Homeomorph.addLeft p))

@[simp] theorem smoothDirichletGraphChart_apply (p c : ℂ) (hc : c ≠ 0)
    (f : ℝ → ℝ) (hf : Continuous f) (z : ℂ) :
    smoothDirichletGraphChart p c hc f hf z = p + smoothDirichletGraphShear f z / c := by
  simp only [smoothDirichletGraphChart, Homeomorph.trans_apply,
    smoothDirichletGraphShearHomeomorph_apply, Homeomorph.mulRight₀_symm_apply,
    Homeomorph.coe_addLeft, div_eq_mul_inv]

theorem smoothDirichletGraphChart_rotate (p c : ℂ) (hc : c ≠ 0)
    (f : ℝ → ℝ) (hf : Continuous f) (z : ℂ) :
    c * (smoothDirichletGraphChart p c hc f hf z - p) = smoothDirichletGraphShear f z := by
  rw [smoothDirichletGraphChart_apply]
  field_simp [hc]
  ring

theorem smoothDirichletGraphChart_contDiff (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDirichletGraphChart p c hc f hf.continuous) :=
  contDiff_const.add ((smoothDirichletGraphShear_contDiff hf).div_const c)

theorem smoothDirichletGraphChart_lipschitz (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hf.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have heq : smoothDirichletGraphChart p c hc f hf.continuous z -
      smoothDirichletGraphChart p c hc f hf.continuous w =
      (smoothDirichletGraphShear f z - smoothDirichletGraphShear f w) / c := by
    simp only [smoothDirichletGraphChart_apply]
    ring
  simpa only [dist_eq_norm, heq, norm_div, hc₁, div_one] using
    (smoothDirichletGraphShear_lipschitz hf).dist_le_mul z w

theorem smoothDirichletGraphChart_symm_lipschitz (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (smoothDirichletGraphChart p c hc f hf.continuous).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist ((smoothDirichletGraphShearHomeomorph f hf.continuous).symm ((-p + z) * c))
    ((smoothDirichletGraphShearHomeomorph f hf.continuous).symm ((-p + w) * c)) ≤ _
  have hs := (smoothDirichletGraphShearHomeomorph_symm_lipschitz hf).dist_le_mul
    ((-p + z) * c) ((-p + w) * c)
  have heq : (-p + z) * c - (-p + w) * c = (z - w) * c := by ring
  simpa only [dist_eq_norm, heq, norm_mul, hc₁, mul_one] using hs

/-- The smooth-domain definition supplies an actual flattened full
rectangle on which physical membership is exactly positive height.
The homeomorphism is built above from that domain's own graph. -/
theorem exists_smoothDomain_flattening_rectangle {Ω : Set ℂ} (hS : IsSmoothDomain Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      ∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im) := by
  obtain ⟨c, r, h, K, f, hc₁, hr, hh, hf, hLip, hf₀, _, hchart⟩ := hS.2 p hp
  have hc : c ≠ 0 := by
    intro heq
    simp only [heq, norm_zero] at hc₁
    norm_num at hc₁
  let a := min r (h / (4 * ((K : ℝ) + 1)))
  let b := h / 4
  have hden : 0 < 4 * ((K : ℝ) + 1) := by positivity
  have ha : 0 < a := lt_min hr (div_pos hh hden)
  have hb : 0 < b := div_pos hh (by norm_num)
  refine ⟨c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb, ?_⟩
  intro z hzre hzim
  have hzrer : |z.re| < r := hzre.trans_le (min_le_left _ _)
  have hscale : 4 * ((K : ℝ) + 1) * |z.re| < h := by
    simpa only [mul_comm] using
      (lt_div_iff₀ hden).mp (hzre.trans_le (min_le_right _ _))
  have hfz : |f z.re| ≤ (K : ℝ) * |z.re| := by
    simpa only [hf₀, sub_zero, Real.norm_eq_abs] using hLip.norm_sub_le z.re 0
  have hfzh : |f z.re| < h / 4 := by
    nlinarith [abs_nonneg z.re]
  have hy : |z.im + f z.re| < h := by
    have hs := abs_add_le z.im (f z.re)
    dsimp [b] at hzim
    linarith
  have hmem := hchart (smoothDirichletGraphChart p c hc f hf.continuous z)
    (by simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re] using hzrer)
    (by simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_im] using hy)
  simpa only [smoothDirichletGraphChart_rotate, smoothDirichletGraphShear_re,
    smoothDirichletGraphShear_im, lt_add_iff_pos_left] using hmem

/-- The bottom edge in an actual flattening rectangle maps to the
physical frontier. This follows from positive-height approach and
the local membership equivalence; frontier membership is not a new
coordinate premise. -/
theorem smoothDirichletGraphChart_mem_frontier {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    {x : ℝ} (hx : |x| < a) :
    smoothDirichletGraphChart p c hc f hf (x : ℂ) ∈ frontier Ω := by
  let Ψ := smoothDirichletGraphChart p c hc f hf
  have hnot : Ψ (x : ℂ) ∉ Ω := by
    have h := hchart (x : ℂ) (by simpa only [Complex.ofReal_re] using hx)
      (by simpa only [Complex.ofReal_im, abs_zero] using hb)
    simpa only [Complex.ofReal_im, lt_self_iff_false, iff_false] using h
  have hcurve : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have h : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝 ((x : ℂ) + (0 : ℂ) * Complex.I)) :=
      (tendsto_const_nhds.add
        ((Complex.ofRealCLM.continuous.tendsto 0).mul_const Complex.I)).mono_left
          nhdsWithin_le_nhds
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using h
  have hmem : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), Ψ ((x : ℂ) + (t : ℂ) * Complex.I) ∈ Ω := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht htb
    have ht₀ : 0 < t := ht
    apply (hchart _ (by simpa using hx) (by simpa [abs_of_pos ht₀] using htb)).mpr
    simpa using ht₀
  rw [hΩ.frontier_eq]
  exact ⟨mem_closure_of_tendsto ((Ψ.continuous.tendsto (x : ℂ)).comp hcurve) hmem, hnot⟩

/-- True zero boundary values of a physical continuous solution
remain true zero values on the flattened boundary interval. -/
theorem smoothDirichletGraphChart_zero_boundary {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    (v : ℂ → ℂ) (hv : ∀ z ∈ frontier Ω, v z = 0) {x : ℝ} (hx : |x| < a) :
    v (smoothDirichletGraphChart p c hc f hf (x : ℂ)) = 0 :=
  hv _ (smoothDirichletGraphChart_mem_frontier hΩ p c hc f hf hb hchart hx)

/-- An actual pointwise H¹ function remains pointwise H¹ under the
constructed graph coordinates. This uses the proved bi-Lipschitz
L² pullback and actual chain differential, with no assumed pullback
energy or flattened Sobolev regularity. -/
theorem smoothDirichletGraphChart_pullback_memLp {Ω U : Set ℂ}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    (himage : smoothDirichletGraphChart p c hc f hf.continuous '' U ⊆ Ω)
    {v : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω)
    (hm : MemLp v 2 (volume.restrict Ω))
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 (volume.restrict Ω)) :
    MemLp (fun z => v (smoothDirichletGraphChart p c hc f hf.continuous z)) 2
      (volume.restrict U) ∧
    ∀ i : Fin 2, MemLp
      (dirD (fun z => v (smoothDirichletGraphChart p c hc f hf.continuous z)) (coordDir i))
      2 (volume.restrict U) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  have hK : 0 < K + 1 := by positivity
  have hΨ : LipschitzOnWith (K + 1) Ψ U :=
    (smoothDirichletGraphChart_lipschitz p c hc hc₁ hLip).lipschitzOnWith
  have hΨinv : LipschitzOnWith (K + 1) Ψ.symm (Ψ '' U) :=
    (smoothDirichletGraphChart_symm_lipschitz p c hc hc₁ hLip).lipschitzOnWith
  have hm' : MemLp v 2 (volume.restrict (Ψ '' U)) :=
    hm.mono_measure (Measure.restrict_mono_set volume himage)
  have hg' (i : Fin 2) : MemLp (dirD v (coordDir i)) 2 (volume.restrict (Ψ '' U)) :=
    (hg i).mono_measure (Measure.restrict_mono_set volume himage)
  refine ⟨memLp_comp_bilip' hU hK hΨ hΨinv hm', ?_⟩
  intro i
  let G : Fin 2 → L2 (Ψ '' U) := fun j => (hg' j).toLp _
  have hmc := memLp_chainGrad hU hK hΨ hΨinv G i
  have hae : ∀ᵐ z ∂(volume.restrict U), ∀ j : Fin 2,
      G j (Ψ z) = dirD v (coordDir j) (Ψ z) :=
    ae_all_iff.mpr (fun j => (quasiMeasurePreserving_restrict hΨinv).ae (hg' j).coeFn_toLp)
  apply hmc.ae_eq
  filter_upwards [hae, ae_restrict_mem hU.measurableSet] with z hz hzU
  have hzΩ : Ψ z ∈ Ω := himage (mem_image_of_mem Ψ hzU)
  have hdv := (hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hzΩ)
  have hdΨ := ((smoothDirichletGraphChart_contDiff p c hc hf).differentiable (by simp)) z
  change chainGrad Ψ (fun j => (G j : ℂ → ℂ)) i z =
    fderiv ℝ (v ∘ Ψ) z (coordDir i)
  rw [fderiv_comp z hdv hdΨ, ContinuousLinearMap.comp_apply, clm_apply_eq_sum_coordRe]
  simp only [chainGrad, smul_eq_mul, hz, dirD]

def smoothDirichletHalfBox (a b : ℝ) : Set ℂ :=
  {z | |z.re| < a ∧ 0 < z.im ∧ z.im < b}

def smoothDirichletClosedHalfBox (a b : ℝ) : Set ℂ :=
  {z | |z.re| ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b}

theorem isOpen_smoothDirichletHalfBox (a b : ℝ) : IsOpen (smoothDirichletHalfBox a b) :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

/-- A complete actual flattened H¹ Dirichlet problem at each physical
boundary point. The pulled solution has zero values on the bottom
edge, continuous values on a closed half rectangle, and genuine L²
first derivatives. These properties are derived from the physical
Green correction, not prescribed as replacement hypotheses. -/
theorem exists_riemannMapping_flattened_zero_boundary_h1 {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let v := fun z => riemannMappingDirichletRemainder F d (Ψ z)
       MapsTo Ψ (smoothDirichletHalfBox a b) Ω ∧
       ContinuousOn v (smoothDirichletClosedHalfBox a b) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b) ∧
       (∀ x : ℝ, |x| < a → v (x : ℂ) = 0) ∧
       ∃ u : NeumannH1 (smoothDirichletHalfBox a b),
         (h1Value _ u : ℂ → ℂ) =ᵐ[volume.restrict (smoothDirichletHalfBox a b)] v ∧
         ∀ i : Fin 2, (h1Gradient _ i u : ℂ → ℂ)
           =ᵐ[volume.restrict (smoothDirichletHalfBox a b)] dirD v (coordDir i)) := by
  obtain ⟨d, u, hvcont, hvsmooth, hvzero, hu, hgu, _, _⟩ :=
    exists_riemannMapping_zero_boundary_poisson_problem hb hS hsc F hF hinj himage
  obtain ⟨c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀, hchart⟩ :=
    exists_smoothDomain_flattening_rectangle hS hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let V := smoothDirichletHalfBox (a / 2) (b / 2)
  let v := fun z => riemannMappingDirichletRemainder F d (Ψ z)
  have hV : IsOpen V := isOpen_smoothDirichletHalfBox _ _
  have hmap : MapsTo Ψ V Ω := by
    intro z hz
    apply (hchart z (hz.1.trans (by linarith)) ?_).mpr hz.2.1
    rw [abs_of_pos hz.2.1]
    exact hz.2.2.trans (by linarith)
  have hclosed : MapsTo Ψ (smoothDirichletClosedHalfBox (a / 2) (b / 2)) (closure Ω) := by
    intro z hz
    have hzr : |z.re| < a := hz.1.trans_lt (by linarith)
    have hzi : |z.im| < b := by rw [abs_of_nonneg hz.2.1]; linarith [hz.2.2]
    rcases eq_or_lt_of_le hz.2.1 with heq | hpos
    · have hzreal : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [← heq]
      rw [hzreal]
      exact frontier_subset_closure
        (smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous hb₀ hchart hzr)
    · exact subset_closure ((hchart z hzr hzi).mpr hpos)
  have hvs : ContDiffOn ℝ (⊤ : ℕ∞) v V :=
    hvsmooth.comp (smoothDirichletGraphChart_contDiff p c hc hf).contDiffOn hmap
  have hvm : MemLp (riemannMappingDirichletRemainder F d) 2 (volume.restrict Ω) :=
    (Lp.memLp (h1Value Ω u)).ae_eq hu
  have hgm (i : Fin 2) : MemLp (dirD (riemannMappingDirichletRemainder F d) (coordDir i))
      2 (volume.restrict Ω) := (Lp.memLp (h1Gradient Ω i u)).ae_eq (hgu i)
  obtain ⟨hvm', hgm'⟩ := smoothDirichletGraphChart_pullback_memLp
    hS.1.1 hV p c hc hc₁ hf hLip (mapsTo_iff_image_subset.mp hmap) hvsmooth hvm hgm
  have hw := isWeakGradient_of_contDiffOn hV hvs hvm' hgm'
  refine ⟨d, c, hc, f, hf, K, a / 2, b / 2, hc₁, hLip, hf₀, by positivity,
    by positivity, hmap, ?_, hvs, ?_, h1Vector hw, ?_, ?_⟩
  · exact hvcont.comp Ψ.continuous.continuousOn hclosed
  · intro x hx
    exact smoothDirichletGraphChart_zero_boundary hS.1.1 p c hc f hf.continuous
      hb₀ hchart _ hvzero (hx.trans (by linarith))
  · rw [h1Value_h1Vector]
    exact hvm'.coeFn_toLp
  · intro i
    rw [h1Gradient_h1Vector]
    exact (hgm' i).coeFn_toLp

/-! ## The actual elliptic coefficients of graph flattening -/

/-- The actual differential of the graph shear at graph slope `d`.
It maps `(x,y)` to `(x,y+d*x)`. -/
def smoothDirichletGraphDifferential (d : ℝ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ + (d • Complex.reCLM).smulRight Complex.I

@[simp] theorem smoothDirichletGraphDifferential_apply (d : ℝ) (w : ℂ) :
    smoothDirichletGraphDifferential d w = w + (d * w.re) • Complex.I := by
  simp only [smoothDirichletGraphDifferential, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, Complex.reCLM_apply, smul_eq_mul]

theorem smoothDirichletGraphShear_hasFDerivAt {f : ℝ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z.re) :
    HasFDerivAt (smoothDirichletGraphShear f)
      (smoothDirichletGraphDifferential (deriv f z.re)) z := by
  have hd := hf.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt
  have hs := (hasFDerivAt_id z).add (hd.smul_const Complex.I)
  have h_simpa := hs
  simp only [smoothDirichletGraphDifferential, smoothDirichletGraphShear, Function.comp_apply, Complex.real_smul, Function.comp_def] at h_simpa ⊢
  exact h_simpa

theorem smoothDirichletGraphChart_hasFDerivAt (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    HasFDerivAt (smoothDirichletGraphChart p c hc f hf.continuous)
      (c⁻¹ • smoothDirichletGraphDifferential (deriv f z.re)) z := by
  have hd := smoothDirichletGraphShear_hasFDerivAt ((hf.differentiable (by simp)) z.re)
  have hs := (hd.mul_const c⁻¹).const_add p
  convert hs using 1
  funext x
  simp only [smoothDirichletGraphChart_apply, div_eq_mul_inv]

theorem smoothDirichletGraphChart_fderiv_apply (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z w : ℂ) :
    fderiv ℝ (smoothDirichletGraphChart p c hc f hf.continuous) z w =
      c⁻¹ * (w + (deriv f z.re * w.re) • Complex.I) := by
  rw [(smoothDirichletGraphChart_hasFDerivAt p c hc hf z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    smoothDirichletGraphDifferential_apply]

/-- The actual chain rule exposes the inverse-graph energy
components. The physical derivatives occur in the rigid directions
`1/c` and `I/c`; the tangential shear term cancels exactly. -/
theorem smoothDirichletGraphChart_pullback_gradient (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {v : ℂ → ℂ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let u := v ∘ Ψ
     dirD u 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD u Complex.I z = fderiv ℝ v (Ψ z) (1 / c)) ∧
    dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z =
      fderiv ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z) (Complex.I / c) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let T := fderiv ℝ v (Ψ z)
  let d := deriv f z.re
  have hdΨ := (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hchain (w : ℂ) : dirD (v ∘ Ψ) w z = T (c⁻¹ * (w + (d * w.re) • Complex.I)) := by
    change fderiv ℝ (v ∘ Ψ) z w = _
    rw [fderiv_comp z hv hdΨ, ContinuousLinearMap.comp_apply,
      smoothDirichletGraphChart_fderiv_apply p c hc hf z w]
  have hI : dirD (v ∘ Ψ) Complex.I z = T (Complex.I / c) := by
    rw [hchain]
    simp only [Complex.I_re, mul_zero, zero_smul, add_zero, div_eq_mul_inv, mul_comm]
  have h1 : dirD (v ∘ Ψ) 1 z = T (1 / c) + d • T (Complex.I / c) := by
    rw [hchain]
    have he : c⁻¹ * ((1 : ℂ) + (d * (1 : ℂ).re) • Complex.I) =
        (1 / c : ℂ) + d • (Complex.I / c) := by
      simp only [Complex.one_re, mul_one, Complex.real_smul, div_eq_mul_inv]
      ring
    rw [he, map_add, map_smul]
  constructor
  · change dirD (v ∘ Ψ) 1 z - (d : ℂ) * dirD (v ∘ Ψ) Complex.I z = T (1 / c)
    rw [h1, hI, Complex.real_smul, add_sub_cancel_right]
  · exact hI

/-- The energy form of the inverse graph differential. Its matrix is
`[[1, -d], [-d, 1+d²]]`, with `d = f′(x)`. -/
def smoothDirichletGraphQuadratic (d x y : ℝ) : ℝ :=
  x ^ 2 - 2 * d * x * y + (1 + d ^ 2) * y ^ 2

theorem smoothDirichletGraphQuadratic_eq_sq (d x y : ℝ) :
    smoothDirichletGraphQuadratic d x y = (x - d * y) ^ 2 + y ^ 2 := by
  unfold smoothDirichletGraphQuadratic
  ring

theorem smoothDirichletGraphQuadratic_nonneg (d x y : ℝ) :
    0 ≤ smoothDirichletGraphQuadratic d x y := by
  rw [smoothDirichletGraphQuadratic_eq_sq]
  positivity

/-- Genuine ellipticity follows from the actual Lipschitz graph
bound; no elliptic coefficient premise is substituted for it. -/
theorem smoothDirichletGraphQuadratic_bounds {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (t x y : ℝ) :
    (x ^ 2 + y ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      smoothDirichletGraphQuadratic (deriv f t) x y ∧
    smoothDirichletGraphQuadratic (deriv f t) x y ≤
      2 * (1 + (K : ℝ) ^ 2) * (x ^ 2 + y ^ 2) := by
  let d := deriv f t
  have hd : |d| ≤ (K : ℝ) := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hf (x₀ := t)
  have hd₂ : d ^ 2 ≤ (K : ℝ) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg d) K.coe_nonneg).mpr hd
    simpa only [sq_abs] using hs
  have hq : 0 ≤ (x - d * y) ^ 2 + y ^ 2 := by positivity
  have hden : 0 < 2 * (1 + (K : ℝ) ^ 2) := by positivity
  have hlow : x ^ 2 + y ^ 2 ≤
      2 * (1 + d ^ 2) * ((x - d * y) ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - 2 * d * y), sq_nonneg y,
      mul_nonneg (sq_nonneg d) (sq_nonneg (x - d * y))]
  have hupp : (x - d * y) ^ 2 + y ^ 2 ≤
      2 * (1 + d ^ 2) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x + d * y),
      mul_nonneg (sq_nonneg d) (sq_nonneg x), sq_nonneg y]
  change (x ^ 2 + y ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      smoothDirichletGraphQuadratic d x y ∧
    smoothDirichletGraphQuadratic d x y ≤ 2 * (1 + (K : ℝ) ^ 2) * (x ^ 2 + y ^ 2)
  rw [smoothDirichletGraphQuadratic_eq_sq]
  constructor
  · apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hd₂) hq]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd₂)
      (add_nonneg (sq_nonneg x) (sq_nonneg y))]

/-- The same genuine elliptic bounds hold for complex-valued
solutions, by applying the real coefficient form to the actual real
and imaginary components. -/
theorem smoothDirichletGraph_complex_energy_bounds {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (t : ℝ) (x y : ℂ) :
    (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 ∧
    ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 ≤
      2 * (1 + (K : ℝ) ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨hr₁, hr₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.re y.re
  obtain ⟨hi₁, hi₂⟩ := smoothDirichletGraphQuadratic_bounds hf t x.im y.im
  have heq : ‖x - ((deriv f t : ℝ) : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 =
      smoothDirichletGraphQuadratic (deriv f t) x.re y.re +
        smoothDirichletGraphQuadratic (deriv f t) x.im y.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, smoothDirichletGraphQuadratic]
    ring
  rw [heq]
  constructor
  · have h := add_le_add hr₁ hi₁
    convert h using 1
    simp only [Complex.sq_norm, Complex.normSq_apply, ← add_div]
    ring
  · have h := add_le_add hr₂ hi₂
    convert h using 1
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring

theorem smoothDirichletGraphChart_actual_energy_bounds (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {v : ℂ → ℂ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
    let u := v ∘ Ψ
    (‖dirD u 1 z‖ ^ 2 + ‖dirD u Complex.I z‖ ^ 2) /
      (2 * (1 + (K : ℝ) ^ 2)) ≤
      ‖fderiv ℝ v (Ψ z) (1 / c)‖ ^ 2 + ‖fderiv ℝ v (Ψ z) (Complex.I / c)‖ ^ 2 ∧
    ‖fderiv ℝ v (Ψ z) (1 / c)‖ ^ 2 + ‖fderiv ℝ v (Ψ z) (Complex.I / c)‖ ^ 2 ≤
      2 * (1 + (K : ℝ) ^ 2) * (‖dirD u 1 z‖ ^ 2 + ‖dirD u Complex.I z‖ ^ 2) := by
  obtain ⟨hx, hy⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf hv
  have h := smoothDirichletGraph_complex_energy_bounds hLip z.re
    (dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) 1 z)
    (dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z)
  have hX : dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) 1 z -
      ((deriv f z.re : ℝ) : ℂ) *
        dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z =
      fderiv ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z) (1 / c) := hx
  have hY : dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z =
      fderiv ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z) (Complex.I / c) := hy
  dsimp only
  rw [← hX, ← hY]
  exact h

/-! ## The genuine one-dimensional zero-boundary energy step -/

/-- An actual continuous zero endpoint and an integrable interior
derivative give the primitive identity up to the endpoint. No
derivative or smooth extension is required at that endpoint. -/
theorem dirichlet_zero_endpoint_primitive {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {t : ℝ} (ht : t ∈ Ioc 0 b) :
    v t = ∫ s in (0 : ℝ)..t, dv s := by
  have hvc : ContinuousOn v (Icc 0 t) := hv.mono
    (Icc_subset_Icc le_rfl ht.2)
  have hleft : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (v 0)) := by
    have h := hvc 0 ⟨le_rfl, ht.1.le⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ht.1] at h
    exact h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hright : Tendsto v (𝓝[<] t) (𝓝 (v t)) := by
    have h := hvc t ⟨ht.1.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE ht.1] at h
    exact h.mono_left (nhdsWithin_mono t Iio_subset_Iic_self)
  have hm' : MemLp dv 2 (volume.restrict (Ioc 0 t)) :=
    hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))
  have hi : IntervalIntegrable dv volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le]
    exact hm'.integrable (by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht.1
    (fun s hs => hd s ⟨hs.1, hs.2.trans_le ht.2⟩) hi hleft hright
  rw [hv₀, sub_zero] at h
  exact h.symm

/-- Actual L² derivative energy controls the value next to a zero
endpoint. This is the estimate needed to remove a thin boundary
strip when closing Dirichlet tests in H¹. -/
theorem dirichlet_zero_endpoint_norm_sq_le {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {t : ℝ} (ht : t ∈ Ioc 0 b) :
    ‖v t‖ ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, ‖dv s‖ ^ 2 := by
  let μ := volume.restrict (Ioc (0 : ℝ) t)
  have hm' : MemLp dv 2 μ :=
    hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))
  have h1 : MemLp (fun _ : ℝ => (1 : ℂ)) 2 μ := memLp_const 1
  have hi : (∫ s in (0 : ℝ)..t, dv s) = inner ℂ (h1.toLp _) (hm'.toLp _) := by
    rw [intervalIntegral.integral_of_le ht.1.le, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp, hm'.coeFn_toLp] with s hs₁ hs₂
    simp only [hs₁, hs₂, RCLike.inner_apply, map_one, mul_one]
  have hnorm : ‖∫ s in (0 : ℝ)..t, dv s‖ ≤ ‖h1.toLp _‖ * ‖hm'.toLp _‖ := by
    rw [hi]
    exact norm_inner_le_norm _ _
  have hnormsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  have hn₁ : ‖h1.toLp _‖ ^ 2 = t := by
    rw [norm_sq_toLp_eq_integral]
    simp only [norm_one, one_pow]
    simp [μ, Measure.real, ht.1.le]
  have hn₂ : ‖hm'.toLp _‖ ^ 2 = ∫ s in (0 : ℝ)..t, ‖dv s‖ ^ 2 := by
    rw [norm_sq_toLp_eq_integral, intervalIntegral.integral_of_le ht.1.le]
  rw [mul_pow, hn₁, hn₂] at hnormsq
  rw [dirichlet_zero_endpoint_primitive hv hv₀ hd hm ht]
  exact hnormsq

/-- The actual zero endpoint controls the mass of a thin boundary
strip by the derivative energy in that same strip. The crude
constant `1` is sufficient to close Dirichlet cutoff tests. -/
theorem dirichlet_zero_endpoint_strip_mass_le {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {ε : ℝ} (hε : ε ∈ Ioc 0 b) :
    (∫ t in (0 : ℝ)..ε, ‖v t‖ ^ 2) / ε ^ 2 ≤
      ∫ t in (0 : ℝ)..ε, ‖dv t‖ ^ 2 := by
  have hmi : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioc 0 b) :=
    hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hI : IntervalIntegrable (fun t => ‖dv t‖ ^ 2) volume 0 ε := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε.1.le]
    exact hmi.mono_set (Ioc_subset_Ioc le_rfl hε.2)
  have hV : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 ε :=
    ((hv.mono (Icc_subset_Icc le_rfl hε.2)).norm.pow 2).intervalIntegrable_of_Icc hε.1.le
  have hE : 0 ≤ ∫ t in (0 : ℝ)..ε, ‖dv t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hε.1.le]
    exact integral_nonneg (fun t => sq_nonneg _)
  have hbnd (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      ‖v t‖ ^ 2 ≤ ε * ∫ s in (0 : ℝ)..ε, ‖dv s‖ ^ 2 := by
    have hpt := dirichlet_zero_endpoint_norm_sq_le hv hv₀ hd hm
      (show t ∈ Ioc 0 b from ⟨ht.1, ht.2.le.trans hε.2⟩)
    have hmono : (∫ s in (0 : ℝ)..t, ‖dv s‖ ^ 2) ≤
        ∫ s in (0 : ℝ)..ε, ‖dv s‖ ^ 2 :=
      intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le
        (Eventually.of_forall fun _ => sq_nonneg _) hI
    exact hpt.trans ((mul_le_mul_of_nonneg_left hmono ht.1.le).trans
      (mul_le_mul_of_nonneg_right ht.2.le hE))
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hε.1.le hV
    (intervalIntegrable_const (c := ε * ∫ s in (0 : ℝ)..ε, ‖dv s‖ ^ 2)) hbnd
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hbound
  apply (div_le_iff₀ (sq_pos_of_pos hε.1)).mpr
  nlinarith

/-- The boundary-strip mass after the derivative-scale normalization
really tends to zero. This uses continuity only for the solution's
values, and L² energy only for its true interior derivative. -/
theorem dirichlet_zero_endpoint_strip_mass_tendsto_zero {b : ℝ} (hb : 0 < b)
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) :
    Tendsto (fun ε : ℝ => (∫ t in (0 : ℝ)..ε, ‖v t‖ ^ 2) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmi : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioc 0 b) :=
    hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hI : IntervalIntegrable (fun t => ‖dv t‖ ^ 2) volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr hmi
  have hE : Tendsto (fun ε : ℝ => ∫ t in (0 : ℝ)..ε, ‖dv t‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc := intervalIntegral.continuousOn_primitive_interval' hI left_mem_uIcc
    have h := hc 0 left_mem_uIcc
    rw [ContinuousWithinAt, uIcc_of_le hb.le, nhdsWithin_Icc_eq_nhdsGE hb] at h
    simpa only [intervalIntegral.integral_same] using
      h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε₀ : 0 < ε := hε
    rw [intervalIntegral.integral_of_le hε₀.le]
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    exact dirichlet_zero_endpoint_strip_mass_le hv hv₀ hd hm ⟨hε, hεb.le⟩

/-- Genuine L² normal derivative energy gives L² energy on almost
every vertical slice, by the actual Lebesgue coordinate map. -/
theorem dirichlet_halfBox_vertical_memLp {a b : ℝ} {v : ℂ → ℂ}
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
      MemLp (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) 2
        (volume.restrict (Ioc (0 : ℝ) b)) := by
  let e : (ℝ × ℝ) ≃ᵐ ℂ := Complex.measurableEquivRealProd.symm
  have hp : MeasurePreserving e volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  have he (p : ℝ × ℝ) : e p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt, and_assoc]
  have henergy := hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hprod := (hp.integrableOn_comp_preimage e.measurableEmbedding).mpr henergy
  rw [hpre, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  change Integrable (fun p : ℝ × ℝ => ‖dirD v Complex.I (e p)‖ ^ 2)
    ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo (0 : ℝ) b))) at hprod
  have hslice := hprod.prod_right_ae
  simp only [he] at hslice
  filter_upwards [hslice] with x hx
  have hLc : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) := continuous_const.add
    (Complex.ofRealCLM.continuous.mul continuous_const)
  have hmeas : Measurable (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    (measurable_fderiv_apply_const ℝ v Complex.I).comp hLc.measurable
  have hmL : MemLp (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) 2
      (volume.restrict (Ioo 0 b)) :=
    (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr hx
  rw [restrict_Ioo_eq_restrict_Ioc] at hmL
  exact hmL

theorem dirichlet_halfBox_vertical_hasDerivAt {a b : ℝ} {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    {x y : ℝ} (hx : |x| < a) (hy : y ∈ Ioo 0 b) :
    HasDerivAt (fun s : ℝ => v ((x : ℂ) + (s : ℂ) * Complex.I))
      (dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) y := by
  have hyV : (x : ℂ) + (y : ℂ) * Complex.I ∈ smoothDirichletHalfBox a b := by
    simpa [smoothDirichletHalfBox] using (show |x| < a ∧ 0 < y ∧ y < b from ⟨hx, hy.1, hy.2⟩)
  have hdv := (hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hyV)
  have hL : HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) Complex.I y := by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)
  exact hdv.hasFDerivAt.comp_hasDerivAt y hL

/-- The endpoint primitive and energy estimate hold on almost every
actual vertical slice of the flattened solution. Slice L² energy is
derived by measure-preserving real coordinates and Fubini, rather
than being a boundary regularity assumption. -/
theorem dirichlet_halfBox_vertical_energy {a b : ℝ}
    {v : ℂ → ℂ} (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a), ∀ t ∈ Ioc (0 : ℝ) b,
      v ((x : ℂ) + (t : ℂ) * Complex.I) =
        (∫ s in (0 : ℝ)..t, dirD v Complex.I ((x : ℂ) + (s : ℂ) * Complex.I)) ∧
      ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤
        t * ∫ s in (0 : ℝ)..t, ‖dirD v Complex.I ((x : ℂ) + (s : ℂ) * Complex.I)‖ ^ 2 := by
  filter_upwards [dirichlet_halfBox_vertical_memLp hg, ae_restrict_mem measurableSet_Ioo]
    with x hmL hxI
  have hxabs : |x| < a := abs_lt.mpr hxI
  let L : ℝ → ℂ := fun y => (x : ℂ) + (y : ℂ) * Complex.I
  have hLc : Continuous L := continuous_const.add
    (Complex.ofRealCLM.continuous.mul continuous_const)
  have hLclosed : MapsTo L (Icc 0 b) (smoothDirichletClosedHalfBox a b) := by
    intro y hy
    simpa [smoothDirichletClosedHalfBox, L] using
      (show |x| ≤ a ∧ 0 ≤ y ∧ y ≤ b from ⟨hxabs.le, hy.1, hy.2⟩)
  have hvL : ContinuousOn (v ∘ L) (Icc 0 b) := hv.comp hLc.continuousOn hLclosed
  have hzero : (v ∘ L) 0 = 0 := by simpa [L] using hz x hxabs
  have hd (y : ℝ) (hy : y ∈ Ioo 0 b) :
      HasDerivAt (v ∘ L) (dirD v Complex.I (L y)) y := by
    exact dirichlet_halfBox_vertical_hasDerivAt hs hxabs hy
  intro t ht
  exact ⟨dirichlet_zero_endpoint_primitive hvL hzero hd hmL ht,
    dirichlet_zero_endpoint_norm_sq_le hvL hzero hd hmL ht⟩

/-- The vertical zero-boundary energy estimate is now instantiated
on the actual conformal Green correction at every original smooth
physical boundary point. In particular, no desired trace or Hardy
support premise is inserted to obtain this local Dirichlet estimate. -/
theorem exists_riemannMapping_flattened_vertical_energy {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (let v := fun z => riemannMappingDirichletRemainder F d
         (smoothDirichletGraphChart p c hc f hf.continuous z)
       ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a), ∀ t ∈ Ioc (0 : ℝ) b,
         v ((x : ℂ) + (t : ℂ) * Complex.I) =
           (∫ s in (0 : ℝ)..t, dirD v Complex.I ((x : ℂ) + (s : ℂ) * Complex.I)) ∧
         ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤
           t * ∫ s in (0 : ℝ)..t, ‖dirD v Complex.I ((x : ℂ) + (s : ℂ) * Complex.I)‖ ^ 2) := by
  obtain ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀,
    _, hv, hs, hz, u, _, hgu⟩ :=
    exists_riemannMapping_flattened_zero_boundary_h1 hb hS hsc F hF hinj himage hp
  refine ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀, ?_⟩
  apply dirichlet_halfBox_vertical_energy hv hs hz
  have hg := (Lp.memLp (h1Gradient (smoothDirichletHalfBox a b) 1 u)).ae_eq (hgu 1)
  have h_simpa := hg
  simp only [coordDir, Fin.cons_one, Fin.cons_zero] at h_simpa ⊢
  exact h_simpa

/-- Actual half-rectangle L² energy in real product coordinates.
This is precisely the product measure of its two coordinate
intervals, with the physical Lebesgue normalization preserved. -/
theorem dirichlet_halfBox_sq_integrable_real_prod {a b : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Integrable (fun p : ℝ × ℝ => ‖g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ^ 2)
      ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo (0 : ℝ) b))) := by
  let e : (ℝ × ℝ) ≃ᵐ ℂ := Complex.measurableEquivRealProd.symm
  have hp : MeasurePreserving e volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  have he (p : ℝ × ℝ) : e p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt, and_assoc]
  have henergy := hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hprod := (hp.integrableOn_comp_preimage e.measurableEmbedding).mpr henergy
  rw [hpre, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  change Integrable (fun p : ℝ × ℝ => ‖g (e p)‖ ^ 2)
    ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo (0 : ℝ) b))) at hprod
  simpa only [he] using hprod

/-- The true boundary-strip estimate after integration over the
tangential variable. Both sides are actual two-dimensional energies,
expressed by Fubini with the ordinary Lebesgue measure. -/
theorem dirichlet_halfBox_strip_mass_le {a b : ℝ}
    {v : ℂ → ℂ} (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    {ε : ℝ} (hε : ε ∈ Ioc 0 b) :
    (∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
      ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2 ≤
    ∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hsub : smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le hε.2⟩
  have hvm := hm.mono_measure (Measure.restrict_mono_set volume hsub)
  have hgm := hg.mono_measure (Measure.restrict_mono_set volume hsub)
  have hVi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
      ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hvm).integral_prod_left
  have hGi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hε.1.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hgm).integral_prod_left
  have hbound :
      (fun x : ℝ => (∫ t in (0 : ℝ)..ε, ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2)
        ≤ᵐ[volume.restrict (Ioo (-a) a)]
      (fun x : ℝ => ∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
    filter_upwards [dirichlet_halfBox_vertical_memLp hg, ae_restrict_mem measurableSet_Ioo]
      with x hmL hxI
    have hx : |x| < a := abs_lt.mpr hxI
    let L : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I
    have hLc : Continuous L := continuous_const.add
      (Complex.ofRealCLM.continuous.mul continuous_const)
    have hmap : MapsTo L (Icc 0 b) (smoothDirichletClosedHalfBox a b) := by
      intro t ht
      simpa [L, smoothDirichletClosedHalfBox] using
        (show |x| ≤ a ∧ 0 ≤ t ∧ t ≤ b from ⟨hx.le, ht.1, ht.2⟩)
    have hvL := hv.comp hLc.continuousOn hmap
    have hzero : (v ∘ L) 0 = 0 := by simpa [L] using hz x hx
    exact dirichlet_zero_endpoint_strip_mass_le hvL hzero
      (fun t ht => dirichlet_halfBox_vertical_hasDerivAt hs hx ht) hmL hε
  have hi := integral_mono_ae (hVi.div_const (ε ^ 2)) hGi hbound
  simpa only [div_eq_mul_inv, integral_mul_const] using hi

theorem dirichlet_slice_energy_tendsto_zero {b : ℝ} (hb : 0 < b) {dv : ℝ → ℂ}
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) :
    Tendsto (fun ε : ℝ => ∫ t in (0 : ℝ)..ε, ‖dv t‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi : IntervalIntegrable (fun t => ‖dv t‖ ^ 2) volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
      (hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have h := hc 0 left_mem_uIcc
  rw [ContinuousWithinAt, uIcc_of_le hb.le, nhdsWithin_Icc_eq_nhdsGE hb] at h
  simpa only [intervalIntegral.integral_same] using
    h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- The actual normal energy in a shrinking boundary strip tends
to zero after tangential integration. The majorant is the genuine
full-rectangle L² normal energy obtained from Fubini. -/
theorem dirichlet_halfBox_normal_strip_energy_tendsto_zero {a b : ℝ} (hb : 0 < b)
    {v : ℂ → ℂ}
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let B : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..b,
    ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
  have hB : Integrable B (volume.restrict (Ioo (-a) a)) := by
    simpa only [B, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hg).integral_prod_left
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    have hsub : smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b :=
      fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans hεb⟩
    have hgm := hg.mono_measure (Measure.restrict_mono_set volume hsub)
    have hi := (dirichlet_halfBox_sq_integrable_real_prod hgm).integral_prod_left
    have hc : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        (volume.restrict (Ioo (-a) a)) := by
      simpa only [intervalIntegral.integral_of_le (show 0 ≤ ε from hε.le),
        integral_Ioc_eq_integral_Ioo] using hi
    exact hc.aestronglyMeasurable
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
      ‖∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2‖ ≤ B x := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    filter_upwards [dirichlet_halfBox_vertical_memLp hg] with x hx
    have hε₀ : 0 < ε := hε
    have hi : IntervalIntegrable
        (fun t => ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) volume 0 b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
        (hx.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    have hnon : 0 ≤ ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hε₀.le]
      exact integral_nonneg (fun _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnon]
    exact intervalIntegral.integral_mono_interval le_rfl hε₀.le hεb.le
      (Eventually.of_forall fun _ => sq_nonneg _) hi
  have hlim : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a), Tendsto
      (fun ε : ℝ => ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards [dirichlet_halfBox_vertical_memLp hg] with x hx
    exact dirichlet_slice_energy_tendsto_zero hb hx
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (f := fun _ : ℝ => (0 : ℝ)) B hmeas hbound hB hlim
  simpa only [integral_zero] using h

/-- The derivative-scale boundary-strip mass tends to zero in the
actual full half rectangle. This is the genuine estimate needed for
normal cutoffs when extending the weak equation to zero-boundary H¹
tests. It still does not assert a boundary second-derivative gain. -/
theorem dirichlet_halfBox_strip_mass_tendsto_zero {a b : ℝ} (hb : 0 < b)
    {v : ℂ → ℂ} (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ =>
      (∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (dirichlet_halfBox_normal_strip_energy_tendsto_zero hb hg)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε₀ : 0 < ε := hε
    apply div_nonneg _ (sq_nonneg _)
    apply integral_nonneg
    intro x
    change (0 : ℝ) ≤ ∫ t in (0 : ℝ)..ε, ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
    rw [intervalIntegral.integral_of_le hε₀.le]
    exact integral_nonneg (fun _ => sq_nonneg _)
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    exact dirichlet_halfBox_strip_mass_le hv hs hz hm hg ⟨hε, hεb.le⟩

/-- The actual conformal Green correction has vanishing
derivative-scale boundary-strip mass in genuine smooth graph
coordinates, from only the original supplied interior map and
smooth physical domain. -/
theorem exists_riemannMapping_flattened_strip_mass_decay {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (let v := fun z => riemannMappingDirichletRemainder F d
         (smoothDirichletGraphChart p c hc f hf.continuous z)
       Tendsto (fun ε : ℝ =>
          (∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
           ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2)
         (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  obtain ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀,
    _, hv, hs, hz, u, hu, hgu⟩ :=
    exists_riemannMapping_flattened_zero_boundary_h1 hb hS hsc F hF hinj himage hp
  refine ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀, ?_⟩
  apply dirichlet_halfBox_strip_mass_tendsto_zero hb₀ hv hs hz
  · exact (Lp.memLp (h1Value (smoothDirichletHalfBox a b) u)).ae_eq hu
  · have hg := (Lp.memLp (h1Gradient (smoothDirichletHalfBox a b) 1 u)).ae_eq (hgu 1)
    have h_simpa := hg
    simp only [coordDir, Fin.cons_one, Fin.cons_zero] at h_simpa ⊢
    exact h_simpa

/-! ### Genuine smooth normal cutoffs -/

/-- The derivative of the actual smooth transition is zero off its
transition interval, including its two endpoints. The endpoint assertion
uses genuine differentiability at the global minimum or maximum. -/
theorem dirichlet_smoothTransition_deriv_eq_zero {t : ℝ}
    (ht : t ≤ 0 ∨ 1 ≤ t) : deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have hmin : IsLocalMin Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition t ≤ Real.smoothTransition s
      rw [Real.smoothTransition.zero_of_nonpos ht]
      exact Eventually.of_forall Real.smoothTransition.nonneg
    exact hmin.deriv_eq_zero
  · have hmax : IsLocalMax Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition s ≤ Real.smoothTransition t
      rw [Real.smoothTransition.one_of_one_le ht]
      exact Eventually.of_forall Real.smoothTransition.le_one
    exact hmax.deriv_eq_zero

theorem exists_dirichlet_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (show ContDiff ℝ 2 Real.smoothTransition from Real.smoothTransition.contDiff).continuous_deriv
      (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have htz : t ≤ 0 ∨ 1 ≤ t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      exact ht.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
    rw [dirichlet_smoothTransition_deriv_eq_zero htz, norm_zero]
    exact le_max_right _ _

/-- A genuine smooth cutoff of the normal coordinate: it is zero below
height `ε` and one above height `2 * ε`. -/
def dirichletNormalCutoff (ε : ℝ) (z : ℂ) : ℂ :=
  (Real.smoothTransition (z.im / ε - 1) : ℂ)

theorem dirichletNormalCutoff_contDiff (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletNormalCutoff ε) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((Complex.imCLM.contDiff.div_const ε).sub contDiff_const))

theorem dirichletNormalCutoff_nonneg (ε : ℝ) (z : ℂ) :
    0 ≤ (dirichletNormalCutoff ε z).re := Real.smoothTransition.nonneg _

theorem norm_dirichletNormalCutoff_le (ε : ℝ) (z : ℂ) :
    ‖dirichletNormalCutoff ε z‖ ≤ 1 := by
  rw [dirichletNormalCutoff, Complex.norm_real, Real.norm_of_nonneg
    (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem dirichletNormalCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z.im ≤ ε) : dirichletNormalCutoff ε z = 0 := by
  have ht : z.im / ε - 1 ≤ 0 := by
    have := (div_le_one hε).mpr hz
    linarith
  simp only [dirichletNormalCutoff, Real.smoothTransition.zero_of_nonpos ht,
    Complex.ofReal_zero]

theorem dirichletNormalCutoff_eq_one {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : 2 * ε ≤ z.im) : dirichletNormalCutoff ε z = 1 := by
  have ht : 1 ≤ z.im / ε - 1 := by
    have := (le_div_iff₀ hε).mpr hz
    linarith
  simp only [dirichletNormalCutoff, Real.smoothTransition.one_of_one_le ht,
    Complex.ofReal_one]

theorem dirichletNormalCutoff_fderiv (ε : ℝ) (z w : ℂ) :
    fderiv ℝ (dirichletNormalCutoff ε) z w =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε * w.im : ℝ) : ℂ) := by
  have hi : HasFDerivAt (fun u : ℂ => u.im / ε - 1)
      (ε⁻¹ • Complex.imCLM) z := by
    have h_simpa := ((Complex.imCLM.hasFDerivAt (x := z)).mul_const ε⁻¹).sub_const 1
    simp only [div_eq_mul_inv] at h_simpa ⊢
    exact h_simpa
  have ht := (show Differentiable ℝ Real.smoothTransition from
    (show ContDiff ℝ 1 Real.smoothTransition from Real.smoothTransition.contDiff).differentiable
      (by norm_num)) (z.im / ε - 1)
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z (ht.hasDerivAt.comp_hasFDerivAt z hi)
  have hd' : HasFDerivAt (dirichletNormalCutoff ε)
      (Complex.ofRealCLM.comp
        (deriv Real.smoothTransition (z.im / ε - 1) • (ε⁻¹ • Complex.imCLM))) z := hd
  rw [hd'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.imCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul, div_eq_mul_inv,
    mul_assoc]

@[simp] theorem dirD_dirichletNormalCutoff_one (ε : ℝ) (z : ℂ) :
    dirD (dirichletNormalCutoff ε) 1 z = 0 := by
  simp only [dirD, dirichletNormalCutoff_fderiv, Complex.one_im, mul_zero,
    Complex.ofReal_zero]

theorem dirD_dirichletNormalCutoff_I (ε : ℝ) (z : ℂ) :
    dirD (dirichletNormalCutoff ε) Complex.I z =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε : ℝ) : ℂ) := by
  simp only [dirD, dirichletNormalCutoff_fderiv, Complex.I_im, mul_one]

theorem dirD_dirichletNormalCutoff_I_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z.im ≤ ε ∨ 2 * ε ≤ z.im) :
    dirD (dirichletNormalCutoff ε) Complex.I z = 0 := by
  have ht : z.im / ε - 1 ≤ 0 ∨ 1 ≤ z.im / ε - 1 := by
    rcases hz with hz | hz
    · have := (div_le_one hε).mpr hz
      exact Or.inl (by linarith)
    · have := (le_div_iff₀ hε).mpr hz
      exact Or.inr (by linarith)
  rw [dirD_dirichletNormalCutoff_I, dirichlet_smoothTransition_deriv_eq_zero ht]
  simp only [zero_div, Complex.ofReal_zero]

theorem norm_dirD_dirichletNormalCutoff_I_le {C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) (z : ℂ) :
    ‖dirD (dirichletNormalCutoff ε) Complex.I z‖ ≤ C / ε := by
  rw [dirD_dirichletNormalCutoff_I, Complex.norm_real, norm_div,
    Real.norm_of_nonneg hε.le]
  exact div_le_div_of_nonneg_right (hC _) hε.le

/-- The actual additional gradient term created by a normal cutoff. -/
def dirichletNormalCutoffError (ε : ℝ) (v : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirD (dirichletNormalCutoff ε) Complex.I z * v z

theorem dirichletNormalCutoffError_memLp {a b C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) {v : ℂ → ℂ}
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletNormalCutoffError ε v) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hd : Continuous (dirD (dirichletNormalCutoff ε) Complex.I) :=
    ((dirichletNormalCutoff_contDiff ε).fderiv_right
      (m := (⊤ : ℕ∞)) le_rfl).continuous.clm_apply continuous_const
  apply hm.of_le_mul (c := C / ε) (hd.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖dirD (dirichletNormalCutoff ε) Complex.I z * v z‖ ≤ (C / ε) * ‖v z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_dirD_dirichletNormalCutoff_I_le hε hC z)
      (norm_nonneg _)

theorem dirichletNormalCutoffError_slice_eq_strip {ε b : ℝ} (hε : 0 < ε)
    (hεb : 2 * ε ≤ b) (v : ℂ → ℂ) (x : ℝ) :
    (∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) =
    ∫ t in (0 : ℝ)..(2 * ε),
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ b),
    intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * ε)]
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc le_rfl hεb)
  intro t ht
  have ht' : 2 * ε ≤ t := by
    have : ¬ t ≤ 2 * ε := fun h => ht.2 ⟨ht.1.1, h⟩
    exact (lt_of_not_ge this).le
  have hzero : dirD (dirichletNormalCutoff ε) Complex.I
      ((x : ℂ) + (t : ℂ) * Complex.I) = 0 :=
    dirD_dirichletNormalCutoff_I_eq_zero hε (Or.inr (by simpa using ht'))
  simp only [dirichletNormalCutoffError, hzero, zero_mul, norm_zero, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

/-- The full additional-gradient energy is bounded by the genuine
derivative-scale strip mass. No boundary derivative or target H² gain
is used in this cutoff estimate. -/
theorem dirichletNormalCutoffError_energy_le {a b C ε : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε ≤ b) (hC₀ : 0 ≤ C)
    (hC : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤
    (C ^ 2 / ε ^ 2) *
      (∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hb : 0 < b := (by positivity : 0 < 2 * ε).trans_le hεb
  have hE := dirichletNormalCutoffError_memLp hε hC hm
  have hEi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hE).integral_prod_left
  have hsub : smoothDirichletHalfBox a (2 * ε) ⊆ smoothDirichletHalfBox a b :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le hεb⟩
  have hmi := hm.mono_measure (Measure.restrict_mono_set volume hsub)
  have hVi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..(2 * ε),
      ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * ε),
      integral_Ioc_eq_integral_Ioo]
      using (dirichlet_halfBox_sq_integrable_real_prod hmi).integral_prod_left
  have hpoint : (fun x : ℝ => ∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ᵐ[volume.restrict (Ioo (-a) a)]
      (fun x : ℝ => (C ^ 2 / ε ^ 2) * ∫ t in (0 : ℝ)..(2 * ε),
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxabs : |x| < a := abs_lt.mpr hx
    let L : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I
    have hLc : Continuous L := continuous_const.add
      (Complex.ofRealCLM.continuous.mul continuous_const)
    have hmap : MapsTo L (Icc 0 (2 * ε)) (smoothDirichletClosedHalfBox a b) := by
      intro t ht
      simpa [L, smoothDirichletClosedHalfBox] using
        (show |x| ≤ a ∧ 0 ≤ t ∧ t ≤ b from ⟨hxabs.le, ht.1, ht.2.trans hεb⟩)
    have hvL := hv.comp hLc.continuousOn hmap
    have hdL : Continuous (fun t =>
        dirD (dirichletNormalCutoff ε) Complex.I (L t)) :=
      (((dirichletNormalCutoff_contDiff ε).fderiv_right
        (m := (⊤ : ℕ∞)) le_rfl).continuous.clm_apply continuous_const).comp hLc
    have hVL : IntervalIntegrable (fun t => ‖v (L t)‖ ^ 2) volume 0 (2 * ε) :=
      (hvL.norm.pow 2).intervalIntegrable_of_Icc (by positivity)
    have hEL : IntervalIntegrable (fun t =>
        ‖dirichletNormalCutoffError ε v (L t)‖ ^ 2) volume 0 (2 * ε) :=
      (((hdL.continuousOn.mul hvL).norm).pow 2).intervalIntegrable_of_Icc (by positivity)
    have hle : ∀ t ∈ Ioo 0 (2 * ε),
        ‖dirichletNormalCutoffError ε v (L t)‖ ^ 2 ≤
          (C ^ 2 / ε ^ 2) * ‖v (L t)‖ ^ 2 := by
      intro t _
      dsimp only [dirichletNormalCutoffError]
      rw [norm_mul, mul_pow]
      have hn := (sq_le_sq₀ (norm_nonneg _)
        (div_nonneg hC₀ hε.le)).mpr (norm_dirD_dirichletNormalCutoff_I_le hε hC (L t))
      simpa only [div_pow] using mul_le_mul_of_nonneg_right hn (sq_nonneg _)
    rw [dirichletNormalCutoffError_slice_eq_strip hε hεb]
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (by positivity : 0 ≤ 2 * ε)
      hEL (hVL.const_mul (C ^ 2 / ε ^ 2)) hle
    simpa only [L, intervalIntegral.integral_const_mul] using h
  simpa only [integral_const_mul] using
    integral_mono_ae hEi (hVi.const_mul (C ^ 2 / ε ^ 2)) hpoint

/-- The genuine normal cutoff's additional gradient tends to zero
in the full two-dimensional energy. This is derived from actual
zero boundary values and H¹ energy, not from an asserted density
or boundary regularity principle. -/
theorem dirichletNormalCutoffError_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..b,
      ‖dirichletNormalCutoffError ε v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC₀, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
  have hscale : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝 (2 * 0)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε₀ : 0 < ε := hε
      show 0 < 2 * ε
      positivity
  have hstrip := (dirichlet_halfBox_strip_mass_tendsto_zero hb hv hs hz hm hg).comp hscale
  have hupper : Tendsto (fun ε : ℝ => (C ^ 2 / ε ^ 2) *
      (∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (4 * C ^ 2) *
        ((∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
          ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / (2 * ε) ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 ((4 * C ^ 2) * 0)) :=
      tendsto_const_nhds.mul hstrip
    have heq : ∀ ε : ℝ, (C ^ 2 / ε ^ 2) *
        (∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
          ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) =
        (4 * C ^ 2) * ((∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
          ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / (2 * ε) ^ 2) := by
      intro ε
      by_cases hε : ε = 0
      · simp only [hε, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          div_zero, zero_mul, mul_zero]
      · have hfactor (m : ℝ) : (C ^ 2 / ε ^ 2) * m =
            (4 * C ^ 2) * (m / (2 * ε) ^ 2) := by
          field_simp [hε]
          ring
        exact hfactor _
    simpa only [← heq, mul_zero] using
      (h : Tendsto (fun ε : ℝ => (4 * C ^ 2) *
        ((∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
          ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / (2 * ε) ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 ((4 * C ^ 2) * 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun ε => integral_nonneg fun x =>
      intervalIntegral.integral_nonneg_of_forall hb.le (fun _ => sq_nonneg _)
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (half_pos hb)).filter_mono nhdsWithin_le_nhds]
      with ε hε hεb
    exact dirichletNormalCutoffError_energy_le hε (by linarith) hC₀ hC hv hm

/-- Fubini identifies the actual physical squared norm with its two
real coordinate integrals. The coordinate transformation has Jacobian
one, so no scale factor is introduced. -/
theorem dirichlet_halfBox_sq_integral_eq_real_prod {a b : ℝ} (hb : 0 < b)
    {g : ℂ → ℂ} (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..b,
        ‖g ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  let e := Complex.measurableEquivRealProd.symm
  have hp : MeasurePreserving e volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  have he (p : ℝ × ℝ) : e p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩
    simp [e, smoothDirichletHalfBox, abs_lt, and_assoc]
  have hmeas : MeasurableSet (smoothDirichletHalfBox a b) :=
    (isOpen_smoothDirichletHalfBox a b).measurableSet
  have hind : (fun p => (smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2) (e p)) =
      (e ⁻¹' smoothDirichletHalfBox a b).indicator (fun p => ‖g (e p)‖ ^ 2) := by
    funext p
    by_cases hz : e p ∈ smoothDirichletHalfBox a b <;> simp [hz]
  have hi := hp.integral_comp e.measurableEmbedding
    ((smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2))
  rw [hind, integral_indicator (hmeas.preimage e.measurable),
    integral_indicator hmeas, hpre, Measure.volume_eq_prod,
    ← Measure.prod_restrict] at hi
  rw [← hi]
  have hprod := dirichlet_halfBox_sq_integrable_real_prod hg
  simpa only [he, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
    using integral_prod
      (fun p : ℝ × ℝ => ‖g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ^ 2) hprod

theorem dirichletNormalCutoffError_physical_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirichletNormalCutoffError ε v z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
  apply (dirichletNormalCutoffError_energy_tendsto_zero hb hv hs hz hm hg).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (dirichlet_halfBox_sq_integral_eq_real_prod hb
    (dirichletNormalCutoffError_memLp hε hC hm)).symm

theorem dirichletNormalCutoff_tendsto_one {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun ε : ℝ => dirichletNormalCutoff ε z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (half_pos hz)).filter_mono nhdsWithin_le_nhds]
    with ε hε hεz
  exact (dirichletNormalCutoff_eq_one hε (by linarith)).symm

/-- Multiplication by the actual cutoff tends to the identity in L².
The majorant is four times the original squared norm. -/
theorem dirichletNormalCutoff_weight_error_energy_tendsto_zero {a b : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let B : ℂ → ℝ := fun z => 4 * ‖g z‖ ^ 2
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable
      (fun z => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) μ := by
    intro ε
    exact ((((dirichletNormalCutoff_contDiff ε).continuous.sub continuous_const).aestronglyMeasurable.mul
      hg.aestronglyMeasurable).norm).pow 2
  have hbound : ∀ ε : ℝ, ∀ᵐ z ∂μ,
      ‖‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2‖ ≤ B z := by
    intro ε
    exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hnorm : ‖dirichletNormalCutoff ε z - 1‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by
          rw [norm_one]
          linarith [norm_dirichletNormalCutoff_le ε z])
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr hnorm
      simpa only [B, show (2 : ℝ) ^ 2 = 4 by norm_num] using
        mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖g z‖)
  have hB : Integrable B μ :=
    (hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul 4
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun ε : ℝ => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    have h : Tendsto (fun ε : ℝ => (dirichletNormalCutoff ε z - 1) * g z)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 - 1 : ℂ) * g z)) :=
      ((dirichletNormalCutoff_tendsto_one hz.2.1).sub
        tendsto_const_nhds).mul tendsto_const_nhds
    simpa only [sub_self, zero_mul, norm_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using h.norm.pow 2
  simpa only [integral_zero] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hB hlim

/-- Localization may reach the bottom edge. Its actual smooth normal
cutoff is nevertheless a genuine compact interior test, because it
vanishes on a whole neighborhood of that edge. -/
theorem dirichletNormalCutoff_testFunction {a b ε : ℝ} (hε : 0 < ε)
    (η : smoothTraceTests)
    (hη : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {v : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b)) :
    TestFunction (smoothDirichletHalfBox a b)
      (fun z => η z * dirichletNormalCutoff ε z * v z) := by
  let w : ℂ → ℂ := fun z => η z * dirichletNormalCutoff ε z * v z
  have hws : ContDiff ℝ (⊤ : ℕ∞) w := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ smoothDirichletHalfBox a b
    · exact (η.property.1.contDiffAt.mul
        (dirichletNormalCutoff_contDiff ε).contDiffAt).mul
        (hs.contDiffAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz))
    · apply (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℂ => (0 : ℂ))).contDiffAt.congr_of_eventuallyEq
      by_cases hzε : z.im < ε
      · have hn : {u : ℂ | u.im < ε} ∈ 𝓝 z :=
          (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzε
        filter_upwards [hn] with u hu
        simp only [w, dirichletNormalCutoff_eq_zero hε hu.le, mul_zero, zero_mul]
      · have hzη : z ∉ tsupport (η : ℂ → ℂ) := by
          intro hzη
          obtain ⟨hx, hy⟩ := hη hzη
          exact hz ⟨hx, hε.trans_le (le_of_not_gt hzε), hy⟩
        have hn := (isClosed_tsupport (η : ℂ → ℂ)).isOpen_compl.mem_nhds hzη
        filter_upwards [hn] with u hu
        simp only [w, image_eq_zero_of_notMem_tsupport hu, zero_mul]
  have hwc : HasCompactSupport w := η.property.2.1.mul_right.mul_right
  have hwη : tsupport w ⊆ tsupport (η : ℂ → ℂ) :=
    tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hheight : tsupport w ⊆ {z : ℂ | ε ≤ z.im} := by
    apply closure_minimal _ (isClosed_le continuous_const Complex.continuous_im)
    intro z hz
    by_contra h
    have hcut := dirichletNormalCutoff_eq_zero hε (le_of_not_ge h)
    exact hz (by simp only [w, hcut, mul_zero, zero_mul])
  refine ⟨hws, hwc, fun z hz => ?_⟩
  obtain ⟨hx, hy⟩ := hη (hwη hz)
  exact ⟨hx, hε.trans_le (hheight hz), hy⟩

theorem dirichletNormalCutoff_weight_error_memLp {a b : ℝ} (ε : ℝ) {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (fun z => (dirichletNormalCutoff ε z - 1) * g z) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  apply hg.of_le_mul (c := 2) ((((dirichletNormalCutoff_contDiff ε).continuous.sub
    continuous_const).aestronglyMeasurable).mul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖(dirichletNormalCutoff ε z - 1) * g z‖ ≤ 2 * ‖g z‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by
      rw [norm_one]
      linarith [norm_dirichletNormalCutoff_le ε z])

/-- The cutoff product rule is proved at every actual interior point. -/
theorem dirichletNormalCutoff_product_dirD {a b : ℝ} (ε : ℝ) {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (w : ℂ) :
    dirD (fun u => dirichletNormalCutoff ε u * v u) w z =
      dirichletNormalCutoff ε z * dirD v w z +
        dirD (dirichletNormalCutoff ε) w z * v z := by
  have hc := (dirichletNormalCutoff_contDiff ε).differentiable (by simp)
  have hv := (hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz)
  simp only [dirD]
  change (fderiv ℝ (dirichletNormalCutoff ε * v) z) w = _
  rw [fderiv_mul (hc z) hv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The actual normal gradient of the cutoff product converges in
L² to the actual normal gradient of the original zero-boundary H¹
function. Both terms in the product rule are controlled separately. -/
theorem dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
        dirD v Complex.I z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let A : ℝ → ℂ → ℂ := fun ε z =>
    (dirichletNormalCutoff ε z - 1) * dirD v Complex.I z
  let B : ℝ → ℂ → ℂ := fun ε z => dirichletNormalCutoffError ε v z
  have hA := dirichletNormalCutoff_weight_error_energy_tendsto_zero hg
  have hB := dirichletNormalCutoffError_physical_energy_tendsto_zero hb hv hs hz hm hg
  have hup : Tendsto (fun ε : ℝ => 2 * (∫ z, ‖A ε z‖ ^ 2 ∂μ) +
      2 * (∫ z, ‖B ε z‖ ^ 2 ∂μ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [A, B, μ, mul_zero, add_zero] using
      (tendsto_const_nhds.mul hA).add (tendsto_const_nhds.mul hB)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall fun ε => integral_nonneg fun z => sq_nonneg _
  · obtain ⟨C, _, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAm : MemLp (A ε) 2 μ := dirichletNormalCutoff_weight_error_memLp ε hg
    have hBm : MemLp (B ε) 2 μ := dirichletNormalCutoffError_memLp hε hC hm
    have hsum : (fun z => A ε z + B ε z) =ᵐ[μ]
        (fun z => dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
          dirD v Complex.I z) := by
      filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
        with z hzV
      rw [dirichletNormalCutoff_product_dirD ε hs hzV]
      dsimp only [A, B, dirichletNormalCutoffError]
      ring
    have hDm := (hAm.add hBm).ae_eq hsum
    have hAi := hAm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hBi := hBm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hDi := hDm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hbound : (fun z =>
        ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
          dirD v Complex.I z‖ ^ 2) ≤ᵐ[μ]
        (fun z => 2 * ‖A ε z‖ ^ 2 + 2 * ‖B ε z‖ ^ 2) := by
      filter_upwards [hsum] with z hzsum
      rw [← hzsum]
      have hn := norm_add_le (A ε z) (B ε z)
      have hn' := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
      nlinarith [sq_nonneg (‖A ε z‖ - ‖B ε z‖)]
    have hi := integral_mono_ae hDi ((hAi.const_mul 2).add (hBi.const_mul 2)) hbound
    simpa only [Pi.add_apply, integral_add (hAi.const_mul 2) (hBi.const_mul 2), integral_const_mul]
      using hi

theorem dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero {a b : ℝ}
    {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hg : MemLp (dirD v 1) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) 1 z -
        dirD v 1 z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (dirichletNormalCutoff_weight_error_energy_tendsto_zero hg).congr'
  exact Eventually.of_forall fun ε => by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    rw [dirichletNormalCutoff_product_dirD ε hs hz, dirD_dirichletNormalCutoff_one]
    congr 2; ring

/-- From only the original interior Riemann map and smooth physical
domain, the actual flattened remainder is approximated by its genuine
normal cutoffs in the value and both gradient energies. -/
theorem exists_riemannMapping_flattened_normalCutoff_energy_convergence {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (let v := fun z => riemannMappingDirichletRemainder F d
         (smoothDirichletGraphChart p c hc f hf.continuous z)
       Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
         ‖(dirichletNormalCutoff ε z - 1) * v z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
       ∀ i : Fin 2, Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
         ‖dirD (fun u => dirichletNormalCutoff ε u * v u) (coordDir i) z -
           dirD v (coordDir i) z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  obtain ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀,
    _, hv, hs, hz, u, hu, hgu⟩ :=
    exists_riemannMapping_flattened_zero_boundary_h1 hb hS hsc F hF hinj himage hp
  refine ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀, ?_⟩
  have hm := (Lp.memLp (h1Value (smoothDirichletHalfBox a b) u)).ae_eq hu
  have hg (i : Fin 2) :=
    (Lp.memLp (h1Gradient (smoothDirichletHalfBox a b) i u)).ae_eq (hgu i)
  refine ⟨dirichletNormalCutoff_weight_error_energy_tendsto_zero hm, ?_⟩
  intro i
  fin_cases i
  · apply dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero hs
    have h_simpa := hg 0
    simp only [coordDir, Fin.cons_zero] at h_simpa ⊢
    exact h_simpa
  · apply dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero hb₀ hv hs hz hm
    have h_simpa := hg 1
    simp only [coordDir, Fin.cons_one, Fin.cons_zero] at h_simpa ⊢
    exact h_simpa

end PolyaNeumann

end
