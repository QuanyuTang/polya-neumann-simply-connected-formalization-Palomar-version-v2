module

public import RequestProject.LocalDirichletBoundaryRegularity
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The actual divergence equation after graph flattening

The coefficients below are those of the genuine smooth graph chart,
`[[1, -f′], [-f′, 1 + f′²]]`. Their divergence is proved equal to the
physical Laplacian. The proof differentiates the actual pulled-back
physical gradient fields; it does not assume an elliptic equation or
boundary second derivatives of the constructed solution.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff ComplexConjugate

/-- Real bilinearity alone gives invariance of the trace under a
unit rotation. Symmetry of the bilinear map is not needed. -/
theorem dirichlet_bilinear_rotated_trace (T : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)
    {e : ℂ} (he : ‖e‖ = 1) :
    T e e + T (Complex.I * e) (Complex.I * e) = T 1 1 + T Complex.I Complex.I := by
  let a := e.re
  let b := e.im
  have hE : e = a • (1 : ℂ) + b • Complex.I := by
    apply Complex.ext <;> simp [a, b]
  have hIE : Complex.I * e = (-b) • (1 : ℂ) + a • Complex.I := by
    apply Complex.ext <;> simp [a, b, Complex.mul_re, Complex.mul_im]
  have hs : a ^ 2 + b ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) he
    change ‖e‖ ^ 2 = (1 : ℝ) ^ 2 at h
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    simpa only [a, b, pow_two, one_mul] using h
  have hsC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have hT : T e e = T (a • (1 : ℂ) + b • Complex.I)
      (a • (1 : ℂ) + b • Complex.I) := congrArg (fun w => T w w) hE
  have hTI : T (Complex.I * e) (Complex.I * e) =
      T ((-b) • (1 : ℂ) + a • Complex.I) ((-b) • (1 : ℂ) + a • Complex.I) :=
    congrArg (fun w => T w w) hIE
  rw [hT, hTI]
  simp only [map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  simp only [Complex.real_smul, Complex.ofReal_neg]
  calc
    _ = ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (T 1 1 + T Complex.I Complex.I) := by ring
    _ = _ := by rw [hsC, one_mul]

theorem dirichlet_rotated_lap {v : ℂ → ℂ} {z e : ℂ}
    (hv : ContDiffAt ℝ 2 v z) (he : ‖e‖ = 1) :
    dirD (dirD v e) e z + dirD (dirD v (Complex.I * e)) (Complex.I * e) z = lap v z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD (w : ℂ) : dirD (dirD v w) w z = fderiv ℝ (fderiv ℝ v) z w w := by
    change fderiv ℝ (fun u => fderiv ℝ v u w) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp only [fderiv_const_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply, map_zero, zero_add]
  rw [hD, hD, lap, hD, hD]
  exact dirichlet_bilinear_rotated_trace _ he

/-- The actual real graph slope, regarded as a complex scalar. -/
def dirichletGraphSlope (f : ℝ → ℝ) (z : ℂ) : ℂ := ((deriv f z.re : ℝ) : ℂ)

theorem dirichletGraphSlope_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletGraphSlope f) :=
  Complex.ofRealCLM.contDiff.comp
    ((contDiff_infty_iff_deriv.mp hf).2.comp Complex.reCLM.contDiff)

@[simp] theorem dirD_dirichletGraphSlope_I {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dirD (dirichletGraphSlope f) Complex.I z = 0 := by
  have hd := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    (hd.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z Complex.I = 0
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.reCLM_apply, Complex.I_re, smul_zero, map_zero]

/-- The flux of the actual graph coefficient matrix. -/
def dirichletFlattenedFlux (f : ℝ → ℝ) (u : ℂ → ℂ) (i : Fin 2) (z : ℂ) : ℂ :=
  ![dirD u 1 z - dirichletGraphSlope f z * dirD u Complex.I z,
    -dirichletGraphSlope f z * dirD u 1 z +
      (1 + dirichletGraphSlope f z ^ 2) * dirD u Complex.I z] i

def dirichletFlattenedDivergence (f : ℝ → ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirD (dirichletFlattenedFlux f u 0) 1 z +
    dirD (dirichletFlattenedFlux f u 1) Complex.I z

theorem dirichletFlattenedFlux_pullback (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {v : ℂ → ℂ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirichletFlattenedFlux f (v ∘ Ψ) 0 z = dirD v (1 / c) (Ψ z)) ∧
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirichletFlattenedFlux f (v ∘ Ψ) 1 z =
       dirD v (Complex.I / c) (Ψ z) - dirichletGraphSlope f z * dirD v (1 / c) (Ψ z)) := by
  have h := smoothDirichletGraphChart_pullback_gradient p c hc hf hv
  constructor
  · simpa only [dirichletFlattenedFlux, Matrix.cons_val_zero, dirichletGraphSlope, dirD]
      using h.1
  · let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
    let u := v ∘ Ψ
    let d := dirichletGraphSlope f z
    have hX : dirD u 1 z - d * dirD u Complex.I z = dirD v (1 / c) (Ψ z) := h.1
    have hY : dirD u Complex.I z = dirD v (Complex.I / c) (Ψ z) := h.2
    change -d * dirD u 1 z + (1 + d ^ 2) * dirD u Complex.I z = _
    calc
      _ = dirD u Complex.I z - d * (dirD u 1 z - d * dirD u Complex.I z) := by ring
      _ = _ := by rw [hX, hY]

/-- This is a pointwise identity for the actual physical function
and the actual graph chart. In particular, the resulting divergence
equation is not an additional assumption about the flattened solution. -/
theorem dirichletFlattenedDivergence_pullback {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {v : ℂ → ℂ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω) {z : ℂ}
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω) :
    dirichletFlattenedDivergence f
      (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) z =
      lap v (smoothDirichletGraphChart p c hc f hf.continuous z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := v ∘ Ψ
  let g₀ := dirD v (1 / c)
  let g₁ := dirD v (Complex.I / c)
  have hvc := hv.contDiffAt (hΩ.mem_nhds hz)
  have hv₂ : ContDiffAt ℝ 2 v (Ψ z) := hvc.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdg (w : ℂ) : DifferentiableAt ℝ (dirD v w) (Ψ z) :=
    ((hvc.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hdΨ := (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hn : ∀ᶠ w in 𝓝 z, Ψ w ∈ Ω := Ψ.continuous.continuousAt.eventually (hΩ.mem_nhds hz)
  have h₀ : dirichletFlattenedFlux f u 0 =ᶠ[𝓝 z] g₀ ∘ Ψ := by
    filter_upwards [hn] with w hw
    exact (dirichletFlattenedFlux_pullback p c hc hf
      ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hw))).1
  have h₁ : dirichletFlattenedFlux f u 1 =ᶠ[𝓝 z]
      (fun w => g₁ (Ψ w) - dirichletGraphSlope f w * g₀ (Ψ w)) := by
    filter_upwards [hn] with w hw
    exact (dirichletFlattenedFlux_pullback p c hc hf
      ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hw))).2
  have hcompI (g : ℂ → ℂ) (hg : DifferentiableAt ℝ g (Ψ z)) :
      dirD (g ∘ Ψ) Complex.I z = dirD g (Complex.I / c) (Ψ z) :=
    (smoothDirichletGraphChart_pullback_gradient p c hc hf hg).2
  have hcompOne (g : ℂ → ℂ) (hg : DifferentiableAt ℝ g (Ψ z)) :
      dirD (g ∘ Ψ) 1 z = dirD g (1 / c) (Ψ z) +
        dirichletGraphSlope f z * dirD g (Complex.I / c) (Ψ z) := by
    have h := (smoothDirichletGraphChart_pullback_gradient p c hc hf hg).1
    have he := sub_eq_iff_eq_add.mp h
    rw [hcompI g hg] at he
    exact he
  have hD₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
      dirD g₀ (1 / c) (Ψ z) +
        dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) := by
    change fderiv ℝ (dirichletFlattenedFlux f u 0) z 1 = _
    rw [h₀.fderiv_eq (𝕜 := ℝ)]
    exact hcompOne g₀ (hdg _)
  have hD₁ : dirD (dirichletFlattenedFlux f u 1) Complex.I z =
      dirD g₁ (Complex.I / c) (Ψ z) -
        dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) := by
    have hgs := (dirichletGraphSlope_contDiff hf).differentiable (by simp)
    have hd₀ : DifferentiableAt ℝ (g₀ ∘ Ψ) z := (hdg (1 / c)).comp z hdΨ
    have hd₁ : DifferentiableAt ℝ (g₁ ∘ Ψ) z := (hdg (Complex.I / c)).comp z hdΨ
    have hdm : DifferentiableAt ℝ (dirichletGraphSlope f * (g₀ ∘ Ψ)) z :=
      (hgs z).mul hd₀
    change fderiv ℝ (dirichletFlattenedFlux f u 1) z Complex.I = _
    rw [h₁.fderiv_eq (𝕜 := ℝ)]
    change fderiv ℝ ((g₁ ∘ Ψ) - (dirichletGraphSlope f * (g₀ ∘ Ψ))) z Complex.I = _
    rw [fderiv_sub hd₁ hdm, fderiv_mul (hgs z) hd₀]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    change dirD (g₁ ∘ Ψ) Complex.I z -
      (dirichletGraphSlope f z * dirD (g₀ ∘ Ψ) Complex.I z +
        g₀ (Ψ z) * dirD (dirichletGraphSlope f) Complex.I z) = _
    rw [hcompI g₁ (hdg _), hcompI g₀ (hdg _), dirD_dirichletGraphSlope_I hf]
    ring
  have he : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc₁, inv_one]
  calc
    _ = dirD g₀ (1 / c) (Ψ z) + dirD g₁ (Complex.I / c) (Ψ z) := by
      rw [dirichletFlattenedDivergence, hD₀, hD₁]
      ring
    _ = lap v (Ψ z) := by
      simpa only [g₀, g₁, one_div, div_eq_mul_inv, one_mul] using dirichlet_rotated_lap hv₂ he

/-- Total directional derivatives of a function smooth on an open
set are again smooth on that same open set. -/
theorem dirichlet_contDiffOn_dirD {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (w : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirD g w) U := by
  intro z hz
  exact (((hg.contDiffAt (hU.mem_nhds hz)).fderiv_right
    (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const).contDiffWithinAt

/-- Local smoothness plus a genuine compact test suffices for this
integrability statement. No global second-derivative energy is used. -/
theorem dirichlet_local_smooth_mul_test_integrable {U : Set ℂ} (hU : IsOpen U)
    {g φ : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hφ : TestFunction U φ) :
    IntegrableOn (fun z => g z * φ z) U := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  have heq : (fun z => g z * φ z) = (fun z => G z * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [(hGg z hz).self_of_nhds]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  rw [heq]
  exact (hG.memLp' 2).integrable_mul (hφ.memLp' 2)

theorem dirichlet_local_smooth_field_test_eq_neg_dirD {U : Set ℂ} (hU : IsOpen U)
    {g φ : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hφ : TestFunction U φ)
    (i : Fin 2) :
    (∫ z in U, g z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD g (coordDir i) z * φ z) := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  have hu := hG.memLp' 2 (μ := volume.restrict U)
  have hgrad (j : Fin 2) := (hG.dirD (coordDir j)).memLp' 2 (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth hG.1 hu hgrad φ hφ i
  have hl : (fun z => (hu.toLp G : L2 U) z * dirD φ (coordDir i) z) =ᵐ[volume.restrict U]
      (fun z => g z * dirD φ (coordDir i) z) := by
    filter_upwards [hu.coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · rw [(hGg z hz).self_of_nhds]
    · simp only [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz,
        ContinuousLinearMap.zero_apply, mul_zero]
  have hr : (fun z => ((hgrad i).toLp _ : L2 U) z * φ z) =ᵐ[volume.restrict U]
      (fun z => dirD g (coordDir i) z * φ z) := by
    filter_upwards [(hgrad i).coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · rw [show dirD G (coordDir i) z = dirD g (coordDir i) z from
        congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i))
          ((hGg z hz).fderiv_eq (𝕜 := ℝ))]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  change (∫ z in U, (hu.toLp G : L2 U) z * dirD φ (coordDir i) z) =
    -(∫ z in U, ((hgrad i).toLp _ : L2 U) z * φ z) at hw
  rw [integral_congr_ae hl, integral_congr_ae hr] at hw
  exact hw

theorem dirichletFlattenedFlux_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletFlattenedFlux f u i) U := by
  have hx := dirichlet_contDiffOn_dirD hU hu 1
  have hy := dirichlet_contDiffOn_dirD hU hu Complex.I
  have hd := (dirichletGraphSlope_contDiff hf).contDiffOn (s := U)
  fin_cases i
  · exact hx.sub (hd.mul hy)
  · exact (hd.neg.mul hx).add ((contDiffOn_const.add (hd.pow 2)).mul hy)

theorem dirichletFlattenedFlux_test_eq_neg_divergence {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u φ : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (hφ : TestFunction U φ) :
    (∫ z in U, ∑ i : Fin 2,
      dirichletFlattenedFlux f u i z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirichletFlattenedDivergence f u z * φ z) := by
  have hflux (i : Fin 2) := dirichletFlattenedFlux_contDiffOn hU hf hu i
  have hFi (i : Fin 2) := dirichlet_local_smooth_mul_test_integrable hU
    (hflux i) (hφ.dirD (coordDir i))
  have hDi (i : Fin 2) := dirichlet_local_smooth_mul_test_integrable hU
    (dirichlet_contDiffOn_dirD hU (hflux i) (coordDir i)) hφ
  calc
    _ = ∑ i : Fin 2, ∫ z in U,
        dirichletFlattenedFlux f u i z * dirD φ (coordDir i) z :=
      integral_finset_sum _ (fun i _ => hFi i)
    _ = ∑ i : Fin 2, -(∫ z in U,
        dirD (dirichletFlattenedFlux f u i) (coordDir i) z * φ z) := by
      apply Finset.sum_congr rfl
      intro i _
      exact dirichlet_local_smooth_field_test_eq_neg_dirD hU (hflux i) hφ i
    _ = -((∫ z in U, dirD (dirichletFlattenedFlux f u 0) 1 z * φ z) +
        ∫ z in U, dirD (dirichletFlattenedFlux f u 1) Complex.I z * φ z) := by
      rw [Fin.sum_univ_two]
      simp only [coordDir, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    _ = _ := by
      have hD₀ : IntegrableOn
          (fun z => dirD (dirichletFlattenedFlux f u 0) 1 z * φ z) U := by
        simpa only [coordDir, Matrix.cons_val_zero] using hDi 0
      have hD₁ : IntegrableOn
          (fun z => dirD (dirichletFlattenedFlux f u 1) Complex.I z * φ z) U := by
        simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hDi 1
      simp only [dirichletFlattenedDivergence, add_mul, integral_add hD₀ hD₁]

/-- The actual compact-test graph equation, obtained from the physical
Laplacian and the real unit chart, with no assumed weak PDE. -/
theorem dirichletFlattenedFlux_pullback_test_eq_neg_lap {U Ω : Set ℂ}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous) U Ω)
    {v φ : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω) (hφ : TestFunction U φ) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     ∫ z in U, ∑ i : Fin 2,
       dirichletFlattenedFlux f (v ∘ Ψ) i z * dirD φ (coordDir i) z) =
      -(∫ z in U, lap v (smoothDirichletGraphChart p c hc f hf.continuous z) * φ z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ Ψ) U :=
    hv.comp (smoothDirichletGraphChart_contDiff p c hc hf).contDiffOn hmap
  rw [dirichletFlattenedFlux_test_eq_neg_divergence hU hf hu hφ]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  rw [dirichletFlattenedDivergence_pullback hΩ p c hc hc₁ hf hv (hmap hz)]

theorem riemannMappingDirichletRemainder_contDiffOn {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    (d : smoothTraceTests) :
    ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingDirichletRemainder F d) Ω :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)).sub
      d.property.1.contDiffOn

/-- Every actual smooth datum gives this physical Laplacian identity;
the selected datum is needed only for the separately proved zero
boundary values. -/
theorem riemannMappingDirichletRemainder_lap {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    (d : smoothTraceTests) {z : ℂ} (hz : z ∈ Ω) :
    lap (riemannMappingDirichletRemainder F d) z = -lap (d : ℂ → ℂ) z := by
  have hharm := (riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage).comp_CLM
    Complex.ofRealCLM
  have hh := (hharm z hz).1
  have hd : ContDiffAt ℝ 2 (d : ℂ → ℂ) z :=
    d.property.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  exact (lap_sub_of_contDiffAt hh hd).trans (by
    rw [lap_eq_euclidean_laplacian hh, (hharm z hz).2.self_of_nhds, Pi.zero_apply, zero_sub])

/-- The constructed actual flattened H¹ remainder satisfies the
true divergence equation with the pulled-back genuine smooth forcing.
All domain, map, zero-boundary and H¹ data come from the original
interior Riemann map and the actual smooth physical domain. -/
theorem exists_riemannMapping_flattened_zero_boundary_weak_equation {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       MapsTo Ψ (smoothDirichletHalfBox a b) Ω ∧
       ContinuousOn u (smoothDirichletClosedHalfBox a b) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b) ∧
       (∀ x : ℝ, |x| < a → u (x : ℂ) = 0) ∧
       (∃ v : NeumannH1 (smoothDirichletHalfBox a b),
         (h1Value (smoothDirichletHalfBox a b) v : ℂ → ℂ) =ᵐ[volume.restrict
           (smoothDirichletHalfBox a b)] u ∧
         ∀ i : Fin 2, (h1Gradient (smoothDirichletHalfBox a b) i v : ℂ → ℂ) =ᵐ[volume.restrict
           (smoothDirichletHalfBox a b)] dirD u (coordDir i)) ∧
       ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
         (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
           dirichletFlattenedFlux f u i z * dirD φ (coordDir i) z) =
         ∫ z in smoothDirichletHalfBox a b, lap (d : ℂ → ℂ) (Ψ z) * φ z) := by
  obtain ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀,
    hmap, hu, hs, hz, v, hv, hgv⟩ :=
    exists_riemannMapping_flattened_zero_boundary_h1 hb hS hsc F hF hinj himage hp
  refine ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀,
    hmap, hu, hs, hz, ⟨v, hv, hgv⟩, ?_⟩
  intro φ hφ
  rw [dirichletFlattenedFlux_pullback_test_eq_neg_lap
    (isOpen_smoothDirichletHalfBox a b) hS.1.1 p c hc hc₁ hf hmap
    (riemannMappingDirichletRemainder_contDiffOn hb hS hsc F hF hinj himage d) hφ]
  have heq : (fun z => lap (riemannMappingDirichletRemainder F d)
      (smoothDirichletGraphChart p c hc f hf.continuous z) * φ z) =ᵐ[volume.restrict
        (smoothDirichletHalfBox a b)]
      (fun z => -(lap (d : ℂ → ℂ) (smoothDirichletGraphChart p c hc f hf.continuous z) * φ z)) := by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hzV
    rw [riemannMappingDirichletRemainder_lap hb hS hsc F hF hinj himage d (hmap hzV), neg_mul]
  rw [integral_congr_ae heq, integral_neg, neg_neg]

/-! ### Actual zero-boundary test approximation -/

theorem dirichlet_bounded_mul_memLp {μ : Measure ℂ} {a g : ℂ → ℂ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hbound : ∀ z, ‖a z‖ ≤ C)
    (hg : MemLp g 2 μ) : MemLp (fun z => a z * g z) 2 μ := by
  apply hg.of_le_mul (c := C) (ha.mul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖a z * g z‖ ≤ C * ‖g z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _)

theorem dirichlet_localized_memLp {μ : Measure ℂ} (η : smoothTraceTests) {g : ℂ → ℂ}
    (hg : MemLp g 2 μ) : MemLp (fun z => η z * g z) 2 μ := by
  obtain ⟨C, hC⟩ := η.property.2.1.exists_bound_of_continuous η.property.1.continuous
  exact dirichlet_bounded_mul_memLp η.property.1.continuous.aestronglyMeasurable hC hg

theorem dirichlet_localized_dirD {U : Set ℂ} (hU : IsOpen U) (η : smoothTraceTests)
    {g : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) {z : ℂ} (hz : z ∈ U) (w : ℂ) :
    dirD (fun u => η u * g u) w z = η z * dirD g w z + dirD (η : ℂ → ℂ) w z * g z := by
  have hη := η.property.1.differentiable (by simp)
  have hgz := (hg.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  change fderiv ℝ ((η : ℂ → ℂ) * g) z w = _
  rw [fderiv_mul (hη z) hgz]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, dirD]
  ring

theorem dirichlet_localized_gradient_memLp {U : Set ℂ} (hU : IsOpen U)
    (η : smoothTraceTests) {g : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hm : MemLp g 2 (volume.restrict U)) {i : Fin 2}
    (hg : MemLp (dirD g (coordDir i)) 2 (volume.restrict U)) :
    MemLp (dirD (fun z => η z * g z) (coordDir i)) 2 (volume.restrict U) := by
  let dη : smoothTraceTests := ⟨dirD (η : ℂ → ℂ) (coordDir i), η.property.dirD (coordDir i)⟩
  have hsum := (dirichlet_localized_memLp η hg).add (dirichlet_localized_memLp dη hm)
  apply hsum.ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  exact (dirichlet_localized_dirD hU η hs hz (coordDir i)).symm

/-- These are genuine compact interior tests, with convergence in
all three actual H¹ energies. The localization can touch the flat
boundary; its sides and top remain inside the coordinate rectangle. -/
theorem dirichlet_localized_zero_boundary_test_approximation {a b : ℝ}
    (hb : 0 < b) (η : smoothTraceTests)
    (hη : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {g : ℂ → ℂ} (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g (x : ℂ) = 0)
    (hm : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD g (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    (let v := fun z => η z * g z
     (∀ ε : ℝ, 0 < ε → TestFunction (smoothDirichletHalfBox a b)
       (fun z => dirichletNormalCutoff ε z * v z)) ∧
     Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
       ‖dirichletNormalCutoff ε z * v z - v z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
     ∀ i : Fin 2, Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
       ‖dirD (fun u => dirichletNormalCutoff ε u * v u) (coordDir i) z -
         dirD v (coordDir i) z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  let v : ℂ → ℂ := fun z => η z * g z
  have hv : ContinuousOn v (smoothDirichletClosedHalfBox a b) :=
    η.property.1.continuous.continuousOn.mul hc
  have hvS : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b) :=
    η.property.1.contDiffOn.mul hs
  have hvz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0 := by
    intro x hx
    simp only [v, hz x hx, mul_zero]
  have hvm := dirichlet_localized_memLp η hm
  have hvg (i : Fin 2) := dirichlet_localized_gradient_memLp
    (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    have htest := dirichletNormalCutoff_testFunction hε η hη hs
    have heq : (fun z => dirichletNormalCutoff ε z * v z) =
        (fun z => η z * dirichletNormalCutoff ε z * g z) := by
      funext z
      dsimp only [v]
      ring
    rw [heq]
    exact htest
  · have h := dirichletNormalCutoff_weight_error_energy_tendsto_zero hvm
    apply h.congr'
    exact Eventually.of_forall fun ε => by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change ‖(dirichletNormalCutoff ε z - 1) * v z‖ ^ 2 =
          ‖dirichletNormalCutoff ε z * v z - v z‖ ^ 2
        have heq : (dirichletNormalCutoff ε z - 1) * v z =
            dirichletNormalCutoff ε z * v z - v z := by ring
        rw [heq]
  · intro i
    fin_cases i
    · apply dirichletNormalCutoff_tangential_gradient_error_energy_tendsto_zero hvS
      simpa only [coordDir, Matrix.cons_val_zero] using hvg 0
    · apply dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero hb hv hvS hvz hvm
      simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hvg 1

theorem dirichlet_eLpNorm_toReal_eq_sqrt_energy {μ : Measure ℂ} {g : ℂ → ℂ}
    (hg : MemLp g 2 μ) :
    (eLpNorm g 2 μ).toReal = Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂μ) := by
  rw [← Lp.norm_toLp g hg, ← norm_sq_toLp_eq_integral hg,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Actual L² energy convergence gives convergence of pairing
against any fixed actual L² function. This is the Cauchy–Schwarz
step needed to pass genuine interior tests to the boundary. -/
theorem dirichlet_pairing_tendsto_zero_of_energy {μ : Measure ℂ}
    {g : ℂ → ℂ} (hg : MemLp g 2 μ) {e : ℝ → ℂ → ℂ}
    (he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (e ε) 2 μ)
    (hE : Tendsto (fun ε : ℝ => ∫ z, ‖e ε z‖ ^ 2 ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ∫ z, g z * e ε z ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hE
  have hup : Tendsto (fun ε : ℝ => (eLpNorm g 2 μ).toReal *
      Real.sqrt (∫ z, ‖e ε z‖ ^ 2 ∂μ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_apply] using tendsto_const_nhds.mul hsqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall fun ε => norm_nonneg _
  · filter_upwards [he] with ε hε
    simpa only [dirichlet_eLpNorm_toReal_eq_sqrt_energy hε] using
      norm_integral_mul_le_eLpNorm hg hε

theorem dirichlet_pairing_tendsto_of_energy_approximation {μ : Measure ℂ}
    {g k : ℂ → ℂ} (hg : MemLp g 2 μ) (hk : MemLp k 2 μ) {kε : ℝ → ℂ → ℂ}
    (hmem : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (kε ε) 2 μ)
    (hE : Tendsto (fun ε : ℝ => ∫ z, ‖kε ε z - k z‖ ^ 2 ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ∫ z, g z * kε ε z ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, g z * k z ∂μ)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (fun z => kε ε z - k z) 2 μ :=
    hmem.mono fun _ h => h.sub hk
  have hp := dirichlet_pairing_tendsto_zero_of_energy hg he hE
  have hplus := hp.add (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => ∫ z, g z * k z ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, g z * k z ∂μ)))
  have hplus' : Tendsto (fun ε : ℝ =>
      (∫ z, g z * (kε ε z - k z) ∂μ) + ∫ z, g z * k z ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, g z * k z ∂μ)) := by
    simpa only [zero_add] using hplus
  apply hplus'.congr'
  filter_upwards [hmem] with ε hε
  simp_rw [mul_sub]
  have hiε : Integrable (fun z => g z * kε ε z) μ := hg.integrable_mul hε
  have hik : Integrable (fun z => g z * k z) μ := hg.integrable_mul hk
  rw [integral_sub hiε hik]
  ring

/-- The passage from actual compact interior tests to a localized
zero-boundary H¹ test. Its convergence and integrability are proved
above, and no density or boundary smoothness assumption is made. -/
theorem dirichlet_weak_equation_localized_zero_boundary_test {a b : ℝ}
    (hb : 0 < b) (η : smoothTraceTests)
    (hη : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {g : ℂ → ℂ} (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g (x : ℂ) = 0)
    (hm : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD g (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    {F : Fin 2 → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ i : Fin 2, MemLp (F i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hweak : ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2, F i z * dirD φ (coordDir i) z) =
        ∫ z in smoothDirichletHalfBox a b, G z * φ z) :
    (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
      F i z * dirD (fun u => η u * g u) (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b, G z * (η z * g z) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let v : ℂ → ℂ := fun z => η z * g z
  let vε : ℝ → ℂ → ℂ := fun ε z => dirichletNormalCutoff ε z * v z
  obtain ⟨htest, hvalue, hgradient⟩ :=
    dirichlet_localized_zero_boundary_test_approximation hb η hη hc hs hz hm hg
  have hvm : MemLp v 2 μ := dirichlet_localized_memLp η hm
  have hvg (i : Fin 2) : MemLp (dirD v (coordDir i)) 2 μ :=
    dirichlet_localized_gradient_memLp (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  have hεm : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (vε ε) 2 μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (htest ε hε).memLp' 2
  have hεg (i : Fin 2) : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (dirD (vε ε) (coordDir i)) 2 μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((htest ε hε).dirD (coordDir i)).memLp' 2
  have hleft (i : Fin 2) : Tendsto
      (fun ε : ℝ => ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, F i z * dirD v (coordDir i) z ∂μ)) :=
    dirichlet_pairing_tendsto_of_energy_approximation (hF i) (hvg i) (hεg i) (hgradient i)
  have hright : Tendsto (fun ε : ℝ => ∫ z, G z * vε ε z ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, G z * v z ∂μ)) :=
    dirichlet_pairing_tendsto_of_energy_approximation hG hvm hεm hvalue
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => hleft i)
  have heq : (fun ε : ℝ => ∑ i : Fin 2, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ∫ z, G z * vε ε z ∂μ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hisum : (∫ z, ∑ i : Fin 2, F i z * dirD (vε ε) (coordDir i) z ∂μ) =
        ∑ i : Fin 2, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ := by
      apply integral_finset_sum
      intro i _
      exact (hF i).integrable_mul (((htest ε hε).dirD (coordDir i)).memLp' 2)
    rw [← hisum]
    exact hweak _ (htest ε hε)
  have hlim : (∑ i : Fin 2, ∫ z, F i z * dirD v (coordDir i) z ∂μ) =
      ∫ z, G z * v z ∂μ := tendsto_nhds_unique hsum (hright.congr' heq.symm)
  change (∫ z, ∑ i : Fin 2, F i z * dirD v (coordDir i) z ∂μ) =
    ∫ z, G z * v z ∂μ
  have hisum : (∫ z, ∑ i : Fin 2, F i z * dirD v (coordDir i) z ∂μ) =
      ∑ i : Fin 2, ∫ z, F i z * dirD v (coordDir i) z ∂μ := by
    apply integral_finset_sum
    intro i _
    exact (hF i).integrable_mul (hvg i)
  rw [hisum]
  exact hlim

/-- The true graph coefficients are bounded by the actual graph
Lipschitz constant, so the flux of an actual H¹ function is in L². -/
theorem dirichletFlattenedFlux_memLp {a b : ℝ} {f : ℝ → ℝ} {K : NNReal}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hLip : LipschitzWith K f) {u : ℂ → ℂ}
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b))) (i : Fin 2) :
    MemLp (dirichletFlattenedFlux f u i) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  have hdx : MemLp (dirD u 1) 2 μ := by simpa only [coordDir, Matrix.cons_val_zero] using hg 0
  have hdy : MemLp (dirD u Complex.I) 2 μ := by
    simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1
  have hc := (dirichletGraphSlope_contDiff hf).continuous
  have hbound (z : ℂ) : ‖dirichletGraphSlope f z‖ ≤ (K : ℝ) := by
    simpa only [dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip (x₀ := z.re)
  have hdsY := dirichlet_bounded_mul_memLp hc.aestronglyMeasurable hbound hdy
  have hndsX := dirichlet_bounded_mul_memLp hc.neg.aestronglyMeasurable
    (fun z => by rw [Pi.neg_apply, norm_neg]; exact hbound z) hdx
  have hcoef (z : ℂ) : ‖(1 : ℂ) + dirichletGraphSlope f z ^ 2‖ ≤ 1 + (K : ℝ) ^ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖dirichletGraphSlope f z ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖dirichletGraphSlope f z‖ ^ 2 := by rw [norm_one, norm_pow]
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hbound z) 2)
  have hcoefY := dirichlet_bounded_mul_memLp
    (continuous_const.add (hc.pow 2)).aestronglyMeasurable hcoef hdy
  fin_cases i
  · exact hdx.sub hdsY
  · exact hndsX.add hcoefY

theorem dirichlet_halfBox_isBounded {a b : ℝ} :
    Bornology.IsBounded (smoothDirichletHalfBox a b) := by
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := a + b)).subset
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ a + b := add_le_add hz.1.le (by rw [abs_of_pos hz.2.1]; exact hz.2.2.le)

/-- The actual pulled-back forcing is in L² because the genuine
smooth compact datum has a bounded Laplacian and the half box has
finite ordinary area. No regularity of the solution is assumed. -/
theorem dirichlet_lapDatum_pullback_memLp {a b : ℝ}
    (d : smoothTraceTests) {Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) :
    MemLp (fun z => lap (d : ℂ → ℂ) (Ψ z)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hd := d.property.lap
  obtain ⟨C, hC⟩ := hd.2.1.exists_bound_of_continuous hd.1.continuous
  letI : IsFiniteMeasure (volume.restrict (smoothDirichletHalfBox a b)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (dirichlet_halfBox_isBounded (a := a) (b := b)).measure_lt_top⟩
  apply MemLp.of_bound (hd.1.continuous.comp hΨ).aestronglyMeasurable C
  exact Eventually.of_forall fun z => hC (Ψ z)

/-- In the constructed actual coordinate chart, the weak equation
already holds for localized tests that reach the flat boundary. The
test is built from the actual zero-boundary remainder; the normal
cutoff passage supplies the boundary step. -/
theorem exists_riemannMapping_flattened_localized_boundary_equation {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       ∀ η : smoothTraceTests,
         tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} →
         (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
           dirichletFlattenedFlux f u i z * dirD (fun w => η w * u w) (coordDir i) z) =
         ∫ z in smoothDirichletHalfBox a b, lap (d : ℂ → ℂ) (Ψ z) * (η z * u z)) := by
  obtain ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀,
    _, hu, hs, hz, hv, hweak⟩ :=
    exists_riemannMapping_flattened_zero_boundary_weak_equation hb hS hsc F hF hinj himage hp
  obtain ⟨v, hv, hgv⟩ := hv
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  have hvm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox a b)) :=
    (Lp.memLp (h1Value (smoothDirichletHalfBox a b) v)).ae_eq hv
  have hvg (i : Fin 2) : MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) :=
    (Lp.memLp (h1Gradient (smoothDirichletHalfBox a b) i v)).ae_eq (hgv i)
  have hflux (i : Fin 2) := dirichletFlattenedFlux_memLp hf hLip hvg i
  have hforce := dirichlet_lapDatum_pullback_memLp (a := a) (b := b) d Ψ.continuous
  refine ⟨d, c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀, ?_⟩
  dsimp only
  intro η hη
  exact dirichlet_weak_equation_localized_zero_boundary_test hb₀ η hη
    hu hs hz hvm hvg hflux hforce hweak

/-- The actual tangential difference quotient, with ordinary real
translation and the physical complex scalar normalization. -/
def dirichletTangentialDifference (h : ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  (u (z + (h : ℂ)) - u z) / (h : ℂ)

theorem dirichlet_continuousOn_memLp_Ioc {a b : ℝ} {v : ℝ → ℂ}
    (hv : ContinuousOn v (Icc a b)) :
    MemLp v 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((hv.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mpr
  exact (hv.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The difference quotient of an actual differentiable interval
function has an L² bound independent of the step. This is an
ordinary FTC/Cauchy--Schwarz/Fubini estimate, with no derivative
assumed at a physical boundary. -/
theorem dirichlet_interval_difference_energy_le {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) {v dv : ℝ → ℂ}
    (hv : ContinuousOn v (Icc (-a) (a + h)))
    (hdv : ContinuousOn dv (Icc (-a) (a + h)))
    (hd : ∀ x ∈ Icc (-a) (a + h), HasDerivAt v (dv x) x) :
    (∫ x in (-a)..a, ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2) ≤
      ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2 := by
  have haa : -a ≤ a := by linarith
  have haah : -a ≤ a + h := by linarith
  have hmap (x : ℝ) (hx : x ∈ Icc (-a) a) :
      MapsTo (fun s : ℝ => x + s) (Icc 0 h) (Icc (-a) (a + h)) := by
    intro s hs
    constructor <;> linarith [hx.1, hx.2, hs.1, hs.2]
  have hpoint (x : ℝ) (hx : x ∈ Icc (-a) a) :
      ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2 ≤
        h⁻¹ * ∫ s in (0 : ℝ)..h, ‖dv (x + s)‖ ^ 2 := by
    have hvs : ContinuousOn (fun s : ℝ => v (x + s) - v x) (Icc 0 h) :=
      (hv.comp (continuous_const.add continuous_id).continuousOn (hmap x hx)).sub
        continuousOn_const
    have hdvs : ContinuousOn (fun s : ℝ => dv (x + s)) (Icc 0 h) :=
      hdv.comp (continuous_const.add continuous_id).continuousOn (hmap x hx)
    have hds (s : ℝ) (hs : s ∈ Ioo 0 h) :
        HasDerivAt (fun t : ℝ => v (x + t) - v x) (dv (x + s)) s := by
      simpa only [one_smul, Function.comp_apply] using
        ((hd (x + s) (hmap x hx (Ioo_subset_Icc_self hs))).scomp s
          ((hasDerivAt_id s).const_add x)).sub_const (v x)
    have hp := dirichlet_zero_endpoint_norm_sq_le hvs
      (by simp) hds (dirichlet_continuousOn_memLp_Ioc hdvs)
      (show h ∈ Ioc (0 : ℝ) h from ⟨hh, le_rfl⟩)
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_pow] at hp ⊢
    apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
    calc
      ‖v (x + h) - v x‖ ^ 2 ≤ h * ∫ s in (0 : ℝ)..h, ‖dv (x + s)‖ ^ 2 := hp
      _ = (h⁻¹ * ∫ s in (0 : ℝ)..h, ‖dv (x + s)‖ ^ 2) * h ^ 2 := by
        field_simp [hh.ne']
  let E : ℝ × ℝ → ℝ := fun p => ‖dv (p.1 + p.2)‖ ^ 2
  have hcE : ContinuousOn E (Icc (-a) a ×ˢ Icc (0 : ℝ) h) :=
    (hdv.norm.pow 2).comp (continuous_fst.add continuous_snd).continuousOn
      (fun p hp => hmap p.1 hp.1 hp.2)
  have hiE : Integrable E
      ((volume.restrict (Ioc (-a) a)).prod (volume.restrict (Ioc (0 : ℝ) h))) := by
    rw [Measure.prod_restrict]
    exact (hcE.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hq : ContinuousOn (fun x : ℝ => ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2)
      (Icc (-a) a) := by
    have hx : MapsTo (fun x : ℝ => x + h) (Icc (-a) a) (Icc (-a) (a + h)) := by
      intro x hx
      constructor <;> linarith [hx.1, hx.2]
    have hid : Icc (-a) a ⊆ Icc (-a) (a + h) :=
      Icc_subset_Icc le_rfl (by linarith)
    exact (((hv.comp (continuous_id.add continuous_const).continuousOn hx).sub
      (hv.mono hid)).div_const (h : ℂ)).norm.pow 2
  have hH : Integrable (fun x : ℝ => ∫ s in (0 : ℝ)..h, E (x, s))
      (volume.restrict (Ioc (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hh.le] using hiE.integral_prod_left
  have hfirst :
      (∫ x in (-a)..a, ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2) ≤
      h⁻¹ * ∫ x in (-a)..a, ∫ s in (0 : ℝ)..h, E (x, s) := by
    rw [intervalIntegral.integral_of_le haa,
      intervalIntegral.integral_of_le haa, ← integral_const_mul]
    apply integral_mono_ae (hq.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hH.const_mul h⁻¹)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hpoint x (Ioc_subset_Icc_self hx)
  have hswap : (∫ x in (-a)..a, ∫ s in (0 : ℝ)..h, E (x, s)) =
      ∫ s in (0 : ℝ)..h, ∫ x in (-a)..a, E (x, s) := by
    simp only [intervalIntegral.integral_of_le haa, intervalIntegral.integral_of_le hh.le]
    exact integral_integral_swap hiE
  have hwide : IntervalIntegrable (fun x : ℝ => ‖dv x‖ ^ 2) volume (-a) (a + h) :=
    (hdv.norm.pow 2).intervalIntegrable_of_Icc haah
  have hlast : (∫ s in (0 : ℝ)..h, ∫ x in (-a)..a, E (x, s)) ≤
      h * ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2 := by
    have hi : IntervalIntegrable (fun s : ℝ => ∫ x in (-a)..a, E (x, s))
        volume 0 h := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
      simpa only [IntegrableOn, intervalIntegral.integral_of_le haa] using hiE.integral_prod_right
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo hh.le hi
      (intervalIntegrable_const (c := ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2))
      (fun s hs => by
        change (∫ x in (-a)..a, ‖dv (x + s)‖ ^ 2) ≤ _
        rw [intervalIntegral.integral_comp_add_right
          (f := fun x : ℝ => ‖dv x‖ ^ 2) s]
        apply intervalIntegral.integral_mono_interval (by linarith [hs.1])
          (by linarith) (by linarith [hs.2])
          (Eventually.of_forall fun x => sq_nonneg _) hwide)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hm
  calc
    _ ≤ h⁻¹ * ∫ x in (-a)..a, ∫ s in (0 : ℝ)..h, E (x, s) := hfirst
    _ = h⁻¹ * ∫ s in (0 : ℝ)..h, ∫ x in (-a)..a, E (x, s) := by rw [hswap]
    _ ≤ h⁻¹ * (h * ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hlast (inv_nonneg.mpr hh.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

/-- Translation preserves actual L² membership on a smaller half
box. The image inclusion is proved from the true horizontal margin,
and the composition uses an actual isometric homeomorphism. -/
theorem dirichlet_halfBox_translation_memLp {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (fun z => u (z + (h : ℂ))) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let T : ℂ ≃ₜ ℂ := Homeomorph.addRight (h : ℂ)
  have hT : Isometry T := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (z + (h : ℂ)) (w + (h : ℂ)) = dist z w
    simp only [dist_eq_norm]
    congr 1
    abel
  have hTi : Isometry T.symm := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (z + -(h : ℂ)) (w + -(h : ℂ)) = dist z w
    simp only [dist_eq_norm]
    congr 1
    abel
  have hsub : T '' smoothDirichletHalfBox a b ⊆ smoothDirichletHalfBox A b := by
    rintro w ⟨z, hz, rfl⟩
    have hx : |z.re + h| < A :=
      (abs_add_le z.re h).trans_lt
        ((show |z.re| + |h| < a + |h| from
          add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin)
    simpa [T, smoothDirichletHalfBox] using
      (show |z.re + h| < A ∧ 0 < z.im ∧ z.im < b from ⟨hx, hz.2⟩)
  have hm' := hm.mono_measure (Measure.restrict_mono_set volume hsub)
  exact memLp_comp_bilip' (f := T) (K := 1) (isOpen_smoothDirichletHalfBox a b)
    (by norm_num) hT.lipschitz.lipschitzOnWith hTi.lipschitz.lipschitzOnWith hm'

theorem dirichletTangentialDifference_memLp {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifference h u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hsub : smoothDirichletHalfBox a b ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩
  have hs := dirichlet_halfBox_translation_memLp hmargin hm
  have hr := hm.mono_measure (Measure.restrict_mono_set volume hsub)
  have hq := (hs.sub hr).const_smul ((h : ℂ)⁻¹)
  have he : ((h : ℂ)⁻¹ • ((fun z => u (z + (h : ℂ))) - u)) =
      dirichletTangentialDifference h u := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      dirichletTangentialDifference, div_eq_mul_inv]
    ring
  rw [he] at hq
  exact hq

/-- The same actual area integral, with horizontal slices first.
The real-coordinate measure has exactly Jacobian one. -/
theorem dirichlet_halfBox_sq_integral_eq_horizontal_real_prod {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ y in Ioo (0 : ℝ) b, ∫ x in (-a)..a,
        ‖g ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
  rw [dirichlet_halfBox_sq_integral_eq_real_prod hb hg]
  simp_rw [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
  rw [integral_integral_swap (dirichlet_halfBox_sq_integrable_real_prod hg)]
  simp_rw [intervalIntegral.integral_of_le (show -a ≤ a by linarith),
    integral_Ioc_eq_integral_Ioo]

/-- Actual finite first-derivative energy gives a uniform L²
tangential difference-quotient estimate all the way to the flat
boundary. Smoothness is used only at interior horizontal segments;
there is no assumed second derivative at the boundary. -/
theorem dirichlet_halfBox_tangential_difference_energy_le {A a b h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hmargin : a + h < A)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hDx : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖dirichletTangentialDifference h u z‖ ^ 2) ≤
      ∫ z in smoothDirichletHalfBox A b, ‖dirD u 1 z‖ ^ 2 := by
  have hA : 0 < A := lt_trans ha (lt_trans (by linarith : a < a + h) hmargin)
  have hq := dirichletTangentialDifference_memLp
    (show a + |h| ≤ A by rw [abs_of_pos hh]; exact hmargin.le) hm
  have hprodQ := dirichlet_halfBox_sq_integrable_real_prod hq
  have hprodD := dirichlet_halfBox_sq_integrable_real_prod hDx
  have hqi : Integrable (fun y : ℝ => ∫ x in (-a)..a,
      ‖dirichletTangentialDifference h u ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (0 : ℝ) b)) := by
    simpa only [intervalIntegral.integral_of_le (show -a ≤ a by linarith),
      integral_Ioc_eq_integral_Ioo] using hprodQ.integral_prod_right
  have hdi : Integrable (fun y : ℝ => ∫ x in (-A)..A,
      ‖dirD u 1 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (0 : ℝ) b)) := by
    simpa only [intervalIntegral.integral_of_le (show -A ≤ A by linarith),
      integral_Ioc_eq_integral_Ioo] using hprodD.integral_prod_right
  have hdxs := dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs 1
  have hbound :
      (fun y : ℝ => ∫ x in (-a)..a,
        ‖dirichletTangentialDifference h u ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
        ≤ᵐ[volume.restrict (Ioo (0 : ℝ) b)]
      (fun y : ℝ => ∫ x in (-A)..A,
        ‖dirD u 1 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) := by
    filter_upwards [hprodD.prod_left_ae, ae_restrict_mem measurableSet_Ioo]
      with y hdy hy
    let L : ℝ → ℂ := fun x => (x : ℂ) + (y : ℂ) * Complex.I
    have hLc : Continuous L := Complex.ofRealCLM.continuous.add continuous_const
    have hmap : MapsTo L (Icc (-a) (a + h)) (smoothDirichletHalfBox A b) := by
      intro x hx
      have hxA : |x| < A := abs_lt.mpr ⟨by linarith [hx.1], hx.2.trans_lt hmargin⟩
      simpa [L, smoothDirichletHalfBox] using
        (show |x| < A ∧ 0 < y ∧ y < b from ⟨hxA, hy⟩)
    have huv : ContinuousOn (u ∘ L) (Icc (-a) (a + h)) :=
      hs.continuousOn.comp hLc.continuousOn hmap
    have hdv : ContinuousOn (dirD u 1 ∘ L) (Icc (-a) (a + h)) :=
      hdxs.continuousOn.comp hLc.continuousOn hmap
    have hd (x : ℝ) (hx : x ∈ Icc (-a) (a + h)) :
        HasDerivAt (u ∘ L) ((dirD u 1 ∘ L) x) x := by
      have hdu := ((hs.contDiffAt
        ((isOpen_smoothDirichletHalfBox A b).mem_nhds (hmap hx))).differentiableAt
        (by simp)).hasFDerivAt
      have hL : HasDerivAt L 1 x := by
        exact ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * Complex.I)
      exact hdu.comp_hasDerivAt x hL
    have hi := dirichlet_interval_difference_energy_le ha hh huv hdv hd
    have hDfull : IntervalIntegrable (fun x : ℝ => ‖dirD u 1 (L x)‖ ^ 2)
        volume (-A) A := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show -A ≤ A by linarith)]
      simpa only [IntegrableOn, L, restrict_Ioo_eq_restrict_Ioc] using hdy
    have hmono := intervalIntegral.integral_mono_interval
      (show -A ≤ -a by linarith) (show -a ≤ a + h by linarith) hmargin.le
      (Eventually.of_forall fun x => sq_nonneg _) hDfull
    have hi' : (∫ x in (-a)..a,
        ‖dirichletTangentialDifference h u (L x)‖ ^ 2) ≤
        ∫ x in (-a)..(a + h), ‖dirD u 1 (L x)‖ ^ 2 := by
      simpa only [Function.comp_apply, dirichletTangentialDifference, L,
        Complex.ofReal_add, add_right_comm] using hi
    exact hi'.trans hmono
  rw [dirichlet_halfBox_sq_integral_eq_horizontal_real_prod ha hb hq,
    dirichlet_halfBox_sq_integral_eq_horizontal_real_prod hA hb hDx]
  exact integral_mono_ae hqi hdi hbound

/-- Every fixed tangential difference quotient is a genuine H¹
function on the smaller half box. Its derivative is the difference
quotient of the actual first derivative; this is proved from the
ordinary chain rule, not from an assumed H² bound. -/
theorem dirichletTangentialDifference_dirD {h : ℝ} {u : ℂ → ℂ} {z : ℂ}
    (hz : DifferentiableAt ℝ u z) (hzh : DifferentiableAt ℝ u (z + (h : ℂ))) (w : ℂ) :
    dirD (dirichletTangentialDifference h u) w z =
      dirichletTangentialDifference h (dirD u w) z := by
  have hT : HasFDerivAt (fun z : ℂ => z + (h : ℂ))
      (ContinuousLinearMap.id ℝ ℂ) z := (hasFDerivAt_id z).add_const (h : ℂ)
  have hq : HasFDerivAt (dirichletTangentialDifference h u)
      ((h : ℂ)⁻¹ • (fderiv ℝ u (z + (h : ℂ)) - fderiv ℝ u z)) z := by
    have hfun : dirichletTangentialDifference h u =
        fun y => ((u ∘ fun z => z + (h : ℂ)) - u) y * (h : ℂ)⁻¹ := by
      funext y
      simp only [dirichletTangentialDifference, div_eq_mul_inv, Pi.sub_apply,
        Function.comp_apply]
    rw [hfun]
    simpa only [ContinuousLinearMap.comp_id] using
      ((hzh.hasFDerivAt.comp z hT).sub hz.hasFDerivAt).mul_const ((h : ℂ)⁻¹)
  change fderiv ℝ (dirichletTangentialDifference h u) z w = _
  rw [hq.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, dirichletTangentialDifference, dirD, div_eq_mul_inv]
  ring

theorem dirichletTangentialDifference_continuousOn {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifference h u) (smoothDirichletClosedHalfBox a b) := by
  have hmap : MapsTo (fun z : ℂ => z + (h : ℂ))
      (smoothDirichletClosedHalfBox a b) (smoothDirichletClosedHalfBox A b) := by
    intro z hz
    have hx : |z.re + h| ≤ A :=
      (abs_add_le z.re h).trans
        ((show |z.re| + |h| ≤ a + |h| from
          add_le_add hz.1 le_rfl).trans hmargin)
    simpa [smoothDirichletClosedHalfBox] using
      (show |z.re + h| ≤ A ∧ 0 ≤ z.im ∧ z.im ≤ b from ⟨hx, hz.2⟩)
  have hsub : smoothDirichletClosedHalfBox a b ⊆ smoothDirichletClosedHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩
  exact ((hc.comp (continuous_id.add continuous_const).continuousOn hmap).sub
    (hc.mono hsub)).div_const (h : ℂ)

theorem dirichletTangentialDifference_contDiffOn {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletTangentialDifference h u)
      (smoothDirichletHalfBox a b) := by
  have hmap : MapsTo (fun z : ℂ => z + (h : ℂ))
      (smoothDirichletHalfBox a b) (smoothDirichletHalfBox A b) := by
    intro z hz
    have hx : |z.re + h| < A :=
      (abs_add_le z.re h).trans_lt
        ((show |z.re| + |h| < a + |h| from
          add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin)
    simpa [smoothDirichletHalfBox] using
      (show |z.re + h| < A ∧ 0 < z.im ∧ z.im < b from ⟨hx, hz.2⟩)
  have hsub : smoothDirichletHalfBox a b ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩
  exact ((hs.comp (contDiff_id.add contDiff_const).contDiffOn hmap).sub
    (hs.mono hsub)).div_const (h : ℂ)

theorem dirichletTangentialDifference_zero_bottom {A a h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0) {x : ℝ} (hx : |x| < a) :
    dirichletTangentialDifference h u (x : ℂ) = 0 := by
  have hxA : |x| < A :=
    hx.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin)
  have hxh : |x + h| < A :=
    (abs_add_le x h).trans_lt
      ((show |x| + |h| < a + |h| from
        add_lt_add_of_lt_of_le hx le_rfl).trans_le hmargin)
  simp only [dirichletTangentialDifference, ← Complex.ofReal_add,
    hz x hxA, hz (x + h) hxh, sub_self, zero_div]

theorem dirichletTangentialDifference_gradient_memLp {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b)) {w : ℂ}
    (hg : MemLp (dirD u w) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirD (dirichletTangentialDifference h u) w) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hmem := dirichletTangentialDifference_memLp hmargin hg
  apply hmem.ae_eq
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  have hzA : z ∈ smoothDirichletHalfBox A b :=
    ⟨hz.1.trans_le (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩
  have hx : |z.re + h| < A :=
    (abs_add_le z.re h).trans_lt
      ((show |z.re| + |h| < a + |h| from
        add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin)
  have hzh : z + (h : ℂ) ∈ smoothDirichletHalfBox A b := by
    simpa [smoothDirichletHalfBox] using
      (show |z.re + h| < A ∧ 0 < z.im ∧ z.im < b from ⟨hx, hz.2⟩)
  exact (dirichletTangentialDifference_dirD
    ((hs.contDiffAt ((isOpen_smoothDirichletHalfBox A b).mem_nhds hzA)).differentiableAt
      (by simp))
    ((hs.contDiffAt ((isOpen_smoothDirichletHalfBox A b).mem_nhds hzh)).differentiableAt
      (by simp)) w).symm

/-- The actual original conformal Green remainder satisfies a
uniform tangential value estimate near every smooth physical
boundary point. This is a first-derivative consequence, with no
extra boundary regularity assumption in the supplied-map tuple. -/
theorem exists_riemannMapping_flattened_tangential_difference_energy {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (A b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < A ∧ 0 < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       ∀ h : ℝ, h ∈ Ioo 0 (A / 2) →
         (∫ z in smoothDirichletHalfBox (A / 2) b,
           ‖dirichletTangentialDifference h u z‖ ^ 2) ≤
         ∫ z in smoothDirichletHalfBox A b, ‖dirD u 1 z‖ ^ 2) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    _, _, hs, _, v, hv, hgv⟩ :=
    exists_riemannMapping_flattened_zero_boundary_h1 hb hS hsc F hF hinj himage hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  have hvm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)) :=
    (Lp.memLp (h1Value (smoothDirichletHalfBox A b) v)).ae_eq hv
  have hvg : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox A b)) := by
    simpa only [u, Function.comp_def, coordDir, Matrix.cons_val_zero] using
      (Lp.memLp (h1Gradient (smoothDirichletHalfBox A b) 0 v)).ae_eq (hgv 0)
  refine ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀, ?_⟩
  dsimp only
  intro h hh
  exact dirichlet_halfBox_tangential_difference_energy_le (by linarith) hb₀ hh.1
    (by linarith [hh.2]) hs hvm hvg

/-- The true graph slope is Lipschitz on every compact horizontal
interval, because its actual second derivative is continuous. The
coefficient bound is derived from the supplied smooth graph. -/
theorem exists_dirichletGraphSlope_interval_lipschitz {A : ℝ} (hA : 0 < A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Icc (-A) A, ∀ y ∈ Icc (-A) A,
      |deriv f y - deriv f x| ≤ L * |y - x| := by
  have hdf := (contDiff_infty_iff_deriv.mp hf).2
  have hddf := (contDiff_infty_iff_deriv.mp hdf).2
  obtain ⟨L, hL⟩ := (isCompact_Icc : IsCompact (Icc (-A) A)).exists_bound_of_continuousOn
    hddf.continuous.continuousOn
  have hL₀ : 0 ≤ L := (norm_nonneg (deriv (deriv f) 0)).trans
    (hL 0 ⟨by linarith, hA.le⟩)
  refine ⟨L, hL₀, ?_⟩
  intro x hx y hy
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hdf.differentiable (by simp)) t) hL (convex_Icc (-A) A) hx hy

/-- The actual coefficient matrix at the shifted horizontal point,
acting on the gradient at the original point. -/
def dirichletShiftedFlux (f : ℝ → ℝ) (h : ℝ) (v : ℂ → ℂ)
    (i : Fin 2) (z : ℂ) : ℂ :=
  ![dirD v 1 z - dirichletGraphSlope f (z + (h : ℂ)) * dirD v Complex.I z,
    -dirichletGraphSlope f (z + (h : ℂ)) * dirD v 1 z +
      (1 + dirichletGraphSlope f (z + (h : ℂ)) ^ 2) * dirD v Complex.I z] i

/-- The actual coefficient commutator in the tangential difference
equation. Both entries are differences of the genuine graph matrix. -/
def dirichletCoefficientDifferenceFlux (f : ℝ → ℝ) (h : ℝ) (u : ℂ → ℂ)
    (i : Fin 2) (z : ℂ) : ℂ :=
  ![-dirichletTangentialDifference h (dirichletGraphSlope f) z * dirD u Complex.I z,
    -dirichletTangentialDifference h (dirichletGraphSlope f) z * dirD u 1 z +
      dirichletTangentialDifference h (fun w => 1 + dirichletGraphSlope f w ^ 2) z *
        dirD u Complex.I z] i

/-- The difference of the actual flux splits into the shifted
elliptic flux and the true coefficient commutator. In particular,
the differentiated equation is not a new assumed boundary PDE. -/
theorem dirichletTangentialDifference_flux_split {f : ℝ → ℝ} {h : ℝ}
    (hh : h ≠ 0) {u : ℂ → ℂ} {z : ℂ}
    (hz : DifferentiableAt ℝ u z) (hzh : DifferentiableAt ℝ u (z + (h : ℂ)))
    (i : Fin 2) :
    dirichletTangentialDifference h (dirichletFlattenedFlux f u i) z =
      dirichletShiftedFlux f h (dirichletTangentialDifference h u) i z +
        dirichletCoefficientDifferenceFlux f h u i z := by
  have hdx := dirichletTangentialDifference_dirD hz hzh 1
  have hdy := dirichletTangentialDifference_dirD hz hzh Complex.I
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  fin_cases i
  · change ((dirD u 1 (z + (h : ℂ)) -
        dirichletGraphSlope f (z + (h : ℂ)) * dirD u Complex.I (z + (h : ℂ))) -
      (dirD u 1 z - dirichletGraphSlope f z * dirD u Complex.I z)) / (h : ℂ) =
      (dirD (dirichletTangentialDifference h u) 1 z -
        dirichletGraphSlope f (z + (h : ℂ)) *
          dirD (dirichletTangentialDifference h u) Complex.I z) +
      (-dirichletTangentialDifference h (dirichletGraphSlope f) z *
        dirD u Complex.I z)
    rw [hdx, hdy]
    simp only [dirichletTangentialDifference]
    field_simp [hhC]
    ring
  · change ((-dirichletGraphSlope f (z + (h : ℂ)) * dirD u 1 (z + (h : ℂ)) +
        (1 + dirichletGraphSlope f (z + (h : ℂ)) ^ 2) *
          dirD u Complex.I (z + (h : ℂ))) -
      (-dirichletGraphSlope f z * dirD u 1 z +
        (1 + dirichletGraphSlope f z ^ 2) * dirD u Complex.I z)) / (h : ℂ) =
      (-dirichletGraphSlope f (z + (h : ℂ)) *
          dirD (dirichletTangentialDifference h u) 1 z +
        (1 + dirichletGraphSlope f (z + (h : ℂ)) ^ 2) *
          dirD (dirichletTangentialDifference h u) Complex.I z) +
      (-dirichletTangentialDifference h (dirichletGraphSlope f) z * dirD u 1 z +
        dirichletTangentialDifference h (fun w => 1 + dirichletGraphSlope f w ^ 2) z *
          dirD u Complex.I z)
    rw [hdx, hdy]
    simp only [dirichletTangentialDifference]
    field_simp [hhC]
    ring

/-- Differentiating the true interior divergence equation gives
the actual weak tangential difference equation on a smaller half
box. All derivatives used here lie inside the original open box;
the coefficient commutator is the explicit physical graph term. -/
theorem dirichletTangentialDifference_weak_equation {A a b h : ℝ}
    (hh : h ≠ 0) (hmargin : a + |h| ≤ A) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    {φ : ℂ → ℂ} (hφ : TestFunction (smoothDirichletHalfBox a b) φ) :
    (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
      (dirichletShiftedFlux f h (dirichletTangentialDifference h u) i z +
        dirichletCoefficientDifferenceFlux f h u i z) * dirD φ (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b, dirichletTangentialDifference h G z * φ z := by
  let U := smoothDirichletHalfBox A b
  let V := smoothDirichletHalfBox a b
  let H : Fin 2 → ℂ → ℂ := fun i =>
    dirichletTangentialDifference h (dirichletFlattenedFlux f u i)
  have hU : IsOpen U := isOpen_smoothDirichletHalfBox A b
  have hV : IsOpen V := isOpen_smoothDirichletHalfBox a b
  have hzdata (z : ℂ) (hz : z ∈ V) : z ∈ U ∧ z + (h : ℂ) ∈ U := by
    have hx : |z.re + h| < A :=
      (abs_add_le z.re h).trans_lt
        ((show |z.re| + |h| < a + |h| from
          add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin)
    refine ⟨⟨hz.1.trans_le
      (le_trans (le_add_of_nonneg_right (abs_nonneg h)) hmargin), hz.2⟩, ?_⟩
    simpa [U, smoothDirichletHalfBox] using
      (show |z.re + h| < A ∧ 0 < z.im ∧ z.im < b from ⟨hx, hz.2⟩)
  have hflux (i : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (dirichletFlattenedFlux f u i) U :=
    dirichletFlattenedFlux_contDiffOn hU hf hs i
  have hH (i : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (H i) V :=
    dirichletTangentialDifference_contDiffOn hmargin (hflux i)
  have hdiv (z : ℂ) (hz : z ∈ V) :
      (∑ i : Fin 2, dirD (H i) (coordDir i) z) =
        -dirichletTangentialDifference h G z := by
    obtain ⟨hzU, hzhU⟩ := hzdata z hz
    have hd (i : Fin 2) : dirD (H i) (coordDir i) z =
        dirichletTangentialDifference h (dirD (dirichletFlattenedFlux f u i) (coordDir i)) z :=
      dirichletTangentialDifference_dirD
        (((hflux i).contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp))
        (((hflux i).contDiffAt (hU.mem_nhds hzhU)).differentiableAt (by simp)) _
    simp_rw [hd]
    rw [Fin.sum_univ_two]
    simp only [coordDir, Matrix.cons_val_zero, Matrix.cons_val_one, dirichletTangentialDifference]
    calc
      _ = (dirichletFlattenedDivergence f u (z + (h : ℂ)) -
          dirichletFlattenedDivergence f u z) / (h : ℂ) := by
        unfold dirichletFlattenedDivergence
        ring
      _ = _ := by rw [hstrong _ hzhU, hstrong _ hzU]; ring
  have hI (i : Fin 2) : IntegrableOn
      (fun z => H i z * dirD φ (coordDir i) z) V :=
    dirichlet_local_smooth_mul_test_integrable hV (hH i) (hφ.dirD (coordDir i))
  have hDI (i : Fin 2) : IntegrableOn
      (fun z => dirD (H i) (coordDir i) z * φ z) V :=
    dirichlet_local_smooth_mul_test_integrable hV
      (dirichlet_contDiffOn_dirD hV (hH i) (coordDir i)) hφ
  have heq : (∫ z in V, ∑ i : Fin 2, H i z * dirD φ (coordDir i) z) =
      -(∫ z in V, (∑ i : Fin 2, dirD (H i) (coordDir i) z) * φ z) := by
    rw [integral_finset_sum _ (fun i _ => hI i)]
    have hibp (i : Fin 2) := dirichlet_local_smooth_field_test_eq_neg_dirD hV (hH i) hφ i
    have hsum : (∑ i : Fin 2, ∫ z in V, H i z * dirD φ (coordDir i) z) =
        ∑ i : Fin 2, -(∫ z in V, dirD (H i) (coordDir i) z * φ z) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hibp i
    rw [hsum, Finset.sum_neg_distrib, ← integral_finset_sum _ (fun i _ => hDI i)]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [Finset.sum_mul]
  have hleft : (∫ z in V, ∑ i : Fin 2,
      (dirichletShiftedFlux f h (dirichletTangentialDifference h u) i z +
        dirichletCoefficientDifferenceFlux f h u i z) * dirD φ (coordDir i) z) =
      ∫ z in V, ∑ i : Fin 2, H i z * dirD φ (coordDir i) z := by
    apply setIntegral_congr_fun hV.measurableSet
    intro z hz
    obtain ⟨hzU, hzhU⟩ := hzdata z hz
    apply Finset.sum_congr rfl
    intro i _
    rw [← dirichletTangentialDifference_flux_split hh
      ((hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp))
      ((hs.contDiffAt (hU.mem_nhds hzhU)).differentiableAt (by simp)) i]
  change (∫ z in V, ∑ i : Fin 2,
    (dirichletShiftedFlux f h (dirichletTangentialDifference h u) i z +
      dirichletCoefficientDifferenceFlux f h u i z) * dirD φ (coordDir i) z) = _
  rw [hleft, heq, ← integral_neg]
  apply setIntegral_congr_fun hV.measurableSet
  intro z hz
  change -((∑ i : Fin 2, dirD (H i) (coordDir i) z) * φ z) =
    dirichletTangentialDifference h G z * φ z
  rw [hdiv z hz]
  ring

private theorem dirichlet_energy_young {M : ℝ} (hM : 0 < M) (Y S : ℝ) :
    Y * S ≤ Y ^ 2 / (4 * M) + M * S ^ 2 := by
  have hfourM : 0 < 4 * M := mul_pos (by norm_num) hM
  have hpoly : 4 * M * Y * S ≤ Y ^ 2 + 4 * M ^ 2 * S ^ 2 := by
    nlinarith only [sq_nonneg (Y - 2 * M * S)]
  calc
    Y * S = (4 * M * Y * S) / (4 * M) := by field_simp [hM.ne']
    _ ≤ (Y ^ 2 + 4 * M ^ 2 * S ^ 2) / (4 * M) :=
      div_le_div_of_nonneg_right hpoly hfourM.le
    _ = _ := by field_simp [hM.ne']

/-- The pointwise absorption estimate for a complex-valued
localized elliptic test. The coefficient coercivity and norm bounds
are algebraic inputs; the actual graph matrix supplies both below.
The cutoff is allowed to be complex, since its weight is `η·conj η`. -/
theorem dirichlet_localized_energy_absorption {M B : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (η α β v x y F₀ F₁ C₀ C₁ G : ℂ)
    (hη : ‖η‖ ≤ 1) (hα : ‖α‖ ≤ B) (hβ : ‖β‖ ≤ B)
    (hcoer : (‖x‖ ^ 2 + ‖y‖ ^ 2) / M ≤ (F₀ * conj x + F₁ * conj y).re)
    (hF : ‖F₀‖ + ‖F₁‖ ≤ 2 * M * (‖x‖ + ‖y‖)) :
    let ρ := η * conj η
    let b₀ := α * conj η + η * conj α
    let b₁ := β * conj η + η * conj β
    let L := (F₀ + C₀) * (ρ * conj x + b₀ * conj v) +
      (F₁ + C₁) * (ρ * conj y + b₁ * conj v)
    ‖η‖ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * M) ≤
      (L - G * ρ * conj v).re + ‖G‖ ^ 2 +
        (4 * M + 2 * B ^ 2) * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) * ‖v‖ ^ 2 := by
  let ρ := η * conj η
  let b₀ := α * conj η + η * conj α
  let b₁ := β * conj η + η * conj β
  let L := (F₀ + C₀) * (ρ * conj x + b₀ * conj v) +
    (F₁ + C₁) * (ρ * conj y + b₁ * conj v)
  let X := ‖x‖ + ‖y‖
  let c := ‖C₀‖ + ‖C₁‖
  let Y := ‖η‖ * X
  let T := ‖η‖ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)
  let S := c + 4 * B * M * ‖v‖
  let main := ρ * (F₀ * conj x + F₁ * conj y)
  let err := (F₀ * b₀ + F₁ * b₁) * conj v +
    ρ * (C₀ * conj x + C₁ * conj y) +
    (C₀ * b₀ + C₁ * b₁) * conj v - G * ρ * conj v
  have hX₀ : 0 ≤ X := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc₀ : 0 ≤ c := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hρnorm : ‖ρ‖ = ‖η‖ ^ 2 := by simp only [ρ, norm_mul, norm_conj, pow_two]
  have hρ : ρ = ((‖η‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [← Complex.ofReal_pow] using Complex.mul_conj' η
  have hb₀ : ‖b₀‖ ≤ 2 * B * ‖η‖ := by
    calc
      _ ≤ ‖α * conj η‖ + ‖η * conj α‖ := norm_add_le _ _
      _ = 2 * ‖α‖ * ‖η‖ := by simp only [norm_mul, norm_conj]; ring
      _ ≤ _ := by gcongr
  have hb₁ : ‖b₁‖ ≤ 2 * B * ‖η‖ := by
    calc
      _ ≤ ‖β * conj η‖ + ‖η * conj β‖ := norm_add_le _ _
      _ = 2 * ‖β‖ * ‖η‖ := by simp only [norm_mul, norm_conj]; ring
      _ ≤ _ := by gcongr
  have hηsq : ‖η‖ ^ 2 ≤ ‖η‖ := by nlinarith only [hη, norm_nonneg η]
  have hAerr : ‖(F₀ * b₀ + F₁ * b₁) * conj v‖ ≤ 4 * B * M * Y * ‖v‖ := by
    rw [norm_mul, norm_conj]
    calc
      _ ≤ (‖F₀ * b₀‖ + ‖F₁ * b₁‖) * ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖F₀‖ * (2 * B * ‖η‖) + ‖F₁‖ * (2 * B * ‖η‖)) * ‖v‖ := by
        simp only [norm_mul]
        gcongr
      _ = 2 * B * ‖η‖ * (‖F₀‖ + ‖F₁‖) * ‖v‖ := by ring
      _ ≤ 2 * B * ‖η‖ * (2 * M * X) * ‖v‖ := by gcongr
      _ = _ := by dsimp [Y]; ring
  have hCdot : ‖C₀ * conj x + C₁ * conj y‖ ≤ c * X := by
    calc
      _ ≤ ‖C₀ * conj x‖ + ‖C₁ * conj y‖ := norm_add_le _ _
      _ = ‖C₀‖ * ‖x‖ + ‖C₁‖ * ‖y‖ := by simp only [norm_mul, norm_conj]
      _ ≤ _ := by
        dsimp [c, X]
        nlinarith only [mul_nonneg (norm_nonneg C₀) (norm_nonneg y),
          mul_nonneg (norm_nonneg C₁) (norm_nonneg x)]
  have hCmain : ‖ρ * (C₀ * conj x + C₁ * conj y)‖ ≤ c * Y := by
    rw [norm_mul, hρnorm]
    calc
      _ ≤ ‖η‖ ^ 2 * (c * X) := mul_le_mul_of_nonneg_left hCdot (sq_nonneg _)
      _ ≤ ‖η‖ * (c * X) := mul_le_mul_of_nonneg_right hηsq (mul_nonneg hc₀ hX₀)
      _ = _ := by dsimp [Y]; ring
  have hCerr : ‖(C₀ * b₀ + C₁ * b₁) * conj v‖ ≤ 2 * B * c * ‖v‖ := by
    rw [norm_mul, norm_conj]
    calc
      _ ≤ (‖C₀ * b₀‖ + ‖C₁ * b₁‖) * ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖C₀‖ * (2 * B * ‖η‖) + ‖C₁‖ * (2 * B * ‖η‖)) * ‖v‖ := by
        simp only [norm_mul]
        gcongr
      _ = 2 * B * c * ‖η‖ * ‖v‖ := by dsimp [c]; ring
      _ ≤ 2 * B * c * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have hGerr : ‖G * ρ * conj v‖ ≤ ‖G‖ * ‖v‖ := by
    rw [norm_mul, norm_mul, hρnorm, norm_conj]
    have hηsq₁ : ‖η‖ ^ 2 ≤ 1 := hηsq.trans hη
    calc
      _ ≤ ‖G‖ * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have herr : ‖err‖ ≤ Y * S + 2 * B * c * ‖v‖ + ‖G‖ * ‖v‖ := by
    calc
      _ ≤ ‖(F₀ * b₀ + F₁ * b₁) * conj v +
          ρ * (C₀ * conj x + C₁ * conj y) + (C₀ * b₀ + C₁ * b₁) * conj v‖ +
          ‖G * ρ * conj v‖ := norm_sub_le _ _
      _ ≤ ((‖(F₀ * b₀ + F₁ * b₁) * conj v‖ +
          ‖ρ * (C₀ * conj x + C₁ * conj y)‖) +
          ‖(C₀ * b₀ + C₁ * b₁) * conj v‖) + ‖G * ρ * conj v‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ((4 * B * M * Y * ‖v‖ + c * Y) + 2 * B * c * ‖v‖) + ‖G‖ * ‖v‖ := by
        gcongr
      _ = _ := by dsimp [S]; ring
  have hYsq : Y ^ 2 ≤ 2 * T := by
    dsimp [Y, X, T]
    have hxy : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖x‖ - ‖y‖)]
    convert mul_le_mul_of_nonneg_left hxy (sq_nonneg ‖η‖) using 1 <;> ring
  have hSsq : S ^ 2 ≤ 2 * c ^ 2 + 32 * B ^ 2 * M ^ 2 * ‖v‖ ^ 2 := by
    dsimp [S]
    nlinarith only [sq_nonneg (c - 4 * B * M * ‖v‖)]
  have hfourM : 0 < 4 * M := by positivity
  have hYoung : Y * S ≤ Y ^ 2 / (4 * M) + M * S ^ 2 :=
    dirichlet_energy_young hM Y S
  have hYoung' : Y * S ≤ T / (2 * M) + 2 * M * c ^ 2 +
      32 * B ^ 2 * M ^ 3 * ‖v‖ ^ 2 := by
    calc
      _ ≤ Y ^ 2 / (4 * M) + M * S ^ 2 := hYoung
      _ ≤ (2 * T) / (4 * M) + M *
          (2 * c ^ 2 + 32 * B ^ 2 * M ^ 2 * ‖v‖ ^ 2) :=
        add_le_add (div_le_div_of_nonneg_right hYsq hfourM.le)
          (mul_le_mul_of_nonneg_left hSsq hM.le)
      _ = _ := by field_simp [hM.ne']; ring
  have hBc : 2 * B * c * ‖v‖ ≤ B ^ 2 * c ^ 2 + ‖v‖ ^ 2 := by
    nlinarith only [sq_nonneg (B * c - ‖v‖)]
  have hGv : ‖G‖ * ‖v‖ ≤ ‖G‖ ^ 2 + ‖v‖ ^ 2 := by
    nlinarith only [sq_nonneg (‖G‖ - ‖v‖), sq_nonneg ‖G‖, sq_nonneg ‖v‖]
  have hcsq : c ^ 2 ≤ 2 * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) := by
    dsimp [c]
    nlinarith only [sq_nonneg (‖C₀‖ - ‖C₁‖)]
  have herr' : ‖err‖ ≤ T / (2 * M) + ‖G‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v‖ ^ 2 := by
    have hcBound := mul_le_mul_of_nonneg_left hcsq
      (show 0 ≤ 2 * M + B ^ 2 by positivity)
    linarith only [herr, hYoung', hBc, hGv, hcBound]
  have hmain : T / M ≤ main.re := by
    rw [show main = ((‖η‖ ^ 2 : ℝ) : ℂ) * (F₀ * conj x + F₁ * conj y) by rw [← hρ]]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      _ = ‖η‖ ^ 2 * ((‖x‖ ^ 2 + ‖y‖ ^ 2) / M) := by dsimp [T]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoer (sq_nonneg _)
  have heq : L - G * ρ * conj v = main + err := by dsimp [L, main, err]; ring
  have hmainBound : main.re ≤ (L - G * ρ * conj v).re + ‖err‖ := by
    rw [heq, Complex.add_re]
    have h := Complex.re_le_norm (-err)
    simp only [Complex.neg_re, norm_neg] at h
    linarith only [h]
  have hTsplit : T / M = T / (2 * M) + T / (2 * M) := by
    field_simp [hM.ne']; ring
  change T / (2 * M) ≤ _
  linarith only [hmain, hmainBound, herr', hTsplit]

/-- A genuine smooth compact weight, even for a complex cutoff. -/
def dirichletCutoffWeight (η : smoothTraceTests) : smoothTraceTests :=
  ⟨fun z => η z * conj (η z),
    ⟨η.property.1.mul (Complex.conjCLE.contDiff.comp η.property.1),
      η.property.2.1.mul_right, subset_univ _⟩⟩

theorem dirichlet_dirD_conj_at {u : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (w : ℂ) :
    dirD (fun z => conj (u z)) w z = conj (dirD u w z) := by
  have hd := (Complex.conjCLE.hasFDerivAt.comp z hu.hasFDerivAt).fderiv
  change fderiv ℝ (Complex.conjCLE ∘ u) z w = _
  rw [hd]
  rfl

theorem dirichletCutoffWeight_dirD (η : smoothTraceTests) (w z : ℂ) :
    dirD (dirichletCutoffWeight η : ℂ → ℂ) w z =
      dirD (η : ℂ → ℂ) w z * conj (η z) +
        η z * conj (dirD (η : ℂ → ℂ) w z) := by
  have hη := ((η.property.1.differentiable (by simp)) z).hasFDerivAt
  have hc := Complex.conjCLE.hasFDerivAt.comp z hη
  have hd := (hη.mul hc).fderiv
  change fderiv ℝ ((η : ℂ → ℂ) * (Complex.conjCLE ∘ (η : ℂ → ℂ))) z w = _
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_apply,
    Function.comp_apply, Complex.conjCLE_apply,
    smul_eq_mul, dirD]
  ring

theorem dirichlet_cutoff_conj_product_dirD (η : smoothTraceTests)
    {v : ℂ → ℂ} {z : ℂ} (hv : DifferentiableAt ℝ v z) (w : ℂ) :
    dirD (fun z => dirichletCutoffWeight η z * conj (v z)) w z =
      dirichletCutoffWeight η z * conj (dirD v w z) +
        (dirD (η : ℂ → ℂ) w z * conj (η z) +
          η z * conj (dirD (η : ℂ → ℂ) w z)) * conj (v z) := by
  have hweight := (((dirichletCutoffWeight η).property.1.differentiable (by simp)) z)
  have hc := Complex.conjCLE.hasFDerivAt.comp z hv.hasFDerivAt
  have hd := (hweight.hasFDerivAt.mul hc).fderiv
  change fderiv ℝ ((dirichletCutoffWeight η : ℂ → ℂ) * (Complex.conjCLE ∘ v)) z w = _
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply, Complex.conjCLE_apply, smul_eq_mul]
  change dirichletCutoffWeight η z * conj (dirD v w z) +
    conj (v z) * dirD (dirichletCutoffWeight η : ℂ → ℂ) w z = _
  rw [dirichletCutoffWeight_dirD]
  ring

/-- The genuine localized energy estimate for a zero-boundary H¹
solution of a weak elliptic equation with an L² flux commutator.
The boundary test is obtained by the proved normal-cutoff passage.
There is no assumed boundary test density or second-derivative gain. -/
theorem dirichlet_localized_boundary_energy_bound {a b M B : ℝ}
    (hb : 0 < b) (hM : 0 < M) (hB : 0 ≤ B)
    (η : smoothTraceTests)
    (hηsupp : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    (hη : ∀ z : ℂ, ‖η z‖ ≤ 1)
    (hηgrad : ∀ z : ℂ, ∀ i : Fin 2, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B)
    {v : ℂ → ℂ} (hc : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    {F C : Fin 2 → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ i : Fin 2, MemLp (F i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hC : ∀ i : Fin 2, MemLp (C i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hcoer : ∀ z ∈ smoothDirichletHalfBox a b,
      (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / M ≤
        (F 0 z * conj (dirD v 1 z) + F 1 z * conj (dirD v Complex.I z)).re)
    (hFbound : ∀ z ∈ smoothDirichletHalfBox a b,
      ‖F 0 z‖ + ‖F 1 z‖ ≤ 2 * M * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖))
    (hweak : ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
        (F i z + C i z) * dirD φ (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b, G z * φ z) :
    (∫ z in smoothDirichletHalfBox a b,
      ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)) / (2 * M) ≤
      (∫ z in smoothDirichletHalfBox a b, ‖G z‖ ^ 2) +
        (4 * M + 2 * B ^ 2) *
          (∫ z in smoothDirichletHalfBox a b, ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) *
          (∫ z in smoothDirichletHalfBox a b, ‖v z‖ ^ 2) := by
  let U := smoothDirichletHalfBox a b
  let μ := volume.restrict U
  let φ : ℂ → ℂ := fun z => dirichletCutoffWeight η z * conj (v z)
  let J : ℂ → ℝ := fun z =>
    ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)
  let R : ℂ → ℂ := fun z =>
    (∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z) - G z * φ z
  have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
  have hvc : ContinuousOn (fun z => conj (v z)) (smoothDirichletClosedHalfBox a b) :=
    Complex.conjCLE.continuous.comp_continuousOn hc
  have hvs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => conj (v z)) U :=
    Complex.conjCLE.contDiff.comp_contDiffOn hs
  have hvz : ∀ x : ℝ, |x| < a → conj (v (x : ℂ)) = 0 := by
    intro x hx
    simp only [hz x hx, map_zero]
  have hvg (i : Fin 2) : MemLp (dirD (fun z => conj (v z)) (coordDir i)) 2 μ := by
    apply (hg i).star.ae_eq
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    exact (dirichlet_dirD_conj_at
      ((hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)) _).symm
  have hweightSupp : tsupport (dirichletCutoffWeight η : ℂ → ℂ) ⊆
      {z : ℂ | |z.re| < a ∧ z.im < b} := tsupport_mul_subset_left.trans hηsupp
  have hφ : MemLp φ 2 μ := dirichlet_localized_memLp (dirichletCutoffWeight η) hm.star
  have hφg (i : Fin 2) : MemLp (dirD φ (coordDir i)) 2 μ :=
    dirichlet_localized_gradient_memLp hU (dirichletCutoffWeight η) hvs hm.star (hvg i)
  have heq : (∫ z, ∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z ∂μ) =
      ∫ z, G z * φ z ∂μ :=
    dirichlet_weak_equation_localized_zero_boundary_test hb
      (dirichletCutoffWeight η) hweightSupp hvc hvs hvz hm.star hvg
      (fun i => (hF i).add (hC i)) hG hweak
  have hFluxInt : Integrable
      (fun z => ∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z) μ :=
    integrable_finset_sum _ (fun i _ =>
      ((hF i).add (hC i)).integrable_mul (hφg i))
  have hLoadInt : Integrable (fun z => G z * φ z) μ := hG.integrable_mul hφ
  have hRi : Integrable R μ := hFluxInt.sub hLoadInt
  have hRzero : (∫ z, (R z).re ∂μ) = 0 := by
    change (∫ z, RCLike.re (R z) ∂μ) = 0
    rw [integral_re hRi]
    have hR : (∫ z, R z ∂μ) = 0 := by
      dsimp only [R]
      rw [integral_sub hFluxInt hLoadInt, heq, sub_self]
    simp only [hR, RCLike.zero_re]
  have hηDx := dirichlet_localized_memLp η
    (show MemLp (dirD v 1) 2 μ by simpa only [coordDir, Matrix.cons_val_zero] using hg 0)
  have hηDy := dirichlet_localized_memLp η
    (show MemLp (dirD v Complex.I) 2 μ by
      simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1)
  have hJ : Integrable J μ := by
    apply ((hηDx.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      (hηDy.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).congr
    filter_upwards with z
    change ‖η z * dirD v 1 z‖ ^ 2 + ‖η z * dirD v Complex.I z‖ ^ 2 =
      ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)
    simp only [norm_mul, mul_pow]
    ring
  have hGsq := hG.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hCsq : Integrable (fun z => ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) μ :=
    ((hC 0).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
    ((hC 1).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hvsq := hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hRre : Integrable (fun z => (R z).re) μ := hRi.re
  have hRG : Integrable (fun z => (R z).re + ‖G z‖ ^ 2) μ := hRre.add hGsq
  have hRGC : Integrable (fun z => (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2)) μ :=
    hRG.add (hCsq.const_mul (4 * M + 2 * B ^ 2))
  have hright : Integrable (fun z => (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2) μ :=
    hRGC.add (hvsq.const_mul (32 * B ^ 2 * M ^ 3 + 2))
  have hmono : (∫ z, J z / (2 * M) ∂μ) ≤
      ∫ z, (R z).re + ‖G z‖ ^ 2 +
        (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2 ∂μ := by
    apply integral_mono_ae (hJ.div_const (2 * M)) hright
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    have hdv := (hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    have hp := dirichlet_localized_energy_absorption hM hB (η z)
      (dirD (η : ℂ → ℂ) 1 z) (dirD (η : ℂ → ℂ) Complex.I z)
      (v z) (dirD v 1 z) (dirD v Complex.I z) (F 0 z) (F 1 z) (C 0 z) (C 1 z) (G z)
      (hη z) (by simpa only [coordDir, Matrix.cons_val_zero] using hηgrad z 0)
      (by simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hηgrad z 1)
      (hcoer z hzU) (hFbound z hzU)
    have hRpoint : R z =
        (F 0 z + C 0 z) * (dirichletCutoffWeight η z * conj (dirD v 1 z) +
          (dirD (η : ℂ → ℂ) 1 z * conj (η z) +
            η z * conj (dirD (η : ℂ → ℂ) 1 z)) * conj (v z)) +
        (F 1 z + C 1 z) * (dirichletCutoffWeight η z * conj (dirD v Complex.I z) +
          (dirD (η : ℂ → ℂ) Complex.I z * conj (η z) +
            η z * conj (dirD (η : ℂ → ℂ) Complex.I z)) * conj (v z)) -
        G z * dirichletCutoffWeight η z * conj (v z) := by
      dsimp only [R]
      rw [Fin.sum_univ_two]
      simp only [coordDir, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [dirichlet_cutoff_conj_product_dirD η hdv 1,
        dirichlet_cutoff_conj_product_dirD η hdv Complex.I]
      dsimp only [φ]
      ring
    change J z / (2 * M) ≤ (R z).re + ‖G z‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2
    rw [hRpoint]
    exact hp
  rw [integral_add hRGC (hvsq.const_mul _),
    integral_add hRG (hCsq.const_mul _), integral_add hRre hGsq,
    hRzero, zero_add, integral_const_mul, integral_const_mul] at hmono
  simpa only [J, div_eq_mul_inv, integral_mul_const] using hmono

theorem dirichlet_graph_flux_conj_pair (d : ℝ) (x y : ℂ) :
    ((x - (d : ℂ) * y) * conj x +
      (-(d : ℂ) * x + (1 + (d : ℂ) ^ 2) * y) * conj y).re =
      ‖x - (d : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

theorem dirichletShiftedFlux_coercive {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (h : ℝ) (v : ℂ → ℂ) (z : ℂ) :
    (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      (dirichletShiftedFlux f h v 0 z * conj (dirD v 1 z) +
        dirichletShiftedFlux f h v 1 z * conj (dirD v Complex.I z)).re := by
  simp only [dirichletShiftedFlux, Matrix.cons_val_zero, Matrix.cons_val_one, dirichletGraphSlope]
  rw [dirichlet_graph_flux_conj_pair]
  exact (smoothDirichletGraph_complex_energy_bounds hLip (z + (h : ℂ)).re _ _).1

theorem dirichletShiftedFlux_norm_sum_bound {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (h : ℝ) (v : ℂ → ℂ) (z : ℂ) :
    ‖dirichletShiftedFlux f h v 0 z‖ + ‖dirichletShiftedFlux f h v 1 z‖ ≤
      2 * (2 * (1 + (K : ℝ) ^ 2)) * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖) := by
  let M := 2 * (1 + (K : ℝ) ^ 2)
  let d := dirichletGraphSlope f (z + (h : ℂ))
  let x := dirD v 1 z
  let y := dirD v Complex.I z
  have hd : ‖d‖ ≤ (K : ℝ) := by
    simpa only [d, dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip (x₀ := (z + (h : ℂ)).re)
  have h₁ : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg (K : ℝ)]
  have hK : (K : ℝ) ≤ M := by dsimp [M]; nlinarith [sq_nonneg ((K : ℝ) - 1)]
  have hKK : 1 + (K : ℝ) ^ 2 ≤ M := by dsimp [M]; nlinarith [sq_nonneg (K : ℝ)]
  have ha : ‖(1 : ℂ) + d ^ 2‖ ≤ 1 + (K : ℝ) ^ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖d ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖d‖ ^ 2 := by rw [norm_one, norm_pow]
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hd 2)
  have hdM : ‖d‖ ≤ M := hd.trans hK
  have haM : ‖(1 : ℂ) + d ^ 2‖ ≤ M := ha.trans hKK
  have hx : ‖x - d * y‖ ≤ M * (‖x‖ + ‖y‖) := by
    calc
      _ ≤ ‖x‖ + ‖d * y‖ := norm_sub_le _ _
      _ ≤ M * ‖x‖ + M * ‖y‖ := by
        rw [norm_mul]
        exact add_le_add (by nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (norm_nonneg x)])
          (mul_le_mul_of_nonneg_right hdM (norm_nonneg y))
      _ = _ := by ring
  have hy : ‖-d * x + (1 + d ^ 2) * y‖ ≤ M * (‖x‖ + ‖y‖) := by
    calc
      _ ≤ ‖-d * x‖ + ‖(1 + d ^ 2) * y‖ := norm_add_le _ _
      _ ≤ M * ‖x‖ + M * ‖y‖ := by
        simp only [norm_mul, norm_neg]
        exact add_le_add (mul_le_mul_of_nonneg_right hdM (norm_nonneg x))
          (mul_le_mul_of_nonneg_right haM (norm_nonneg y))
      _ = _ := by ring
  change ‖x - d * y‖ + ‖-d * x + (1 + d ^ 2) * y‖ ≤ 2 * M * (‖x‖ + ‖y‖)
  linarith

theorem dirichlet_ae_bounded_mul_memLp {μ : Measure ℂ} {a g : ℂ → ℂ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hbound : ∀ᵐ z ∂μ, ‖a z‖ ≤ C)
    (hg : MemLp g 2 μ) : MemLp (fun z => a z * g z) 2 μ := by
  apply hg.of_le_mul (c := C) (ha.mul hg.aestronglyMeasurable)
  filter_upwards [hbound] with z hz
  change ‖a z * g z‖ ≤ C * ‖g z‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

theorem dirichletShiftedFlux_memLp {U : Set ℂ} {f : ℝ → ℝ} {K : NNReal}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hLip : LipschitzWith K f) (h : ℝ) {v : ℂ → ℂ}
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 (volume.restrict U)) (i : Fin 2) :
    MemLp (dirichletShiftedFlux f h v i) 2 (volume.restrict U) := by
  let d : ℂ → ℂ := fun z => dirichletGraphSlope f (z + (h : ℂ))
  have hd : Continuous d := (dirichletGraphSlope_contDiff hf).continuous.comp
    (continuous_id.add continuous_const)
  have hdb (z : ℂ) : ‖d z‖ ≤ (K : ℝ) := by
    simpa only [d, dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip (x₀ := (z + (h : ℂ)).re)
  have hdx : MemLp (dirD v 1) 2 (volume.restrict U) := by
    simpa only [coordDir, Matrix.cons_val_zero] using hg 0
  have hdy : MemLp (dirD v Complex.I) 2 (volume.restrict U) := by
    simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1
  have hdY := dirichlet_bounded_mul_memLp hd.aestronglyMeasurable hdb hdy
  have hndX := dirichlet_bounded_mul_memLp hd.neg.aestronglyMeasurable
    (fun z => by rw [Pi.neg_apply, norm_neg]; exact hdb z) hdx
  have hab (z : ℂ) : ‖(1 : ℂ) + d z ^ 2‖ ≤ 1 + (K : ℝ) ^ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖d z ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖d z‖ ^ 2 := by rw [norm_one, norm_pow]
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hdb z) 2)
  have haY := dirichlet_bounded_mul_memLp
    (continuous_const.add (hd.pow 2)).aestronglyMeasurable hab hdy
  fin_cases i
  · exact hdx.sub hdY
  · exact hndX.add haY

theorem dirichletGraphCoefficientDifference_bounds {A a b h L : ℝ}
    (hh : 0 < h) (hmargin : a + h ≤ A) (hL₀ : 0 ≤ L) {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f)
    (hL : ∀ x ∈ Icc (-A) A, ∀ y ∈ Icc (-A) A,
      |deriv f y - deriv f x| ≤ L * |y - x|) {z : ℂ}
    (hz : z ∈ smoothDirichletHalfBox a b) :
    ‖dirichletTangentialDifference h (dirichletGraphSlope f) z‖ ≤ L ∧
      ‖dirichletTangentialDifference h (fun w => 1 + dirichletGraphSlope f w ^ 2) z‖ ≤
        2 * (K : ℝ) * L := by
  let d := dirichletGraphSlope f z
  let d' := dirichletGraphSlope f (z + (h : ℂ))
  have haA : a < A := by linarith
  have hx : z.re ∈ Icc (-A) A := by
    have hx := abs_lt.mp (hz.1.trans haA)
    exact ⟨hx.1.le, hx.2.le⟩
  have hxh : z.re + h ∈ Icc (-A) A := by
    have hxabs : |z.re + h| < A := (abs_add_le z.re h).trans_lt
      (by
        rw [abs_of_pos hh]
        have hxadd : |z.re| + h < a + h := add_lt_add_of_lt_of_le hz.1 le_rfl
        exact hxadd.trans_le hmargin)
    exact ⟨(abs_lt.mp hxabs).1.le, (abs_lt.mp hxabs).2.le⟩
  have hdd : ‖d' - d‖ ≤ L * h := by
    simpa only [d, d', dirichletGraphSlope, Complex.add_re, Complex.ofReal_re,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      add_sub_cancel_left, abs_of_pos hh] using
      hL z.re hx (z.re + h) hxh
  have hfirst : ‖dirichletTangentialDifference h (dirichletGraphSlope f) z‖ ≤ L := by
    change ‖(d' - d) / (h : ℂ)‖ ≤ L
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    exact (div_le_iff₀ hh).mpr hdd
  have hd (w : ℂ) : ‖dirichletGraphSlope f w‖ ≤ (K : ℝ) := by
    simpa only [dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip (x₀ := w.re)
  have hsum : ‖d' + d‖ ≤ 2 * (K : ℝ) :=
    (norm_add_le _ _).trans (by dsimp [d, d']; linarith [hd z, hd (z + (h : ℂ))])
  have heq : dirichletTangentialDifference h (fun w => 1 + dirichletGraphSlope f w ^ 2) z =
      dirichletTangentialDifference h (dirichletGraphSlope f) z * (d' + d) := by
    change ((1 + d' ^ 2) - (1 + d ^ 2)) / (h : ℂ) = ((d' - d) / (h : ℂ)) * (d' + d)
    ring
  refine ⟨hfirst, ?_⟩
  rw [heq, norm_mul]
  have h := mul_le_mul hfirst hsum (norm_nonneg _) hL₀
  nlinarith

theorem dirichletCoefficientDifferenceFlux_memLp {A a b h L : ℝ}
    (hh : 0 < h) (hmargin : a + h ≤ A) (hL₀ : 0 ≤ L)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal}
    (hLip : LipschitzWith K f)
    (hL : ∀ x ∈ Icc (-A) A, ∀ y ∈ Icc (-A) A,
      |deriv f y - deriv f x| ≤ L * |y - x|) {u : ℂ → ℂ}
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b))) (i : Fin 2) :
    MemLp (dirichletCoefficientDifferenceFlux f h u i) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let V := smoothDirichletHalfBox a b
  let μ := volume.restrict V
  let a₀ : ℂ → ℂ := dirichletTangentialDifference h (dirichletGraphSlope f)
  let a₁ : ℂ → ℂ := dirichletTangentialDifference h (fun z => 1 + dirichletGraphSlope f z ^ 2)
  have hdc := (dirichletGraphSlope_contDiff hf).continuous
  have hac : Continuous a₀ :=
    ((hdc.comp (continuous_id.add continuous_const)).sub hdc).div_const (h : ℂ)
  have hc₁ : Continuous (fun z => (1 : ℂ) + dirichletGraphSlope f z ^ 2) :=
    continuous_const.add (hdc.pow 2)
  have hbc : Continuous a₁ :=
    ((hc₁.comp (continuous_id.add continuous_const)).sub hc₁).div_const (h : ℂ)
  have hbnds : ∀ᵐ z ∂μ, ‖a₀ z‖ ≤ L ∧ ‖a₁ z‖ ≤ 2 * (K : ℝ) * L := by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    exact dirichletGraphCoefficientDifference_bounds hh hmargin hL₀ hLip hL hz
  have hdx : MemLp (dirD u 1) 2 μ := by simpa only [coordDir, Matrix.cons_val_zero] using hg 0
  have hdy : MemLp (dirD u Complex.I) 2 μ := by
    simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1
  have hneg {g : ℂ → ℂ} (hgm : MemLp g 2 μ) : MemLp (fun z => -a₀ z * g z) 2 μ :=
    dirichlet_ae_bounded_mul_memLp hac.neg.aestronglyMeasurable
      (hbnds.mono fun z hz => by simpa only [norm_neg] using hz.1) hgm
  have hlast := dirichlet_ae_bounded_mul_memLp hbc.aestronglyMeasurable
    (hbnds.mono fun _ hz => hz.2) hdy
  fin_cases i
  · exact hneg hdy
  · exact (hneg hdx).add hlast

theorem dirichletCoefficientDifferenceFlux_sq_bound {A a b h L : ℝ}
    (hh : 0 < h) (hmargin : a + h ≤ A) (hL₀ : 0 ≤ L) {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f)
    (hL : ∀ x ∈ Icc (-A) A, ∀ y ∈ Icc (-A) A,
      |deriv f y - deriv f x| ≤ L * |y - x|) (u : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ smoothDirichletHalfBox a b) :
    ‖dirichletCoefficientDifferenceFlux f h u 0 z‖ ^ 2 +
      ‖dirichletCoefficientDifferenceFlux f h u 1 z‖ ^ 2 ≤
        2 * (L * (1 + 2 * (K : ℝ))) ^ 2 *
          (‖dirD u 1 z‖ ^ 2 + ‖dirD u Complex.I z‖ ^ 2) := by
  let D := L * (1 + 2 * (K : ℝ))
  let x := dirD u 1 z
  let y := dirD u Complex.I z
  let c₀ := dirichletCoefficientDifferenceFlux f h u 0 z
  let c₁ := dirichletCoefficientDifferenceFlux f h u 1 z
  obtain ⟨ha, hb⟩ := dirichletGraphCoefficientDifference_bounds hh hmargin hL₀ hLip hL hz
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hc₀ : ‖c₀‖ ≤ L * ‖y‖ := by
    change ‖-dirichletTangentialDifference h (dirichletGraphSlope f) z * y‖ ≤ _
    rw [norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  have hc₁ : ‖c₁‖ ≤ L * ‖x‖ + (2 * (K : ℝ) * L) * ‖y‖ := by
    change ‖-dirichletTangentialDifference h (dirichletGraphSlope f) z * x +
      dirichletTangentialDifference h (fun w => 1 + dirichletGraphSlope f w ^ 2) z * y‖ ≤ _
    calc
      _ ≤ ‖-dirichletTangentialDifference h (dirichletGraphSlope f) z * x‖ +
        ‖dirichletTangentialDifference h (fun w => 1 + dirichletGraphSlope f w ^ 2) z * y‖ :=
          norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul, norm_neg]; gcongr
  have hsum : ‖c₀‖ + ‖c₁‖ ≤ D * (‖x‖ + ‖y‖) := by
    dsimp [D]
    nlinarith [hc₀, hc₁,
      mul_nonneg (show 0 ≤ 2 * (K : ℝ) * L by positivity) (norm_nonneg x)]
  have hsqs := (sq_le_sq₀ (add_nonneg (norm_nonneg c₀) (norm_nonneg c₁))
    (mul_nonneg hD (add_nonneg (norm_nonneg x) (norm_nonneg y)))).mpr hsum
  have hxy : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hc : ‖c₀‖ ^ 2 + ‖c₁‖ ^ 2 ≤ (‖c₀‖ + ‖c₁‖) ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg c₀) (norm_nonneg c₁)]
  calc
    _ ≤ (‖c₀‖ + ‖c₁‖) ^ 2 := hc
    _ ≤ (D * (‖x‖ + ‖y‖)) ^ 2 := hsqs
    _ ≤ D ^ 2 * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hxy (sq_nonneg D)
    _ = _ := by dsimp [D, x, y]; ring

/-- A compact smooth test has a genuine bound for both actual coordinate
derivatives. Keeping the test abstract avoids unfolding a concrete bump
inside the compact-support derivative estimates. -/
theorem exists_dirichlet_smoothTraceTest_gradient_bound (η : smoothTraceTests) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : ℂ, ∀ i : Fin 2, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B := by
  have h₀ := η.property.dirD 1
  have h₁ := η.property.dirD Complex.I
  obtain ⟨B₀, hB₀⟩ := h₀.2.1.exists_bound_of_continuous h₀.1.continuous
  obtain ⟨B₁, hB₁⟩ := h₁.2.1.exists_bound_of_continuous h₁.1.continuous
  let B := max 0 (max B₀ B₁)
  refine ⟨B, le_max_left _ _, ?_⟩
  intro z i
  fin_cases i
  · change ‖dirD (η : ℂ → ℂ) 1 z‖ ≤ B
    exact (hB₀ z).trans ((le_max_left B₀ B₁).trans (le_max_right 0 (max B₀ B₁)))
  · change ‖dirD (η : ℂ → ℂ) Complex.I z‖ ≤ B
    exact (hB₁ z).trans ((le_max_right B₀ B₁).trans (le_max_right 0 (max B₀ B₁)))

/-- The actual complex-valued smooth test associated with a real bump. -/
def dirichletComplexBumpTest (κ : ContDiffBump (0 : ℂ)) : smoothTraceTests :=
  ⟨fun z => (κ z : ℂ),
    ⟨Complex.ofRealCLM.contDiff.comp κ.contDiff,
      κ.hasCompactSupport.comp_left
        (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero,
      subset_univ _⟩⟩

theorem dirichletComplexBumpTest_apply (κ : ContDiffBump (0 : ℂ)) (z : ℂ) :
    dirichletComplexBumpTest κ z = (κ z : ℂ) := rfl

theorem dirichletComplexBumpTest_tsupport_subset (κ : ContDiffBump (0 : ℂ)) :
    tsupport (dirichletComplexBumpTest κ : ℂ → ℂ) ⊆
      closedBall (0 : ℂ) κ.rOut := by
  change tsupport (fun z => (κ z : ℂ)) ⊆ closedBall (0 : ℂ) κ.rOut
  rw [← κ.tsupport_eq]
  exact tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero (κ : ℂ → ℝ)

theorem dirichletComplexBumpTest_norm_le_one (κ : ContDiffBump (0 : ℂ)) (z : ℂ) :
    ‖dirichletComplexBumpTest κ z‖ ≤ 1 := by
  rw [dirichletComplexBumpTest_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (κ.nonneg' z)]
  exact κ.le_one

theorem dirichletComplexBumpTest_eq_one (κ : ContDiffBump (0 : ℂ)) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) κ.rIn) : dirichletComplexBumpTest κ z = 1 := by
  rw [dirichletComplexBumpTest_apply, κ.one_of_mem_closedBall hz, Complex.ofReal_one]

/-- A genuine cutoff equal to one on a smaller boundary half box,
with support avoiding the sides and top, is supplied by an actual
smooth bump. Its derivative bound follows from compact support. -/
theorem exists_dirichlet_boundary_energy_cutoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < a ∧ r < b ∧ ∃ (η : smoothTraceTests) (B : ℝ),
      0 ≤ B ∧ tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} ∧
      (∀ z : ℂ, ‖η z‖ ≤ 1) ∧
      (∀ z : ℂ, ∀ i : Fin 2, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B) ∧
      ∀ z ∈ smoothDirichletHalfBox (r / 2) (r / 2), η z = 1 := by
  let r := min a b / 8
  have hr : 0 < r := div_pos (lt_min ha hb) (by norm_num)
  have h2a : 2 * r < a := by
    dsimp only [r]
    linarith [min_le_left a b, lt_min ha hb]
  have h2b : 2 * r < b := by
    dsimp only [r]
    linarith [min_le_right a b, lt_min ha hb]
  let κ : ContDiffBump (0 : ℂ) := ⟨r, 2 * r, hr, by linarith⟩
  let η := dirichletComplexBumpTest κ
  have hηsupp : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} := by
    intro z hz
    have hzκ : z ∈ closedBall (0 : ℂ) (2 * r) :=
      dirichletComplexBumpTest_tsupport_subset κ hz
    have hzn : ‖z‖ ≤ 2 * r := by simpa only [mem_closedBall, dist_zero_right] using hzκ
    exact ⟨((Complex.abs_re_le_norm z).trans hzn).trans_lt h2a,
      ((le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hzn)).trans_lt h2b⟩
  have hη (z : ℂ) : ‖η z‖ ≤ 1 := by
    exact dirichletComplexBumpTest_norm_le_one κ z
  have hηone (z : ℂ) (hz : z ∈ smoothDirichletHalfBox (r / 2) (r / 2)) : η z = 1 := by
    have hzn : ‖z‖ ≤ r := by
      calc
        _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ r := by rw [abs_of_pos hz.2.1]; linarith [hz.1, hz.2.2]
    exact dirichletComplexBumpTest_eq_one κ
      (by simpa only [mem_closedBall, dist_zero_right] using hzn)
  obtain ⟨B, hB, hg⟩ := exists_dirichlet_smoothTraceTest_gradient_bound η
  exact ⟨r, hr, by linarith, by linarith, η, B, hB, hηsupp, hη, hg, hηone⟩

/-- The actual zero-boundary graph problem has a uniform gradient
difference-quotient bound on a smaller boundary half box. The bound
is derived from the true equation, the genuine coefficient
commutator, the cutoff energy estimate, and first-derivative energy.
No uniform difference estimate is assumed. -/
theorem exists_dirichlet_halfBox_tangential_gradient_energy {A b : ℝ}
    (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiffOn ℝ (⊤ : ℕ∞) G (smoothDirichletHalfBox A b))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hGx : MemLp (dirD G 1) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    ∃ ρ E : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧ 0 ≤ E ∧
      ∀ h : ℝ, h ∈ Ioo 0 (A / 4) →
        (∫ z in smoothDirichletHalfBox ρ ρ,
          ‖dirD (dirichletTangentialDifference h u) 1 z‖ ^ 2 +
            ‖dirD (dirichletTangentialDifference h u) Complex.I z‖ ^ 2) ≤ E := by
  let U := smoothDirichletHalfBox A b
  let V := smoothDirichletHalfBox (A / 2) b
  have hVsub : V ⊆ U := fun z hz => ⟨hz.1.trans (by linarith), hz.2⟩
  have hηdata := exists_dirichlet_boundary_energy_cutoff (show 0 < A / 2 by linarith) hb
  obtain ⟨r, hr, hra, hrb, η, B, hB, hηsupp, hη, hηgrad, hηone⟩ := hηdata
  obtain ⟨L, hL₀, hL⟩ := exists_dirichletGraphSlope_interval_lipschitz hA hf
  let M := 2 * (1 + (K : ℝ) ^ 2)
  let D := 2 * (L * (1 + 2 * (K : ℝ))) ^ 2
  let eg := ∫ z in U, ‖dirD G 1 z‖ ^ 2
  let ex := ∫ z in U, ‖dirD u 1 z‖ ^ 2
  let eu := ∫ z in U, ‖dirD u 1 z‖ ^ 2 + ‖dirD u Complex.I z‖ ^ 2
  let E := 2 * M * (eg + (4 * M + 2 * B ^ 2) * (D * eu) +
    (32 * B ^ 2 * M ^ 3 + 2) * ex)
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have heg : 0 ≤ eg := integral_nonneg fun z => sq_nonneg _
  have hex : 0 ≤ ex := integral_nonneg fun z => sq_nonneg _
  have heu : 0 ≤ eu := integral_nonneg fun z => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hux : MemLp (dirD u 1) 2 (volume.restrict U) := by
    simpa only [coordDir, Matrix.cons_val_zero] using hg 0
  have huy : MemLp (dirD u Complex.I) 2 (volume.restrict U) := by
    simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1
  have hgui : IntegrableOn (fun z => ‖dirD u 1 z‖ ^ 2 + ‖dirD u Complex.I z‖ ^ 2) U :=
    (hux.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      (huy.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  refine ⟨r / 2, E, by linarith, by linarith, by linarith, hE, ?_⟩
  intro h hh
  have hmargin : A / 2 + |h| ≤ A := by rw [abs_of_pos hh.1]; linarith [hh.2]
  have hmargin' : A / 2 + h < A := by linarith [hh.2]
  let v := dirichletTangentialDifference h u
  let F : Fin 2 → ℂ → ℂ := dirichletShiftedFlux f h v
  let C : Fin 2 → ℂ → ℂ := dirichletCoefficientDifferenceFlux f h u
  let Q := dirichletTangentialDifference h G
  have hvc := dirichletTangentialDifference_continuousOn hmargin hc
  have hvs := dirichletTangentialDifference_contDiffOn hmargin hs
  have hvz (x : ℝ) (hx : |x| < A / 2) : v (x : ℂ) = 0 :=
    dirichletTangentialDifference_zero_bottom hmargin hz hx
  have hvm := dirichletTangentialDifference_memLp hmargin hm
  have hvg (i : Fin 2) : MemLp (dirD v (coordDir i)) 2 (volume.restrict V) :=
    dirichletTangentialDifference_gradient_memLp hmargin hs (hg i)
  have hug (i : Fin 2) : MemLp (dirD u (coordDir i)) 2 (volume.restrict V) :=
    (hg i).mono_measure (Measure.restrict_mono_set volume hVsub)
  have hFm (i : Fin 2) : MemLp (F i) 2 (volume.restrict V) :=
    dirichletShiftedFlux_memLp hf hLip h hvg i
  have hCm (i : Fin 2) : MemLp (C i) 2 (volume.restrict V) :=
    dirichletCoefficientDifferenceFlux_memLp hh.1 hmargin'.le hL₀ hf hLip hL hug i
  have hQm := dirichletTangentialDifference_memLp hmargin hG
  have hvenergy : (∫ z in V, ‖v z‖ ^ 2) ≤ ex :=
    dirichlet_halfBox_tangential_difference_energy_le (by linarith) hb hh.1 hmargin'
      hs hm hux
  have hQenergy : (∫ z in V, ‖Q z‖ ^ 2) ≤ eg :=
    dirichlet_halfBox_tangential_difference_energy_le (by linarith) hb hh.1 hmargin'
      hGs hG hGx
  have hCenergy : (∫ z in V, ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) ≤ D * eu := by
    have hCi := ((hCm 0).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      ((hCm 1).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    have hui := hgui.mono_set hVsub
    have hbnd : (∫ z in V, ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) ≤
        ∫ z in V, D * (‖dirD u 1 z‖ ^ 2 + ‖dirD u Complex.I z‖ ^ 2) := by
      apply integral_mono_ae hCi (hui.const_mul D)
      filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox (A / 2) b).measurableSet]
        with z hzV
      exact dirichletCoefficientDifferenceFlux_sq_bound hh.1 hmargin'.le hL₀ hLip hL u hzV
    rw [integral_const_mul] at hbnd
    exact hbnd.trans (mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hgui
        (Eventually.of_forall fun z => add_nonneg (sq_nonneg _) (sq_nonneg _))
        hVsub.eventuallyLE) hD)
  have hweak (φ : ℂ → ℂ) (hφ : TestFunction V φ) :
      (∫ z in V, ∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z) =
        ∫ z in V, Q z * φ z :=
    dirichletTangentialDifference_weak_equation hh.1.ne' hmargin hf hs hstrong hφ
  have henergy := dirichlet_localized_boundary_energy_bound hb
    hM hB η hηsupp hη hηgrad hvc hvs hvz hvm hvg hFm hCm hQm
    (fun z _ => dirichletShiftedFlux_coercive hLip h v z)
    (fun z _ => dirichletShiftedFlux_norm_sum_bound hLip h v z) hweak
  have hJbound : (∫ z in V,
      ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)) ≤ E := by
    have hbnd := henergy.trans (add_le_add
      (add_le_add hQenergy (mul_le_mul_of_nonneg_left hCenergy
        (show 0 ≤ 4 * M + 2 * B ^ 2 by positivity)))
      (mul_le_mul_of_nonneg_left hvenergy
        (show 0 ≤ 32 * B ^ 2 * M ^ 3 + 2 by positivity)))
    have h := (div_le_iff₀ (show 0 < 2 * M by positivity)).mp hbnd
    dsimp only [E]
    nlinarith
  let W := smoothDirichletHalfBox (r / 2) (r / 2)
  have hWsub : W ⊆ V := fun z hzW =>
    ⟨hzW.1.trans (by linarith), hzW.2.1, hzW.2.2.trans (by linarith)⟩
  have hηx := dirichlet_localized_memLp η
    (show MemLp (dirD v 1) 2 (volume.restrict V) by
      simpa only [coordDir, Matrix.cons_val_zero] using hvg 0)
  have hηy := dirichlet_localized_memLp η
    (show MemLp (dirD v Complex.I) 2 (volume.restrict V) by
      simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hvg 1)
  have hJi : IntegrableOn (fun z =>
      ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)) V := by
    apply ((hηx.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      (hηy.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).congr
    filter_upwards with z
    change ‖η z * dirD v 1 z‖ ^ 2 + ‖η z * dirD v Complex.I z‖ ^ 2 =
      ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)
    simp only [norm_mul, mul_pow]
    ring
  have hW : (∫ z in W, ‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) =
      ∫ z in W, ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) := by
    apply setIntegral_congr_fun (isOpen_smoothDirichletHalfBox _ _).measurableSet
    intro z hzW
    change ‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2 =
      ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)
    rw [hηone z hzW, norm_one]
    simp only [one_pow, one_mul]
  rw [hW]
  exact (setIntegral_mono_set hJi
    (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))) hWsub.eventuallyLE).trans hJbound

/-- The Fatou step for actual tangential difference quotients.
The uniform energy estimate is used to bound the genuine L²
seminorm; the limit is the actual interior first derivative of the
first derivative, not a separately asserted weak representative. -/
theorem dirichlet_tangential_second_memLp_of_gradient_energy {U W : Set ℂ}
    (hU : IsOpen U) (hW : MeasurableSet W) (hWU : W ⊆ U) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u U) {ε E : ℝ} (hε : 0 < ε)
    (hmem : ∀ h ∈ Ioo (0 : ℝ) ε, ∀ i : Fin 2,
      MemLp (dirD (dirichletTangentialDifference h u) (coordDir i)) 2 (volume.restrict W))
    (henergy : ∀ h ∈ Ioo (0 : ℝ) ε,
      (∫ z in W, ‖dirD (dirichletTangentialDifference h u) 1 z‖ ^ 2 +
        ‖dirD (dirichletTangentialDifference h u) Complex.I z‖ ^ 2) ≤ E) :
    ∀ i : Fin 2, MemLp (dirD (dirD u (coordDir i)) 1) 2 (volume.restrict W) := by
  intro i
  let μ := volume.restrict W
  let f : ℝ → ℂ → ℂ := fun h => dirD (dirichletTangentialDifference h u) (coordDir i)
  let g : ℂ → ℂ := dirD (dirD u (coordDir i)) 1
  have hbound : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), eLpNorm (f h) 2 μ ≤
      ENNReal.ofReal (Real.sqrt E) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with h hh hhε
    have hhI : h ∈ Ioo (0 : ℝ) ε := ⟨hh, hhε⟩
    have hm := hmem h hhI i
    have hm₀ : MemLp (dirD (dirichletTangentialDifference h u) 1) 2 μ := by
      simpa only [coordDir, Matrix.cons_val_zero] using hmem h hhI 0
    have hm₁ : MemLp (dirD (dirichletTangentialDifference h u) Complex.I) 2 μ := by
      simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hmem h hhI 1
    have hle (z : ℂ) : ‖f h z‖ ^ 2 ≤
        ‖dirD (dirichletTangentialDifference h u) 1 z‖ ^ 2 +
          ‖dirD (dirichletTangentialDifference h u) Complex.I z‖ ^ 2 := by
      fin_cases i
      · change ‖dirD (dirichletTangentialDifference h u) 1 z‖ ^ 2 ≤ _
        exact le_add_of_nonneg_right (sq_nonneg _)
      · change ‖dirD (dirichletTangentialDifference h u) Complex.I z‖ ^ 2 ≤ _
        exact le_add_of_nonneg_left (sq_nonneg _)
    have hi := integral_mono_ae (hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      ((hm₀.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
        (hm₁.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)))
      (Eventually.of_forall hle)
    have hEi : (∫ z, ‖f h z‖ ^ 2 ∂μ) ≤ E := hi.trans (henergy h hhI)
    apply (ENNReal.toReal_le_toReal hm.eLpNorm_ne_top (by simp)).mp
    rw [dirichlet_eLpNorm_toReal_eq_sqrt_energy hm,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg E)]
    exact Real.sqrt_le_sqrt hEi
  have hmeas (h : ℝ) : AEStronglyMeasurable (f h) μ :=
    (measurable_fderiv_apply_const ℝ (dirichletTangentialDifference h u) (coordDir i)).aestronglyMeasurable
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun h : ℝ => f h z) (𝓝[>] (0 : ℝ)) (𝓝 (g z)) := by
    filter_upwards [ae_restrict_mem hW] with z hzW
    have hzU := hWU hzW
    let v := dirD u (coordDir i)
    have hvs := dirichlet_contDiffOn_dirD hU hs (coordDir i)
    have hv := ((hvs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)).hasFDerivAt
    have hv' : HasFDerivAt v (fderiv ℝ v z) (z + (0 : ℂ)) := by
      simpa only [add_zero] using hv
    have hL : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 (0 : ℝ) :=
      ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add z
    have hvL : HasDerivAt (fun t : ℝ => v (z + (t : ℂ))) (dirD v 1 z) (0 : ℝ) := by
      simpa only [Complex.ofReal_zero, add_zero, Function.comp_def, dirD] using
        hv'.comp_hasDerivAt (0 : ℝ) hL
    have hvlim : Tendsto (fun h : ℝ => dirichletTangentialDifference h v z)
        (𝓝[>] (0 : ℝ)) (𝓝 (dirD v 1 z)) := by
      simpa only [zero_add, Complex.ofReal_zero, add_zero, Complex.real_smul,
        Complex.ofReal_inv, dirichletTangentialDifference, div_eq_mul_inv, mul_comm] using
        hvL.tendsto_slope_zero_right
    have hzshift : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), z + (h : ℂ) ∈ U := by
      have ht : Tendsto (fun h : ℝ => z + (h : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
        have hc : ContinuousAt (fun h : ℝ => z + (h : ℂ)) (0 : ℝ) :=
          ((continuous_const : Continuous (fun _ : ℝ => z)).add
            Complex.ofRealCLM.continuous).continuousAt
        simpa only [Complex.ofReal_zero, add_zero] using
          hc.tendsto.mono_left nhdsWithin_le_nhds
      exact ht.eventually (hU.mem_nhds hzU)
    have heq : (fun h : ℝ => dirichletTangentialDifference h v z)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun h : ℝ => f h z) := by
      filter_upwards [hzshift] with h hzhU
      exact (dirichletTangentialDifference_dirD
        ((hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp))
        ((hs.contDiffAt (hU.mem_nhds hzhU)).differentiableAt (by simp)) (coordDir i)).symm
    exact hvlim.congr' heq
  have hgmeas : AEStronglyMeasurable g μ :=
    (measurable_fderiv_apply_const ℝ (dirD u (coordDir i)) 1).aestronglyMeasurable
  exact lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto hbound hmeas hgmeas hlim) (by simp)

theorem dirichlet_dirD_comm {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u U) {z : ℂ} (hz : z ∈ U) (v w : ℂ) :
    dirD (dirD u v) w z = dirD (dirD u w) v z := by
  have hu := hs.contDiffAt (hU.mem_nhds hz)
  have hd : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiableAt (by simp)
  have hD (v w : ℂ) : dirD (dirD u v) w z = fderiv ℝ (fderiv ℝ u) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ u x v) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [hD, hD]
  exact (hu.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).eq w v

/-- Actual tangential H² follows from the proved graph energy
estimate and Fatou. The mixed derivative is put in the order used
by normal recovery, by true smooth interior symmetry. -/
theorem exists_dirichlet_halfBox_tangential_second_memLp {A b : ℝ}
    (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiffOn ℝ (⊤ : ℕ∞) G (smoothDirichletHalfBox A b))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hGx : MemLp (dirD G 1) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      MemLp (dirD (dirD u 1) 1) 2 (volume.restrict (smoothDirichletHalfBox ρ ρ)) ∧
      MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict (smoothDirichletHalfBox ρ ρ)) := by
  obtain ⟨ρ, E, hρ, hρA, hρb, _, henergy⟩ :=
    exists_dirichlet_halfBox_tangential_gradient_energy hA hb hf hLip hc hs hz hm hg
      hstrong hGs hG hGx
  let U := smoothDirichletHalfBox A b
  let V := smoothDirichletHalfBox (A / 2) b
  let W := smoothDirichletHalfBox ρ ρ
  have hWsub : W ⊆ V := fun z hz => ⟨hz.1.trans hρA, hz.2.1, hz.2.2.trans hρb⟩
  have hWU : W ⊆ U := fun z hz => ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩
  have hmem (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) (A / 4)) (i : Fin 2) :
      MemLp (dirD (dirichletTangentialDifference h u) (coordDir i)) 2 (volume.restrict W) := by
    have hmV := dirichletTangentialDifference_gradient_memLp
      (show A / 2 + |h| ≤ A by rw [abs_of_pos hh.1]; linarith [hh.2]) hs (hg i)
    exact hmV.mono_measure (Measure.restrict_mono_set volume hWsub)
  have h2 := dirichlet_tangential_second_memLp_of_gradient_energy
    (isOpen_smoothDirichletHalfBox A b) (isOpen_smoothDirichletHalfBox ρ ρ).measurableSet
    hWU hs (show 0 < A / 4 by linarith) hmem henergy
  have hxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict W) := by
    simpa only [coordDir, Matrix.cons_val_zero] using h2 0
  have hxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict W) := by
    have hyx : MemLp (dirD (dirD u Complex.I) 1) 2 (volume.restrict W) := by
      simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using h2 1
    apply hyx.ae_eq
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox ρ ρ).measurableSet]
      with z hzW
    exact dirichlet_dirD_comm (isOpen_smoothDirichletHalfBox A b) hs (hWU hzW) Complex.I 1
  exact ⟨ρ, hρ, hρA, hρb, hxx, hxy⟩

/-- Genuine tangential second-derivative energy for the original
physical conformal Green remainder at every smooth boundary point.
The forcing and its first derivative are pulled back from the actual
compact smooth datum. No boundary H² or uniform estimate is supplied
as an additional original-map hypothesis. -/
theorem exists_riemannMapping_flattened_tangential_second_memLp {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (ρ : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < ρ ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       let W := smoothDirichletHalfBox ρ ρ
       MapsTo Ψ W Ω ∧ ContinuousOn u (smoothDirichletClosedHalfBox ρ ρ) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) u W ∧
       (∀ x : ℝ, |x| < ρ → u (x : ℂ) = 0) ∧
       MemLp u 2 (volume.restrict W) ∧
       (∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2 (volume.restrict W)) ∧
       MemLp (dirD (dirD u 1) 1) 2 (volume.restrict W) ∧
       MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict W)) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hmap, hu, hs, hz, v, hv, hgv⟩ :=
    exists_riemannMapping_flattened_zero_boundary_h1 hb hS hsc F hF hinj himage hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  let G := lap (d : ℂ → ℂ) ∘ Ψ
  let U := smoothDirichletHalfBox A b
  have hvm : MemLp u 2 (volume.restrict U) :=
    (Lp.memLp (h1Value U v)).ae_eq hv
  have hvg (i : Fin 2) : MemLp (dirD u (coordDir i)) 2 (volume.restrict U) :=
    (Lp.memLp (h1Gradient U i v)).ae_eq (hgv i)
  have hd := d.property.lap
  have hforcing := smoothDirichletGraphChart_pullback_memLp isOpen_univ
    (isOpen_smoothDirichletHalfBox A b) p c hc hc₁ hf hLip
    (subset_univ _) hd.1.contDiffOn (hd.memLp' 2)
    (fun i => (hd.dirD (coordDir i)).memLp' 2)
  have hGs : ContDiffOn ℝ (⊤ : ℕ∞) G U :=
    (hd.1.comp (smoothDirichletGraphChart_contDiff p c hc hf)).contDiffOn
  have hG : MemLp G 2 (volume.restrict U) := hforcing.1
  have hGx : MemLp (dirD G 1) 2 (volume.restrict U) := by
    simpa only [G, Function.comp_def, coordDir, Matrix.cons_val_zero] using hforcing.2 0
  have hstrong (z : ℂ) (hzU : z ∈ U) : dirichletFlattenedDivergence f u z = -G z := by
    rw [dirichletFlattenedDivergence_pullback hS.1.1 p c hc hc₁ hf
      (riemannMappingDirichletRemainder_contDiffOn hb hS hsc F hF hinj himage d) (hmap hzU)]
    exact riemannMappingDirichletRemainder_lap hb hS hsc F hF hinj himage d (hmap hzU)
  obtain ⟨ρ, hρ, hρA, hρb, hxx, hxy⟩ :=
    exists_dirichlet_halfBox_tangential_second_memLp hA hb₀ hf hLip hu hs hz hvm hvg
      hstrong hGs hG hGx
  let W := smoothDirichletHalfBox ρ ρ
  have hWU : W ⊆ U := fun z hzW =>
    ⟨hzW.1.trans (by linarith), hzW.2.1, hzW.2.2.trans hρb⟩
  have hclosed : smoothDirichletClosedHalfBox ρ ρ ⊆ smoothDirichletClosedHalfBox A b := by
    intro z hzW
    exact ⟨hzW.1.trans (by linarith), hzW.2.1, hzW.2.2.trans hρb.le⟩
  refine ⟨d, c, hc, f, hf, K, ρ, hc₁, hLip, hf₀, hρ, ?_⟩
  exact ⟨fun z hzW => hmap (hWU hzW), hu.mono hclosed, hs.mono hWU,
    fun x hx => hz x (hx.trans (by linarith)),
    hvm.mono_measure (Measure.restrict_mono_set volume hWU),
    fun i => (hvg i).mono_measure (Measure.restrict_mono_set volume hWU), hxx, hxy⟩

end PolyaNeumann

end
