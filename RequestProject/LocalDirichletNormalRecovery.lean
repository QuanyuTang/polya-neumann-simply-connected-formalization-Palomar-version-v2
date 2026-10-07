module

public import RequestProject.LocalDirichletFlattenedEquation
public import RequestProject.RiemannMappingEnergy
public import RequestProject.LpBoundedMultiplier
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
Recovery of the actual normal second derivative in a smooth graph chart.
The matrix is `[[1,-f′],[-f′,1+f′²]]`. The existing physical equation has
`div(A∇u) = -G`, hence the recovered numerator is
`-G + f′′ Dy u + 2 f′ Dxy u - Dxx u`. Tangential second derivatives may be
supplied as genuine L² data; no normal second derivative or recovery identity
is assumed. Interior smoothness and localized compact-test integration by
parts turn the recovered L² derivative into the actual weak derivative.
This module is part of the verified dependency chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

theorem dirichlet_normal_dirD_add {a b : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w + b w) v z = dirD a v z + dirD b v z := by
  change fderiv ℝ (fun w => a w + b w) z v = _
  rw [fderiv_fun_add ha hb]
  rfl

theorem dirichlet_normal_dirD_sub {a b : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w - b w) v z = dirD a v z - dirD b v z := by
  change fderiv ℝ (fun w => a w - b w) z v = _
  rw [fderiv_fun_sub ha hb]
  rfl

theorem dirichlet_normal_dirD_mul {a b : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w * b w) v z = dirD a v z * b z + a z * dirD b v z := by
  change fderiv ℝ (fun w => a w * b w) z v = _
  rw [fderiv_fun_mul ha hb]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change a z * dirD b v z + b z * dirD a v z = _
  ring

/-- The actual graph curvature coefficient in complex scalar form. -/
def dirichletGraphCurvature (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ((deriv (deriv f) z.re : ℝ) : ℂ)

theorem dirichletGraphCurvature_continuous {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (dirichletGraphCurvature f) := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  exact Complex.continuous_ofReal.comp
    (((contDiff_infty_iff_deriv.mp hd).2.continuous).comp Complex.continuous_re)

theorem dirD_dirichletGraphSlope_one {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dirD (dirichletGraphSlope f) 1 z = dirichletGraphCurvature f z := by
  have hd := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    (hd.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z 1 = _
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.reCLM_apply, Complex.one_re, smul_eq_mul, mul_one,
    Complex.ofRealCLM_apply, dirichletGraphCurvature]

/-- Mixed derivative symmetry is derived at each genuine smooth interior
point; it is not an assumed weak second-derivative identity. -/
theorem dirichlet_normal_dirD_comm {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) {z : ℂ} (hz : z ∈ U) (v w : ℂ) :
    dirD (dirD u v) w z = dirD (dirD u w) v z := by
  have hs := hu.contDiffAt (hU.mem_nhds hz)
  have hd : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hs.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiableAt (by simp)
  have hv : fderiv ℝ (dirD u v) z w = fderiv ℝ (fderiv ℝ u) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ u x v) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  have hw : fderiv ℝ (dirD u w) z v = fderiv ℝ (fderiv ℝ u) z v w := by
    change fderiv ℝ (fun x => fderiv ℝ u x w) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  change fderiv ℝ (dirD u v) z w = fderiv ℝ (dirD u w) z v
  rw [hv, hw]
  exact (hs.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).eq w v

theorem dirichletFlattenedDivergence_normal_expansion {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) {z : ℂ} (hz : z ∈ U) :
    dirichletFlattenedDivergence f u z =
      dirD (dirD u 1) 1 z - dirichletGraphCurvature f z * dirD u Complex.I z -
        2 * dirichletGraphSlope f z * dirD (dirD u 1) Complex.I z +
        (1 + dirichletGraphSlope f z ^ 2) * dirD (dirD u Complex.I) Complex.I z := by
  let d := dirichletGraphSlope f
  let x := dirD u 1
  let y := dirD u Complex.I
  have hd : DifferentiableAt ℝ d z :=
    (dirichletGraphSlope_contDiff hf).differentiable (by simp) z
  have hx : DifferentiableAt ℝ x z :=
    ((dirichlet_contDiffOn_dirD hU hu 1).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hz)
  have hy : DifferentiableAt ℝ y z :=
    ((dirichlet_contDiffOn_dirD hU hu Complex.I).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hz)
  have hdx : dirD d 1 z = dirichletGraphCurvature f z := dirD_dirichletGraphSlope_one hf z
  have hdy : dirD d Complex.I z = 0 := dirD_dirichletGraphSlope_I hf z
  have haI : dirD (fun w => (1 : ℂ) + d w ^ 2) Complex.I z = 0 := by
    have heq : (fun w => (1 : ℂ) + d w ^ 2) = fun w => 1 + d w * d w := by
      funext w
      rw [pow_two]
    rw [heq, dirichlet_normal_dirD_add (a := fun _ => (1 : ℂ))
      (b := fun w => d w * d w) (differentiableAt_const 1) (hd.mul hd),
      dirichlet_normal_dirD_mul (a := d) (b := d) hd hd, hdy]
    simp [dirD]
  have hflux₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
      dirD x 1 z - (dirichletGraphCurvature f z * y z + d z * dirD y 1 z) := by
    change dirD (fun w => x w - d w * y w) 1 z = _
    rw [dirichlet_normal_dirD_sub (a := x) (b := fun w => d w * y w)
      hx (hd.mul hy), dirichlet_normal_dirD_mul (a := d) (b := y) hd hy, hdx]
  have hflux₁ : dirD (dirichletFlattenedFlux f u 1) Complex.I z =
      -d z * dirD x Complex.I z + (1 + d z ^ 2) * dirD y Complex.I z := by
    have heq : dirichletFlattenedFlux f u 1 =
        fun w => (1 + d w ^ 2) * y w - d w * x w := by
      funext w
      change -d w * x w + (1 + d w ^ 2) * y w = _
      ring
    rw [heq, dirichlet_normal_dirD_sub
      (a := fun w => (1 + d w ^ 2) * y w) (b := fun w => d w * x w)
      (((differentiableAt_const (1 : ℂ)).add (hd.pow 2)).mul hy) (hd.mul hx),
      dirichlet_normal_dirD_mul (a := fun w => 1 + d w ^ 2) (b := y)
        ((differentiableAt_const 1).add (hd.pow 2)) hy,
      dirichlet_normal_dirD_mul (a := d) (b := x) hd hx, haI, hdy]
    ring
  rw [dirichletFlattenedDivergence, hflux₀, hflux₁]
  change dirD (dirD u 1) 1 z -
      (dirichletGraphCurvature f z * dirD u Complex.I z +
        dirichletGraphSlope f z * dirD (dirD u Complex.I) 1 z) +
      (-dirichletGraphSlope f z * dirD (dirD u 1) Complex.I z +
        (1 + dirichletGraphSlope f z ^ 2) * dirD (dirD u Complex.I) Complex.I z) = _
  rw [dirichlet_normal_dirD_comm hU hu hz Complex.I 1]
  ring

/-- The reciprocal actual normal coefficient, with a genuine global bound. -/
def dirichletNormalCoefficientInverse (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal ((1 + (deriv f z.re) ^ 2 : ℝ)⁻¹)

theorem dirichletNormalCoefficientInverse_norm_le_one (f : ℝ → ℝ) (z : ℂ) :
    ‖dirichletNormalCoefficientInverse f z‖ ≤ 1 := by
  have hpos : 0 < 1 + (deriv f z.re) ^ 2 := by positivity
  rw [dirichletNormalCoefficientInverse, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact (inv_le_one₀ hpos).mpr (by nlinarith [sq_nonneg (deriv f z.re)])

theorem dirichletNormalCoefficientInverse_continuous {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (dirichletNormalCoefficientInverse f) := by
  have hd : Continuous (fun z : ℂ => deriv f z.re) :=
    (contDiff_infty_iff_deriv.mp hf).2.continuous.comp Complex.continuous_re
  have hi : Continuous (fun z : ℂ => (1 + (deriv f z.re) ^ 2 : ℝ)⁻¹) :=
    (((continuous_const : Continuous (fun _ : ℂ => (1 : ℝ))).add (hd.pow 2)).inv₀
      (fun z => show (1 + (deriv f z.re) ^ 2 : ℝ) ≠ 0 from
        (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg (deriv f z.re))).ne'))
  exact Complex.continuous_ofReal.comp hi

theorem dirichletNormalCoefficientInverse_mul (f : ℝ → ℝ) (z : ℂ) :
    dirichletNormalCoefficientInverse f z * (1 + dirichletGraphSlope f z ^ 2) = 1 := by
  have hpos : (1 + (deriv f z.re) ^ 2 : ℝ) ≠ 0 := by positivity
  have heq : (1 + dirichletGraphSlope f z ^ 2 : ℂ) =
      ((1 + (deriv f z.re) ^ 2 : ℝ) : ℂ) := by
    simp [dirichletGraphSlope]
  rw [heq, dirichletNormalCoefficientInverse, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hpos, Complex.ofReal_one]

theorem dirichlet_normal_derivative_recovery {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    {z : ℂ} (hz : z ∈ U) :
    dirD (dirD u Complex.I) Complex.I z = dirichletNormalCoefficientInverse f z *
      (-G z + dirichletGraphCurvature f z * dirD u Complex.I z +
        2 * dirichletGraphSlope f z * dirD (dirD u 1) Complex.I z -
        dirD (dirD u 1) 1 z) := by
  have he := dirichletFlattenedDivergence_normal_expansion hU hf hu hz
  rw [hstrong z hz] at he
  have hnum : -G z + dirichletGraphCurvature f z * dirD u Complex.I z +
      2 * dirichletGraphSlope f z * dirD (dirD u 1) Complex.I z - dirD (dirD u 1) 1 z =
      (1 + dirichletGraphSlope f z ^ 2) * dirD (dirD u Complex.I) Complex.I z := by
    linear_combination he
  rw [hnum, ← mul_assoc, dirichletNormalCoefficientInverse_mul, one_mul]

/-- A bounded coefficient acts on the genuine `L² U` space. This small
barrier prevents proofs about normal derivatives from unfolding H¹ jets. -/
def dirichletCoefficientL2Multiplier (U : Set ℂ) (a : ℂ → ℂ)
    (ha : Continuous a) {C : ℝ} (hbound : ∀ᵐ z ∂volume.restrict U, ‖a z‖ ≤ C) :
    L2 U →L[ℂ] L2 U :=
  lpBoundedMultiplier a ha.aestronglyMeasurable hbound

theorem dirichletCoefficientL2Multiplier_ae (U : Set ℂ) (a : ℂ → ℂ)
    (ha : Continuous a) {C : ℝ} (hbound : ∀ᵐ z ∂volume.restrict U, ‖a z‖ ≤ C)
    (v : L2 U) :
    (dirichletCoefficientL2Multiplier U a ha hbound v : ℂ → ℂ)
      =ᵐ[volume.restrict U] fun z => a z * v z :=
  lpBoundedMultiplier_ae a ha.aestronglyMeasurable hbound v

theorem norm_dirichletCoefficientL2Multiplier_le (U : Set ℂ) (a : ℂ → ℂ)
    (ha : Continuous a) {C : ℝ} (hbound : ∀ᵐ z ∂volume.restrict U, ‖a z‖ ≤ C)
    (v : L2 U) : ‖dirichletCoefficientL2Multiplier U a ha hbound v‖ ≤ C * ‖v‖ := by
  change ‖lpBoundedMulLin a ha.aestronglyMeasurable hbound v‖ ≤ _
  exact norm_lpBoundedMulLin_le a ha.aestronglyMeasurable hbound v

theorem dirichlet_normal_numerator_ae {U : Set ℂ} (G Y XX XY KY SXY : L2 U)
    (d κ : ℂ → ℂ)
    (hK : (KY : ℂ → ℂ) =ᵐ[volume.restrict U] fun z => κ z * Y z)
    (hS : (SXY : ℂ → ℂ) =ᵐ[volume.restrict U] fun z => d z * XY z) :
    ((-G + KY + (2 : ℂ) • SXY - XX : L2 U) : ℂ → ℂ)
      =ᵐ[volume.restrict U] fun z => -G z + κ z * Y z + 2 * d z * XY z - XX z := by
  filter_upwards [Lp.coeFn_neg G, Lp.coeFn_add (-G) KY,
    Lp.coeFn_smul (2 : ℂ) SXY, Lp.coeFn_add (-G + KY) ((2 : ℂ) • SXY),
    Lp.coeFn_sub (-G + KY + (2 : ℂ) • SXY) XX, hK, hS]
    with z hn ha hs hb hc hk hd
  simp only [hc, hb, ha, hn, hs, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, hk, hd]
  ring

/-- The recovered derivative is an actual L² class built from the forcing,
the original first derivative, and the two genuine tangential derivatives. -/
def dirichletNormalRecoveryL2 (U : Set ℂ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M)
    (G Y XX XY : L2 U) : L2 U :=
  dirichletCoefficientL2Multiplier U (dirichletNormalCoefficientInverse f)
    (dirichletNormalCoefficientInverse_continuous hf)
    (Filter.Eventually.of_forall (dirichletNormalCoefficientInverse_norm_le_one f))
    (-G + dirichletCoefficientL2Multiplier U (dirichletGraphCurvature f)
      (dirichletGraphCurvature_continuous hf) hCurvature Y +
      (2 : ℂ) • dirichletCoefficientL2Multiplier U (dirichletGraphSlope f)
        (dirichletGraphSlope_contDiff hf).continuous hSlope XY - XX)

theorem dirichletNormalRecoveryL2_ae (U : Set ℂ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M)
    (G Y XX XY : L2 U) :
    (dirichletNormalRecoveryL2 U f hf hSlope hCurvature G Y XX XY : ℂ → ℂ)
      =ᵐ[volume.restrict U] fun z => dirichletNormalCoefficientInverse f z *
        (-G z + dirichletGraphCurvature f z * Y z +
          2 * dirichletGraphSlope f z * XY z - XX z) := by
  let K := dirichletCoefficientL2Multiplier U (dirichletGraphCurvature f)
    (dirichletGraphCurvature_continuous hf) hCurvature
  let S := dirichletCoefficientL2Multiplier U (dirichletGraphSlope f)
    (dirichletGraphSlope_contDiff hf).continuous hSlope
  have hnum := dirichlet_normal_numerator_ae G Y XX XY (K Y) (S XY)
    (dirichletGraphSlope f) (dirichletGraphCurvature f)
    (dirichletCoefficientL2Multiplier_ae U _ _ hCurvature Y)
    (dirichletCoefficientL2Multiplier_ae U _ _ hSlope XY)
  have hinv := dirichletCoefficientL2Multiplier_ae U
    (dirichletNormalCoefficientInverse f) (dirichletNormalCoefficientInverse_continuous hf)
    (Filter.Eventually.of_forall (dirichletNormalCoefficientInverse_norm_le_one f))
    (-G + K Y + (2 : ℂ) • S XY - XX)
  filter_upwards [hinv, hnum] with z hi hn
  change (dirichletCoefficientL2Multiplier U _ _ _
    (-G + K Y + (2 : ℂ) • S XY - XX)) z = _
  rw [hi, hn]

theorem norm_dirichletNormalRecoveryL2_le (U : Set ℂ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M)
    (G Y XX XY : L2 U) :
    ‖dirichletNormalRecoveryL2 U f hf hSlope hCurvature G Y XX XY‖ ≤
      ‖G‖ + M * ‖Y‖ + 2 * L * ‖XY‖ + ‖XX‖ := by
  let K := dirichletCoefficientL2Multiplier U (dirichletGraphCurvature f)
    (dirichletGraphCurvature_continuous hf) hCurvature
  let S := dirichletCoefficientL2Multiplier U (dirichletGraphSlope f)
    (dirichletGraphSlope_contDiff hf).continuous hSlope
  have hK : ‖K Y‖ ≤ M * ‖Y‖ := norm_dirichletCoefficientL2Multiplier_le U _ _ hCurvature Y
  have hS : ‖S XY‖ ≤ L * ‖XY‖ := norm_dirichletCoefficientL2Multiplier_le U _ _ hSlope XY
  have hi : ‖dirichletNormalRecoveryL2 U f hf hSlope hCurvature G Y XX XY‖ ≤
      ‖-G + K Y + (2 : ℂ) • S XY - XX‖ := by
    have h := norm_dirichletCoefficientL2Multiplier_le U
      (dirichletNormalCoefficientInverse f) (dirichletNormalCoefficientInverse_continuous hf)
      (Filter.Eventually.of_forall (dirichletNormalCoefficientInverse_norm_le_one f))
      (-G + K Y + (2 : ℂ) • S XY - XX)
    rw [one_mul] at h
    exact h
  have ht := norm_sub_le (-G + K Y + (2 : ℂ) • S XY) XX
  have ha := norm_add_le (-G + K Y) ((2 : ℂ) • S XY)
  have hb := norm_add_le (-G) (K Y)
  have hs : ‖(2 : ℂ) • S XY‖ = 2 * ‖S XY‖ := by
    rw [norm_smul]
    norm_num
  rw [norm_neg] at hb
  rw [hs] at ha
  nlinarith

/-- No second normal derivative is assumed: its L² membership follows
from the actual strong equation, which the physical pullback proves. -/
theorem dirichlet_normal_derivative_memLp {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict U))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict U))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict U))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict U))
    {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M) :
    MemLp (dirD (dirD u Complex.I) Complex.I) 2 (volume.restrict U) := by
  let R := dirichletNormalRecoveryL2 U f hf hSlope hCurvature
    (hG.toLp G) (hDy.toLp _) (hDxx.toLp _) (hDxy.toLp _)
  have hR : (R : ℂ → ℂ) =ᵐ[volume.restrict U] dirD (dirD u Complex.I) Complex.I := by
    filter_upwards [dirichletNormalRecoveryL2_ae U f hf hSlope hCurvature
      (hG.toLp G) (hDy.toLp _) (hDxx.toLp _) (hDxy.toLp _),
      hG.coeFn_toLp, hDy.coeFn_toLp, hDxx.coeFn_toLp, hDxy.coeFn_toLp,
      ae_restrict_mem hU.measurableSet] with z hr hg hy hxx hxy hz
    rw [hr, hg, hy, hxx, hxy]
    exact (dirichlet_normal_derivative_recovery hU hf hu hstrong hz).symm
  exact MemLp.ae_eq hR (Lp.memLp R)

/-- The actual two directional derivatives of `Dy u` are now in L².
The first component uses genuine smooth mixed-derivative symmetry. -/
theorem dirichlet_normal_gradient_memLp {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict U))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict U))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict U))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict U))
    {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M) :
    ∀ i : Fin 2, MemLp (fun z => fderiv ℝ (dirD u Complex.I) z (coordDir i))
      2 (volume.restrict U) := by
  intro i
  fin_cases i
  · change MemLp (dirD (dirD u Complex.I) 1) 2 (volume.restrict U)
    apply MemLp.ae_eq _ hDxy
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact dirichlet_normal_dirD_comm hU hu hz 1 Complex.I
  · change MemLp (dirD (dirD u Complex.I) Complex.I) 2 (volume.restrict U)
    exact dirichlet_normal_derivative_memLp hU hf hu hstrong hG hDy hDxx hDxy hSlope hCurvature

/-- The actual weak-gradient identity is obtained by compact interior
test localization and integration by parts, not supplied as a hypothesis. -/
theorem dirichlet_normal_gradient_isWeakGradient {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict U))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict U))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict U))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict U))
    {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M) :
    IsWeakGradient U (hDy.toLp (dirD u Complex.I))
      (fun i => (dirichlet_normal_gradient_memLp hU hf hu hstrong hG hDy hDxx hDxy
        hSlope hCurvature i).toLp _) :=
  isWeakGradient_of_contDiffOn hU (dirichlet_contDiffOn_dirD hU hu Complex.I) hDy
    (dirichlet_normal_gradient_memLp hU hf hu hstrong hG hDy hDxx hDxy hSlope hCurvature)

/-- An actual H¹ vector for the normal first derivative. -/
def dirichletNormalDerivativeH1 {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict U))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict U))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict U))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict U))
    {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M) :
    NeumannH1 U :=
  h1Vector (dirichlet_normal_gradient_isWeakGradient hU hf hu hstrong hG hDy hDxx hDxy
    hSlope hCurvature)

theorem h1Value_dirichletNormalDerivativeH1 {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict U))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict U))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict U))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict U))
    {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M) :
    h1Value U (dirichletNormalDerivativeH1 hU hf hu hstrong hG hDy hDxx hDxy hSlope hCurvature) =
      hDy.toLp (dirD u Complex.I) :=
  h1Value_h1Vector (dirichlet_normal_gradient_isWeakGradient hU hf hu hstrong hG hDy hDxx hDxy
    hSlope hCurvature)

theorem h1Gradient_dirichletNormalDerivativeH1_ae {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict U))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict U))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict U))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict U))
    {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M) (i : Fin 2) :
    (h1Gradient U i (dirichletNormalDerivativeH1 hU hf hu hstrong hG hDy hDxx hDxy
      hSlope hCurvature) : ℂ → ℂ) =ᵐ[volume.restrict U]
        fun z => fderiv ℝ (dirD u Complex.I) z (coordDir i) := by
  rw [dirichletNormalDerivativeH1, h1Gradient_h1Vector]
  exact (dirichlet_normal_gradient_memLp hU hf hu hstrong hG hDy hDxx hDxy
    hSlope hCurvature i).coeFn_toLp

section NormalData

variable {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict U))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict U))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict U))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict U))
    {L M : ℝ}
    (hSlope : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphSlope f z‖ ≤ L)
    (hCurvature : ∀ᵐ z ∂volume.restrict U, ‖dirichletGraphCurvature f z‖ ≤ M)

include hU hu hstrong in
theorem dirichlet_normal_derivative_toLp_eq_recovery
    (hYY : MemLp (dirD (dirD u Complex.I) Complex.I) 2 (volume.restrict U)) :
    hYY.toLp (dirD (dirD u Complex.I) Complex.I) =
      dirichletNormalRecoveryL2 U f hf hSlope hCurvature
        (hG.toLp G) (hDy.toLp _) (hDxx.toLp _) (hDxy.toLp _) := by
  apply Lp.ext
  filter_upwards [hYY.coeFn_toLp,
    dirichletNormalRecoveryL2_ae U f hf hSlope hCurvature
      (hG.toLp G) (hDy.toLp _) (hDxx.toLp _) (hDxy.toLp _),
    hG.coeFn_toLp, hDy.coeFn_toLp, hDxx.coeFn_toLp, hDxy.coeFn_toLp,
    ae_restrict_mem hU.measurableSet] with z hyy hr hg hy hxx hxy hz
  change (hYY.toLp _) z = (dirichletNormalRecoveryL2 U f hf hSlope hCurvature
    (hG.toLp G) (hDy.toLp _) (hDxx.toLp _) (hDxy.toLp _)) z
  rw [hyy, hr, hg, hy, hxx, hxy]
  exact dirichlet_normal_derivative_recovery hU hf hu hstrong hz

include hU hf hu hstrong hSlope hCurvature in
/-- A quantitative bound on the actual normal second derivative class. -/
theorem norm_dirichlet_normal_derivative_toLp_le
    (hYY : MemLp (dirD (dirD u Complex.I) Complex.I) 2 (volume.restrict U)) :
    ‖hYY.toLp (dirD (dirD u Complex.I) Complex.I)‖ ≤
      ‖hG.toLp G‖ + M * ‖hDy.toLp (dirD u Complex.I)‖ +
        2 * L * ‖hDxy.toLp (dirD (dirD u 1) Complex.I)‖ +
          ‖hDxx.toLp (dirD (dirD u 1) 1)‖ := by
  rw [dirichlet_normal_derivative_toLp_eq_recovery hU hf hu hstrong hG hDy hDxx hDxy
    hSlope hCurvature hYY]
  exact norm_dirichletNormalRecoveryL2_le U f hf hSlope hCurvature
    (hG.toLp G) (hDy.toLp _) (hDxx.toLp _) (hDxy.toLp _)

theorem norm_h1Gradient_dirichletNormalDerivativeH1_le :
    ‖h1Gradient U 1 (dirichletNormalDerivativeH1 hU hf hu hstrong hG hDy hDxx hDxy
      hSlope hCurvature)‖ ≤
      ‖hG.toLp G‖ + M * ‖hDy.toLp (dirD u Complex.I)‖ +
        2 * L * ‖hDxy.toLp (dirD (dirD u 1) Complex.I)‖ +
          ‖hDxx.toLp (dirD (dirD u 1) 1)‖ := by
  have hg : h1Gradient U 1 (dirichletNormalDerivativeH1 hU hf hu hstrong hG hDy hDxx hDxy
      hSlope hCurvature) =
        (dirichlet_normal_derivative_memLp hU hf hu hstrong hG hDy hDxx hDxy
          hSlope hCurvature).toLp (dirD (dirD u Complex.I) Complex.I) := by
    apply Lp.ext
    filter_upwards [h1Gradient_dirichletNormalDerivativeH1_ae hU hf hu hstrong hG hDy hDxx hDxy
      hSlope hCurvature 1,
      (dirichlet_normal_derivative_memLp hU hf hu hstrong hG hDy hDxx hDxy
        hSlope hCurvature).coeFn_toLp] with z hl hr
    change (h1Gradient U 1 (dirichletNormalDerivativeH1 hU hf hu hstrong hG hDy hDxx hDxy
      hSlope hCurvature)) z = _
    rw [hl, hr]
    rfl
  rw [hg]
  exact norm_dirichlet_normal_derivative_toLp_le hU hf hu hstrong hG hDy hDxx hDxy
    hSlope hCurvature _

end NormalData

/-- The graph slope bound is derived from the actual Lipschitz graph. -/
theorem dirichletGraphSlope_norm_le_of_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (z : ℂ) : ‖dirichletGraphSlope f z‖ ≤ (K : ℝ) := by
  simpa only [dirichletGraphSlope, Complex.norm_real] using
    norm_deriv_le_of_lipschitz hLip (x₀ := z.re)

/-- The curvature bound on a finite graph rectangle is obtained from
the actual smooth graph and compactness of its horizontal interval. -/
theorem exists_dirichletGraphCurvature_bound_on_halfBox {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ smoothDirichletHalfBox a b,
      ‖dirichletGraphCurvature f z‖ ≤ M := by
  have hκ : Continuous (deriv (deriv f)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2.continuous
  obtain ⟨M, hM⟩ :=
    (show IsCompact (Icc (-a) a) from isCompact_Icc).exists_bound_of_continuousOn hκ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  have hzI : z.re ∈ Icc (-a) a :=
    ⟨(abs_lt.mp hz.1).1.le, (abs_lt.mp hz.1).2.le⟩
  have hb := hM z.re hzI
  simpa only [dirichletGraphCurvature, Complex.norm_real] using hb.trans (le_max_left _ _)

/-- With actual graph data, the coefficient bounds introduce no extra
normal-regularity premise. Only the genuine tangential L² inputs remain. -/
theorem dirichlet_normal_derivative_memLp_on_halfBox {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    (a b : ℝ) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox a b,
      dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirD (dirD u Complex.I) Complex.I) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  obtain ⟨M, _, hM⟩ := exists_dirichletGraphCurvature_bound_on_halfBox hf a b
  exact dirichlet_normal_derivative_memLp (isOpen_smoothDirichletHalfBox a b) hf hu hstrong
    hG hDy hDxx hDxy
    (Filter.Eventually.of_forall (dirichletGraphSlope_norm_le_of_lipschitz hLip))
    (ae_restrict_of_forall_mem (isOpen_smoothDirichletHalfBox a b).measurableSet hM)

/-- The normal first derivative has a genuine H¹ realization on the
rectangle, using no normal second-derivative assumption. -/
theorem exists_dirichlet_normal_derivative_h1_on_halfBox {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    (a b : ℝ) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox a b,
      dirichletFlattenedDivergence f u z = -G z)
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDy : MemLp (dirD u Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDxx : MemLp (dirD (dirD u 1) 1) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    ∃ w : NeumannH1 (smoothDirichletHalfBox a b),
      (h1Value _ w : ℂ → ℂ) =ᵐ[volume.restrict (smoothDirichletHalfBox a b)] dirD u Complex.I ∧
      ∀ i : Fin 2, (h1Gradient _ i w : ℂ → ℂ)
        =ᵐ[volume.restrict (smoothDirichletHalfBox a b)]
          fun z => fderiv ℝ (dirD u Complex.I) z (coordDir i) := by
  obtain ⟨M, _, hM⟩ := exists_dirichletGraphCurvature_bound_on_halfBox hf a b
  have hU := isOpen_smoothDirichletHalfBox a b
  have hSlope : ∀ᵐ z ∂volume.restrict (smoothDirichletHalfBox a b),
      ‖dirichletGraphSlope f z‖ ≤ (K : ℝ) :=
    Filter.Eventually.of_forall (dirichletGraphSlope_norm_le_of_lipschitz hLip)
  have hCurvature : ∀ᵐ z ∂volume.restrict (smoothDirichletHalfBox a b),
      ‖dirichletGraphCurvature f z‖ ≤ M :=
    ae_restrict_of_forall_mem hU.measurableSet hM
  refine ⟨dirichletNormalDerivativeH1 hU hf hu hstrong hG hDy hDxx hDxy hSlope hCurvature, ?_, ?_⟩
  · rw [h1Value_dirichletNormalDerivativeH1]
    exact hDy.coeFn_toLp
  · exact h1Gradient_dirichletNormalDerivativeH1_ae hU hf hu hstrong hG hDy hDxx hDxy
      hSlope hCurvature

/-- For the actual Green correction remainder the strong equation is
proved from the genuine physical Laplacian, with its original forcing. -/
theorem riemannMapping_flattened_dirichlet_strong_equation {Ω U : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    (d : smoothTraceTests) (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous) U Ω) :
    ∀ z ∈ U, dirichletFlattenedDivergence f
      (riemannMappingDirichletRemainder F d ∘ smoothDirichletGraphChart p c hc f hf.continuous) z =
        -lap (d : ℂ → ℂ) (smoothDirichletGraphChart p c hc f hf.continuous z) := by
  intro z hz
  rw [dirichletFlattenedDivergence_pullback hS.1.1 p c hc hc₁ hf
    (riemannMappingDirichletRemainder_contDiffOn hb hS hsc F hF hinj himage d) (hmap hz)]
  exact riemannMappingDirichletRemainder_lap hb hS hsc F hF hinj himage d (hmap hz)

/-- The actual physical remainder acquires its normal second derivative
as soon as the separately proved tangential energy estimates are supplied.
The equation and all graph coefficient bounds are derived here. -/
theorem riemannMapping_flattened_normal_derivative_memLp {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    (d : smoothTraceTests) (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    (a b : ℝ)
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) Ω)
    (hG : MemLp (fun z => lap (d : ℂ → ℂ) (smoothDirichletGraphChart p c hc f hf.continuous z))
      2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDy : MemLp (dirD (riemannMappingDirichletRemainder F d ∘
      smoothDirichletGraphChart p c hc f hf.continuous) Complex.I)
      2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDxx : MemLp (dirD (dirD (riemannMappingDirichletRemainder F d ∘
      smoothDirichletGraphChart p c hc f hf.continuous) 1) 1)
      2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDxy : MemLp (dirD (dirD (riemannMappingDirichletRemainder F d ∘
      smoothDirichletGraphChart p c hc f hf.continuous) 1) Complex.I)
      2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirD (dirD (riemannMappingDirichletRemainder F d ∘
      smoothDirichletGraphChart p c hc f hf.continuous) Complex.I) Complex.I)
      2 (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞)
      (riemannMappingDirichletRemainder F d ∘ smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) :=
    (riemannMappingDirichletRemainder_contDiffOn hb hS hsc F hF hinj himage d).comp
      (smoothDirichletGraphChart_contDiff p c hc hf).contDiffOn hmap
  exact dirichlet_normal_derivative_memLp_on_halfBox hf hLip a b hu
    (riemannMapping_flattened_dirichlet_strong_equation hb hS hsc F hF hinj himage d
      p c hc hc₁ hf hmap) hG hDy hDxx hDxy

/-- For the actual physical remainder, the existing first-gradient
H¹ vector supplies `Dy ∈ L²` and the genuine compact datum supplies
the forcing. The only additional energy data are the two tangential
second derivatives that the difference-quotient argument produces. -/
theorem exists_riemannMapping_flattened_normal_derivative_h1 {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    (d : smoothTraceTests) (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {a b : ℝ}
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) Ω)
    (v : NeumannH1 (smoothDirichletHalfBox a b))
    (hgv : (h1Gradient (smoothDirichletHalfBox a b) 1 v : ℂ → ℂ)
      =ᵐ[volume.restrict (smoothDirichletHalfBox a b)]
        dirD (riemannMappingDirichletRemainder F d ∘
          smoothDirichletGraphChart p c hc f hf.continuous) Complex.I)
    (hDxx : MemLp (dirD (dirD (riemannMappingDirichletRemainder F d ∘
      smoothDirichletGraphChart p c hc f hf.continuous) 1) 1)
      2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hDxy : MemLp (dirD (dirD (riemannMappingDirichletRemainder F d ∘
      smoothDirichletGraphChart p c hc f hf.continuous) 1) Complex.I)
      2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (let u := riemannMappingDirichletRemainder F d ∘
       smoothDirichletGraphChart p c hc f hf.continuous
     ∃ w : NeumannH1 (smoothDirichletHalfBox a b),
       (h1Value _ w : ℂ → ℂ) =ᵐ[volume.restrict (smoothDirichletHalfBox a b)] dirD u Complex.I ∧
       ∀ i : Fin 2, (h1Gradient _ i w : ℂ → ℂ)
         =ᵐ[volume.restrict (smoothDirichletHalfBox a b)]
           fun z => fderiv ℝ (dirD u Complex.I) z (coordDir i)) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b) :=
    (riemannMappingDirichletRemainder_contDiffOn hb hS hsc F hF hinj himage d).comp
      (smoothDirichletGraphChart_contDiff p c hc hf).contDiffOn hmap
  have hDy : MemLp (dirD u Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)) :=
    MemLp.ae_eq hgv (Lp.memLp (h1Gradient (smoothDirichletHalfBox a b) 1 v))
  have hG := dirichlet_lapDatum_pullback_memLp (a := a) (b := b) d Ψ.continuous
  exact exists_dirichlet_normal_derivative_h1_on_halfBox hf hLip a b hu
    (riemannMapping_flattened_dirichlet_strong_equation hb hS hsc F hF hinj himage d
      p c hc hc₁ hf hmap) hG hDy hDxx hDxy

end PolyaNeumann
end
