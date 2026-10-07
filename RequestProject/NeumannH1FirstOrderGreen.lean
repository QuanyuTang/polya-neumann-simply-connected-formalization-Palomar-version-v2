module

public import RequestProject.NeumannHardyTraceInjective
public import RequestProject.LpBoundedMultiplier

/-!
# First-order and conormal Green identities on the actual H¹ space

The nonconjugate velocity identity is proved first on compact smooth
restrictions by the genuine winding-number Green formula, then extended
by H¹ density through bounded functionals. Combining it with the conjugate
identity gives the two real coordinate divergence formulas. When the weak
gradient components themselves have actual H¹ representatives, these give
the genuine second-order conormal Green formula with their actual traces.

Boundary measure is ordinary dθ. Its normal density is `-i γ′`, so its
real coordinate components are `Im γ′` and `-Re γ′`.
This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate

def firstOrderL2TestPair (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) : L2 Ω →L[ℂ] ℂ :=
  innerSL ℂ ((hφ.conj.memLp' 2).toLp (fun z => conj (φ z)))

private theorem firstOrderL2TestPair_apply (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (u : L2 Ω) :
    firstOrderL2TestPair Ω hφ u = ∫ z in Ω, u z * φ z := by
  change ⟪(hφ.conj.memLp' 2).toLp (fun z => conj (φ z)), u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hφ.conj.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply, hz, Complex.conj_conj]

private theorem firstOrder_boundary_coefficient_memLp {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (a : ℝ → ℂ) (ha : AEStronglyMeasurable a volume) {K : ℝ}
    (hK : ∀ θ, ‖a θ‖ ≤ K) :
    MemLp (fun θ => φ (γ θ) * a θ) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  have hC0 : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC 0)
  apply MemLp.of_bound
    ((hφ.1.continuous.comp hKγ.continuous).aestronglyMeasurable.mul ha).restrict (C * K)
  apply Eventually.of_forall
  intro θ
  change ‖φ (γ θ) * a θ‖ ≤ C * K
  rw [norm_mul]
  exact mul_le_mul (hC (γ θ)) (hK θ) (norm_nonneg _) hC0

theorem firstOrder_velocity_coefficient_memLp {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    MemLp (fun θ => φ (γ θ) * deriv γ θ) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  exact firstOrder_boundary_coefficient_memLp hγ hφ (deriv γ)
    (measurable_deriv γ).aestronglyMeasurable (fun _ => norm_deriv_le_of_lipschitz hK)

private theorem firstOrder_conjugate_velocity_coefficient_memLp {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    MemLp (fun θ => φ (γ θ) * conj (deriv γ θ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  apply firstOrder_boundary_coefficient_memLp hγ hφ (fun θ => conj (deriv γ θ))
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (measurable_deriv γ).aestronglyMeasurable)
  intro θ
  simpa only [Complex.norm_conj] using norm_deriv_le_of_lipschitz (x₀ := θ) hK

/-- Conjugation converts the bilinear boundary test into an inner-product
functional linear in the actual trace. -/
def firstOrderVelocityTestL2 {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) : BoundaryL2 :=
  ((firstOrder_velocity_coefficient_memLp hγ hφ).star).toLp
    (fun θ => conj (φ (γ θ) * deriv γ θ))

def h1FirstOrderBoundaryTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (firstOrderVelocityTestL2 hγ hφ)).comp (h1BoundaryTrace hb hL hγ)

def h1FirstOrderInteriorTest (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  Complex.I • ((firstOrderL2TestPair Ω hφ).comp (h1Gradient Ω 0) +
      (firstOrderL2TestPair Ω (hφ.dirD 1)).comp (h1Value Ω)) -
    ((firstOrderL2TestPair Ω hφ).comp (h1Gradient Ω 1) +
      (firstOrderL2TestPair Ω (hφ.dirD Complex.I)).comp (h1Value Ω))

theorem h1FirstOrderInteriorTest_apply (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (u : NeumannH1 Ω) :
    h1FirstOrderInteriorTest Ω hφ u =
      Complex.I * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) := by
  simp only [h1FirstOrderInteriorTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, firstOrderL2TestPair_apply]

theorem h1FirstOrderBoundaryTest_apply {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (u : NeumannH1 Ω) :
    h1FirstOrderBoundaryTest hb hL hγ hφ u =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * deriv γ θ) := by
  change ⟪firstOrderVelocityTestL2 hγ hφ, h1BoundaryTrace hb hL hγ u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((firstOrder_velocity_coefficient_memLp hγ hφ).star).coeFn_toLp]
    with θ hθ
  change firstOrderVelocityTestL2 hγ hφ θ = conj (φ (γ θ) * deriv γ θ) at hθ
  simp only [RCLike.inner_apply]
  change h1BoundaryTrace hb hL hγ u θ * conj (firstOrderVelocityTestL2 hγ hφ θ) = _
  rw [hθ, Complex.conj_conj]

private theorem smooth_firstOrder_green {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {p : ℂ → ℂ} (hp : TestFunction univ p) :
    (∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * deriv γ θ) =
      Complex.I * (∫ z in Ω, dirD p 1 z) - ∫ z in Ω, dirD p Complex.I z := by
  obtain ⟨Kp, hKp⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hp.2.1 hp.1 (by simp)
  have hg : (∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * deriv γ θ) =
      2 * Complex.I * ∫ z in Ω, dbar p z := by
    simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
      using integral_boundary_eq_dbar hb hL hγ hKp hp.2.1
  have hdx : IntegrableOn (dirD p 1) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD 1).memLp' 1)
  have hdy : IntegrableOn (dirD p Complex.I) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD Complex.I).memLp' 1)
  calc
    _ = 2 * Complex.I * ∫ z in Ω, dbar p z := hg
    _ = ∫ z in Ω, (Complex.I * dirD p 1 z - dirD p Complex.I z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only [dbar, dirD]
      ring_nf; simp only [Complex.I_sq]; ring
    _ = _ := by rw [integral_sub (hdx.const_mul _) hdy, integral_const_mul]

private theorem firstOrderL2TestPair_smooth_value (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (f : smoothTraceTests) :
    firstOrderL2TestPair Ω hφ (h1Value Ω (smoothTraceH1 Ω f)) = ∫ z in Ω, f z * φ z := by
  rw [firstOrderL2TestPair_apply]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp Ω f).coeFn_toLp] with z hz
  rw [h1Value_smoothTraceH1, hz]

private theorem firstOrderL2TestPair_smooth_gradient (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (f : smoothTraceTests) (i : Fin 2) :
    firstOrderL2TestPair Ω hφ (h1Gradient Ω i (smoothTraceH1 Ω f)) =
      ∫ z in Ω, dirD (f : ℂ → ℂ) (coordDir i) z * φ z := by
  rw [firstOrderL2TestPair_apply]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz
  simpa only [h1Gradient_smoothTraceH1, dirD] using
    congrArg (fun w : ℂ => w * φ z) hz

private theorem h1FirstOrder_green_smooth {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (f : smoothTraceTests) :
    h1FirstOrderBoundaryTest hb hL hγ hφ (smoothTraceH1 Ω f) =
      h1FirstOrderInteriorTest Ω hφ (smoothTraceH1 Ω f) := by
  let p : ℂ → ℂ := fun z => f z * φ z
  have hp : TestFunction univ p :=
    ⟨f.property.1.mul hφ.1, f.property.2.1.mul_right, subset_univ _⟩
  have hleft : h1FirstOrderBoundaryTest hb hL hγ hφ (smoothTraceH1 Ω f) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * deriv γ θ := by
    rw [h1FirstOrderBoundaryTest_apply]
    apply integral_congr_ae
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
    rw [hθ]
    dsimp [p]
    ring
  have hproduct (v z : ℂ) :
      dirD p v z = dirD (f : ℂ → ℂ) v z * φ z + f z * dirD φ v z := by
    rw [dirD, fderiv_fun_mul (f.property.1.differentiable (by simp) z)
      (hφ.1.differentiable (by simp) z)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    dsimp only [dirD]
    ring
  have hproduct_integral (v : ℂ) :
      (∫ z in Ω, dirD p v z) = (∫ z in Ω, dirD (f : ℂ → ℂ) v z * φ z) +
        ∫ z in Ω, f z * dirD φ v z := by
    simp_rw [hproduct]
    exact integral_add (integrable_mul_test ((f.property.dirD v).memLp' 2) hφ)
      (integrable_mul_test (f.property.memLp' 2) (hφ.dirD v))
  rw [hleft, smooth_firstOrder_green hb hL hγ hp,
    hproduct_integral, hproduct_integral]
  have hdir0 : coordDir (0 : Fin 2) = (1 : ℂ) := rfl
  have hdir1 : coordDir (1 : Fin 2) = Complex.I := rfl
  simp only [h1FirstOrderInteriorTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, firstOrderL2TestPair_smooth_gradient,
    firstOrderL2TestPair_smooth_value, hdir0, hdir1]

theorem h1FirstOrderBoundaryTest_eq_interior {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    h1FirstOrderBoundaryTest hb hL hγ hφ = h1FirstOrderInteriorTest Ω hφ := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1FirstOrderBoundaryTest hb hL hγ hφ).continuous
    (h1FirstOrderInteriorTest Ω hφ).continuous
  funext f
  rw [Function.comp_apply, Function.comp_apply, smoothTraceH1Lin_apply]
  exact h1FirstOrder_green_smooth hb hL hγ hφ f

/-- The genuine nonconjugate first-order Green identity on every H¹ input. -/
theorem h1_firstOrder_green {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (u : NeumannH1 Ω) :
    Complex.I * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
      ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * deriv γ θ) := by
  rw [← h1FirstOrderInteriorTest_apply Ω hφ u,
    ← h1FirstOrderBoundaryTest_eq_interior hb hL hγ hφ,
    h1FirstOrderBoundaryTest_apply]

private theorem firstOrder_normal_x (z : ℂ) :
    (z.im : ℂ) = (-Complex.I / 2) * (z - conj z) := by
  rw [Complex.sub_conj]
  push_cast
  ring_nf; simp only [Complex.I_sq]; ring

private theorem firstOrder_normal_y (z : ℂ) :
    -(z.re : ℂ) = (-1 / 2 : ℂ) * (z + conj z) := by
  rw [Complex.add_conj]
  push_cast
  ring

/-- Divergence in the real x direction, with the actual outward normal density. -/
theorem h1_coordinate_divergence_x {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (u : NeumannH1 Ω) :
    (∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
        (∫ z in Ω, h1Value Ω u z * dirD φ 1 z) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * ((deriv γ θ).im : ℂ)) := by
  have hp := h1_firstOrder_green hb hL hγ hφ u
  have hm := h1_firstOrder_conjugate_green hb hL hγ hφ u
  have hip := (Lp.memLp (h1BoundaryTrace hb hL hγ u)).integrable_mul
    (firstOrder_velocity_coefficient_memLp hγ hφ)
  have him := (Lp.memLp (h1BoundaryTrace hb hL hγ u)).integrable_mul
    (firstOrder_conjugate_velocity_coefficient_memLp hγ hφ)
  symm
  calc
    _ = ∫ θ in Ioc (0 : ℝ) (2 * π), (-Complex.I / 2) *
        (h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * deriv γ θ) -
          h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * conj (deriv γ θ))) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro θ
      change h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * ((deriv γ θ).im : ℂ)) =
        (-Complex.I / 2) *
          (h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * deriv γ θ) -
            h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * conj (deriv γ θ)))
      rw [firstOrder_normal_x]
      ring
    _ = (-Complex.I / 2) *
        ((∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
          (φ (γ θ) * deriv γ θ)) -
        ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
          (φ (γ θ) * conj (deriv γ θ))) := by
      rw [integral_const_mul]
      exact congrArg (fun z : ℂ => (-Complex.I / 2) * z) (integral_sub hip him)
    _ = _ := by
      rw [← hp, ← hm]
      ring_nf; simp only [Complex.I_sq]; ring

/-- Divergence in the real y direction, with density `-Re γ′`. -/
theorem h1_coordinate_divergence_y {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (u : NeumannH1 Ω) :
    (∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        (∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * (-(deriv γ θ).re : ℂ)) := by
  have hp := h1_firstOrder_green hb hL hγ hφ u
  have hm := h1_firstOrder_conjugate_green hb hL hγ hφ u
  have hip := (Lp.memLp (h1BoundaryTrace hb hL hγ u)).integrable_mul
    (firstOrder_velocity_coefficient_memLp hγ hφ)
  have him := (Lp.memLp (h1BoundaryTrace hb hL hγ u)).integrable_mul
    (firstOrder_conjugate_velocity_coefficient_memLp hγ hφ)
  symm
  calc
    _ = ∫ θ in Ioc (0 : ℝ) (2 * π), (-1 / 2 : ℂ) *
        (h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * deriv γ θ) +
          h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * conj (deriv γ θ))) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro θ
      change h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * (-(deriv γ θ).re : ℂ)) =
        (-1 / 2 : ℂ) *
          (h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * deriv γ θ) +
            h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * conj (deriv γ θ)))
      rw [show (-(deriv γ θ).re : ℂ) = -((deriv γ θ).re : ℂ) from by simp,
        firstOrder_normal_y]
      ring
    _ = (-1 / 2 : ℂ) *
        ((∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
          (φ (γ θ) * deriv γ θ)) +
        ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
          (φ (γ θ) * conj (deriv γ θ))) := by
      rw [integral_const_mul]
      exact congrArg (fun z : ℂ => (-1 / 2 : ℂ) * z) (integral_add hip him)
    _ = _ := by rw [← hp, ← hm]; ring

def firstOrderBoundarySpeedBound {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : NNReal := Classical.choose hγ.lipschitz

private theorem firstOrderBoundarySpeedBound_spec {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : LipschitzWith (firstOrderBoundarySpeedBound hγ) γ :=
  Classical.choose_spec hγ.lipschitz

theorem firstOrder_normalX_measurable (γ : ℝ → ℂ) :
    AEStronglyMeasurable (fun θ => ((deriv γ θ).im : ℂ)) volume :=
  Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
    (Complex.imCLM.continuous.comp_aestronglyMeasurable (measurable_deriv γ).aestronglyMeasurable)

theorem firstOrder_normalY_measurable (γ : ℝ → ℂ) :
    AEStronglyMeasurable (fun θ => (-(deriv γ θ).re : ℂ)) volume := by
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Complex.continuous_re.comp_aestronglyMeasurable
        (measurable_deriv γ).aestronglyMeasurable)).neg

theorem firstOrder_normalX_bound {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (θ : ℝ) :
    ‖((deriv γ θ).im : ℂ)‖ ≤ firstOrderBoundarySpeedBound hγ := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans
    (norm_deriv_le_of_lipschitz (firstOrderBoundarySpeedBound_spec hγ))

theorem firstOrder_normalY_bound {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (θ : ℝ) :
    ‖(-(deriv γ θ).re : ℂ)‖ ≤ firstOrderBoundarySpeedBound hγ := by
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans
    (norm_deriv_le_of_lipschitz (firstOrderBoundarySpeedBound_spec hγ))

/-- Multiplication by the genuine x component of the outward normal density. -/
def h1BoundaryNormalXMultiplier {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  lpBoundedMultiplier (fun θ => ((deriv γ θ).im : ℂ))
    (firstOrder_normalX_measurable γ).restrict
    (Eventually.of_forall (firstOrder_normalX_bound hγ))

/-- Multiplication by the genuine y component of the outward normal density. -/
def h1BoundaryNormalYMultiplier {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  lpBoundedMultiplier (fun θ => (-(deriv γ θ).re : ℂ))
    (firstOrder_normalY_measurable γ).restrict
    (Eventually.of_forall (firstOrder_normalY_bound hγ))

theorem h1BoundaryNormalXMultiplier_ae {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (g : BoundaryL2) :
    (h1BoundaryNormalXMultiplier hγ g : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * π))]
      fun θ => ((deriv γ θ).im : ℂ) * g θ :=
  lpBoundedMultiplier_ae _ _ _ g

theorem h1BoundaryNormalYMultiplier_ae {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (g : BoundaryL2) :
    (h1BoundaryNormalYMultiplier hγ g : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * π))]
      fun θ => (-(deriv γ θ).re : ℂ) * g θ :=
  lpBoundedMultiplier_ae _ _ _ g

/-- The actual L² conormal density for two H¹ gradient representatives. -/
def h1GradientConormalDensity {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (g0 g1 : NeumannH1 Ω) : BoundaryL2 :=
  h1BoundaryNormalXMultiplier hγ (h1BoundaryTrace hb hL hγ g0) +
    h1BoundaryNormalYMultiplier hγ (h1BoundaryTrace hb hL hγ g1)

theorem h1GradientConormalDensity_ae {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (g0 g1 : NeumannH1 Ω) :
    (h1GradientConormalDensity hb hL hγ g0 g1 : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * π))]
      fun θ => ((deriv γ θ).im : ℂ) * h1BoundaryTrace hb hL hγ g0 θ +
        (-(deriv γ θ).re : ℂ) * h1BoundaryTrace hb hL hγ g1 θ := by
  filter_upwards [Lp.coeFn_add
      (h1BoundaryNormalXMultiplier hγ (h1BoundaryTrace hb hL hγ g0))
      (h1BoundaryNormalYMultiplier hγ (h1BoundaryTrace hb hL hγ g1)),
    h1BoundaryNormalXMultiplier_ae hγ (h1BoundaryTrace hb hL hγ g0),
    h1BoundaryNormalYMultiplier_ae hγ (h1BoundaryTrace hb hL hγ g1)] with θ ha hx hy
  change (_ + _ : BoundaryL2) θ = _
  rw [ha]
  simp only [Pi.add_apply, hx, hy]

/-- The divergence is the sum of actual weak derivative components. -/
def h1GradientDivergence (Ω : Set ℂ) (g0 g1 : NeumannH1 Ω) : L2 Ω :=
  h1Gradient Ω 0 g0 + h1Gradient Ω 1 g1

/-- The genuine conormal Green identity for a vector with H¹ weak gradients.
The actual gradient traces form an L² boundary density, rather than an
unspecified conormal regularity premise. -/
theorem h1_conormal_green_compact_test {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u g0 g1 : NeumannH1 Ω)
    (hg0 : h1Gradient Ω 0 u = h1Value Ω g0)
    (hg1 : h1Gradient Ω 1 u = h1Value Ω g1)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) +
        (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * φ z) =
      ∫ θ in Ioc (0 : ℝ) (2 * π),
        h1GradientConormalDensity hb hL hγ g0 g1 θ * φ (γ θ) := by
  have hx := h1_coordinate_divergence_x hb hL hγ hφ g0
  have hy := h1_coordinate_divergence_y hb hL hγ hφ g1
  have hdiv : (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * φ z) =
      (∫ z in Ω, h1Gradient Ω 0 g0 z * φ z) +
        ∫ z in Ω, h1Gradient Ω 1 g1 z * φ z := by
    rw [← firstOrderL2TestPair_apply Ω hφ]
    change firstOrderL2TestPair Ω hφ (_ + _) = _
    rw [map_add, firstOrderL2TestPair_apply, firstOrderL2TestPair_apply]
  have hix := (Lp.memLp (h1BoundaryTrace hb hL hγ g0)).integrable_mul
    (firstOrder_boundary_coefficient_memLp hγ hφ _ (firstOrder_normalX_measurable γ)
      (firstOrder_normalX_bound hγ))
  have hiy := (Lp.memLp (h1BoundaryTrace hb hL hγ g1)).integrable_mul
    (firstOrder_boundary_coefficient_memLp hγ hφ _ (firstOrder_normalY_measurable γ)
      (firstOrder_normalY_bound hγ))
  have hbd : (∫ θ in Ioc (0 : ℝ) (2 * π),
      h1GradientConormalDensity hb hL hγ g0 g1 θ * φ (γ θ)) =
      (∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ g0 θ *
        (φ (γ θ) * ((deriv γ θ).im : ℂ))) +
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ g1 θ *
        (φ (γ θ) * (-(deriv γ θ).re : ℂ)) := by
    calc
      _ = ∫ θ in Ioc (0 : ℝ) (2 * π),
          h1BoundaryTrace hb hL hγ g0 θ * (φ (γ θ) * ((deriv γ θ).im : ℂ)) +
          h1BoundaryTrace hb hL hγ g1 θ * (φ (γ θ) * (-(deriv γ θ).re : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [h1GradientConormalDensity_ae hb hL hγ g0 g1] with θ hθ
        rw [hθ]
        ring
      _ = _ := integral_add hix hiy
  rw [Fin.sum_univ_two]
  change (∫ z in Ω, h1Gradient Ω 0 u z * dirD φ 1 z) +
      (∫ z in Ω, h1Gradient Ω 1 u z * dirD φ Complex.I z) + _ = _
  rw [hg0, hg1, hdiv, hbd, ← hx, ← hy]
  ring

/-- The true second Green formula with actual gradient traces. -/
theorem h1_secondGreen_compact_test {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u g0 g1 : NeumannH1 Ω)
    (hg0 : h1Gradient Ω 0 u = h1Value Ω g0)
    (hg1 : h1Gradient Ω 1 u = h1Value Ω g1)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∫ z in Ω, h1Value Ω u z * lap φ z) -
        (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * φ z) =
      (∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) -
      ∫ θ in Ioc (0 : ℝ) (2 * π),
        h1GradientConormalDensity hb hL hγ g0 g1 θ * φ (γ θ) := by
  have hA := h1_doubleLayer_green hb hL hγ hφ u
  have hB := h1_conormal_green_compact_test hb hL hγ u g0 g1 hg0 hg1 hφ
  rw [← hA, ← hB]
  ring

private theorem firstOrder_inner_toLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℂ 2 μ) {φ : α → ℂ} (hφ : MemLp φ 2 μ) :
    ⟪u, hφ.toLp φ⟫_ℂ = conj (∫ z, u z * conj (φ z) ∂μ) := by
  rw [L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with z hz
  simp only [RCLike.inner_apply, hz, map_mul, Complex.conj_conj]
  exact mul_comm _ _

private theorem firstOrder_inner_conjugate_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u v : Lp ℂ 2 μ) :
    ⟪u, v⟫_ℂ = conj (∫ z, u z * conj (v z) ∂μ) := by
  rw [L2.inner_def, ← integral_conj]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_conj, mul_comm]

/-- A bounded functional in the H¹ test input; its first argument is fixed. -/
def h1ConormalGreenInteriorFunctional (Ω : Set ℂ) (u g0 g1 : NeumannH1 Ω) :
    NeumannH1 Ω →L[ℂ] ℂ :=
  (∑ i : Fin 2, (innerSL ℂ (h1Gradient Ω i u)).comp (h1Gradient Ω i)) +
    (innerSL ℂ (h1GradientDivergence Ω g0 g1)).comp (h1Value Ω)

def h1ConormalGreenBoundaryFunctional {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (g0 g1 : NeumannH1 Ω) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (h1GradientConormalDensity hb hL hγ g0 g1)).comp (h1BoundaryTrace hb hL hγ)

theorem h1ConormalGreenInteriorFunctional_apply (Ω : Set ℂ)
    (u g0 g1 w : NeumannH1 Ω) :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 w =
      (∑ i : Fin 2, ⟪h1Gradient Ω i u, h1Gradient Ω i w⟫_ℂ) +
        ⟪h1GradientDivergence Ω g0 g1, h1Value Ω w⟫_ℂ := by
  simp only [h1ConormalGreenInteriorFunctional, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]

theorem h1ConormalGreenBoundaryFunctional_apply {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (g0 g1 w : NeumannH1 Ω) :
    h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 w =
      ⟪h1GradientConormalDensity hb hL hγ g0 g1, h1BoundaryTrace hb hL hγ w⟫_ℂ := rfl

private theorem h1ConormalGreen_smooth {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u g0 g1 : NeumannH1 Ω)
    (hg0 : h1Gradient Ω 0 u = h1Value Ω g0)
    (hg1 : h1Gradient Ω 1 u = h1Value Ω g1) (f : smoothTraceTests) :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 (smoothTraceH1 Ω f) =
      h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 (smoothTraceH1 Ω f) := by
  have hi (i : Fin 2) :
      ⟪h1Gradient Ω i u, h1Gradient Ω i (smoothTraceH1 Ω f)⟫_ℂ =
        conj (∫ z in Ω, h1Gradient Ω i u z *
          dirD (fun w => conj (f w)) (coordDir i) z) := by
    rw [h1Gradient_smoothTraceH1, firstOrder_inner_toLp]
    apply congrArg conj
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    change h1Gradient Ω i u z * conj (dirD (f : ℂ → ℂ) (coordDir i) z) =
      h1Gradient Ω i u z * dirD (fun w => conj (f w)) (coordDir i) z
    rw [dirD_conj (f.property.1.of_le (by simp))]
  have hv : ⟪h1GradientDivergence Ω g0 g1, h1Value Ω (smoothTraceH1 Ω f)⟫_ℂ =
      conj (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * conj (f z)) := by
    rw [h1Value_smoothTraceH1, firstOrder_inner_toLp]
  have hbnd : ⟪h1GradientConormalDensity hb hL hγ g0 g1,
      h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f)⟫_ℂ =
      conj (∫ θ in Ioc (0 : ℝ) (2 * π),
        h1GradientConormalDensity hb hL hγ g0 g1 θ * conj (f (γ θ))) := by
    rw [firstOrder_inner_conjugate_integral]
    apply congrArg conj
    apply integral_congr_ae
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
    rw [hθ]
  have h := congrArg conj
    (h1_conormal_green_compact_test hb hL hγ u g0 g1 hg0 hg1 f.property.conj)
  simp only [map_add, map_sum] at h
  simpa only [h1ConormalGreenInteriorFunctional_apply,
    h1ConormalGreenBoundaryFunctional_apply, hi, hv, hbnd] using h

/-- Both sides are genuinely bounded functionals in the test input, so
the compact-smooth identity extends to every actual H¹ test vector. -/
theorem h1ConormalGreenInteriorFunctional_eq_boundary {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u g0 g1 : NeumannH1 Ω)
    (hg0 : h1Gradient Ω 0 u = h1Value Ω g0)
    (hg1 : h1Gradient Ω 1 u = h1Value Ω g1) :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 =
      h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1ConormalGreenInteriorFunctional Ω u g0 g1).continuous
    (h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1).continuous
  funext f
  rw [Function.comp_apply, Function.comp_apply, smoothTraceH1Lin_apply]
  exact h1ConormalGreen_smooth hb hL hγ u g0 g1 hg0 hg1 f

/-- The true conormal Green formula against arbitrary H¹ tests, with the
same first-slot test convention as the physical Neumann form. -/
theorem h1_conormal_green {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u g0 g1 : NeumannH1 Ω)
    (hg0 : h1Gradient Ω 0 u = h1Value Ω g0)
    (hg1 : h1Gradient Ω 1 u = h1Value Ω g1) (w : NeumannH1 Ω) :
    (∑ i : Fin 2, ⟪h1Gradient Ω i w, h1Gradient Ω i u⟫_ℂ) +
        ⟪h1Value Ω w, h1GradientDivergence Ω g0 g1⟫_ℂ =
      ⟪h1BoundaryTrace hb hL hγ w, h1GradientConormalDensity hb hL hγ g0 g1⟫_ℂ := by
  have h := congrArg (fun T : NeumannH1 Ω →L[ℂ] ℂ => T w)
    (h1ConormalGreenInteriorFunctional_eq_boundary hb hL hγ u g0 g1 hg0 hg1)
  change h1ConormalGreenInteriorFunctional Ω u g0 g1 w =
    h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 w at h
  rw [h1ConormalGreenInteriorFunctional_apply,
    h1ConormalGreenBoundaryFunctional_apply] at h
  simpa only [map_add, map_sum, inner_conj_symm] using congrArg conj h

end PolyaNeumann

end
