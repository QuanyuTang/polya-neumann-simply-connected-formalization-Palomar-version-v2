module

public import RequestProject.NeumannTraceInjective
public import RequestProject.NeumannConstantTrace
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Uniqueness from the actual Hardy trace

The first-order conjugate Green identity is extended from compact smooth
restrictions to the genuine weak-gradient H¹ space. A zero actual trace
therefore makes the Cauchy--Riemann equation valid against global compact
tests. Its distributional Laplacian vanishes across the boundary. The
existing second-order Green identity then gives the zero-energy form
equation, whose genuine constants have injective actual trace.

No smoothness, Neumann equation, or spectral premise is imposed on the
input H¹ vector. Boundary measure is ordinary dθ and the boundary direction
in the first-order identity is the actual conjugate velocity.

This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate

def hardyL2TestPair (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) : L2 Ω →L[ℂ] ℂ :=
  innerSL ℂ ((hφ.conj.memLp' 2).toLp (fun z => conj (φ z)))

private theorem hardyL2TestPair_apply (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (u : L2 Ω) :
    hardyL2TestPair Ω hφ u = ∫ z in Ω, u z * φ z := by
  change ⟪(hφ.conj.memLp' 2).toLp (fun z => conj (φ z)), u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hφ.conj.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply, hz, Complex.conj_conj]

theorem hardyConjugateVelocityTest_memLp {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    MemLp (fun θ => conj (φ (γ θ) * conj (deriv γ θ))) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  have hC0 : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC 0)
  have hm : AEStronglyMeasurable
      (fun θ => φ (γ θ) * conj (deriv γ θ)) volume :=
    (hφ.1.continuous.comp hKγ.continuous).aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable
        (measurable_deriv γ).aestronglyMeasurable)
  apply MemLp.of_bound
    (Complex.continuous_conj.comp_aestronglyMeasurable hm).restrict (C * Kγ)
  apply Eventually.of_forall
  intro θ
  simp only [Complex.norm_conj, norm_mul]
  exact mul_le_mul (hC (γ θ)) (norm_deriv_le_of_lipschitz hKγ)
    (norm_nonneg _) hC0

/-- The actual conjugate-velocity boundary test is an L² class. -/
def hardyConjugateVelocityTestL2 {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) : BoundaryL2 :=
  (hardyConjugateVelocityTest_memLp hγ hφ).toLp
    (fun θ => conj (φ (γ θ) * conj (deriv γ θ)))

/-- A continuous first-order boundary functional on the actual H¹ space. -/
def h1FirstOrderConjugateBoundaryTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (hardyConjugateVelocityTestL2 hγ hφ)).comp (h1BoundaryTrace hb hL hγ)

/-- The two genuine weak derivatives and the smooth test derivatives
give a continuous first-order interior functional. -/
def h1FirstOrderConjugateInteriorTest (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (-Complex.I) • ((hardyL2TestPair Ω hφ).comp (h1Gradient Ω 0) +
      (hardyL2TestPair Ω (hφ.dirD 1)).comp (h1Value Ω)) -
    ((hardyL2TestPair Ω hφ).comp (h1Gradient Ω 1) +
      (hardyL2TestPair Ω (hφ.dirD Complex.I)).comp (h1Value Ω))

theorem h1FirstOrderConjugateInteriorTest_apply (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (u : NeumannH1 Ω) :
    h1FirstOrderConjugateInteriorTest Ω hφ u =
      -Complex.I * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) := by
  simp only [h1FirstOrderConjugateInteriorTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, hardyL2TestPair_apply]

theorem h1FirstOrderConjugateBoundaryTest_apply {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (u : NeumannH1 Ω) :
    h1FirstOrderConjugateBoundaryTest hb hL hγ hφ u =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * conj (deriv γ θ)) := by
  change ⟪hardyConjugateVelocityTestL2 hγ hφ, h1BoundaryTrace hb hL hγ u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hardyConjugateVelocityTest_memLp hγ hφ).coeFn_toLp] with θ hθ
  simp only [hardyConjugateVelocityTestL2, RCLike.inner_apply, hθ, Complex.conj_conj]

private theorem smooth_conjugate_firstOrder_green {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {p : ℂ → ℂ} (hp : TestFunction univ p) :
    (∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * conj (deriv γ θ)) =
      -Complex.I * (∫ z in Ω, dirD p 1 z) - ∫ z in Ω, dirD p Complex.I z := by
  obtain ⟨Kp, hKp⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    hp.conj.2.1 hp.conj.1 (by simp)
  have hg : (∫ θ in Ioc (0 : ℝ) (2 * π), conj (p (γ θ)) * deriv γ θ) =
      2 * Complex.I * ∫ z in Ω, dbar (fun w => conj (p w)) z := by
    simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
      using integral_boundary_eq_dbar hb hL hγ hKp hp.conj.2.1
  have hdx : IntegrableOn (dirD p 1) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD 1).memLp' 1)
  have hdy : IntegrableOn (dirD p Complex.I) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD Complex.I).memLp' 1)
  have hdbar (z : ℂ) :
      conj (dbar (fun w => conj (p w)) z) = (dirD p 1 z - Complex.I * dirD p Complex.I z) / 2 := by
    change conj ((dirD (fun w => conj (p w)) 1 z +
      Complex.I * dirD (fun w => conj (p w)) Complex.I z) / 2) = _
    rw [dirD_conj (hp.1.of_le (by simp)), dirD_conj (hp.1.of_le (by simp))]
    simp only [map_div₀, map_add, map_mul, Complex.conj_conj, Complex.conj_I, map_ofNat]
    ring
  calc
    _ = conj (∫ θ in Ioc (0 : ℝ) (2 * π), conj (p (γ θ)) * deriv γ θ) := by
      rw [← integral_conj]
      simp only [map_mul, Complex.conj_conj]
    _ = conj (2 * Complex.I * ∫ z in Ω, dbar (fun w => conj (p w)) z) := congrArg conj hg
    _ = -2 * Complex.I * ∫ z in Ω, conj (dbar (fun w => conj (p w)) z) := by
      rw [map_mul, ← integral_conj]
      simp only [map_mul, map_ofNat, Complex.conj_I]
      ring
    _ = ∫ z in Ω, (-Complex.I * dirD p 1 z - dirD p Complex.I z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      change -2 * Complex.I * conj (dbar (fun w => conj (p w)) z) =
        -Complex.I * dirD p 1 z - dirD p Complex.I z
      rw [hdbar]
      ring_nf; simp only [Complex.I_sq]; ring
    _ = _ := by rw [integral_sub (hdx.const_mul _) hdy, integral_const_mul]

private theorem hardyL2TestPair_smooth_value (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (f : smoothTraceTests) :
    hardyL2TestPair Ω hφ (h1Value Ω (smoothTraceH1 Ω f)) = ∫ z in Ω, f z * φ z := by
  rw [hardyL2TestPair_apply]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp Ω f).coeFn_toLp] with z hz
  rw [h1Value_smoothTraceH1, hz]

private theorem hardyL2TestPair_smooth_gradient (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (f : smoothTraceTests) (i : Fin 2) :
    hardyL2TestPair Ω hφ (h1Gradient Ω i (smoothTraceH1 Ω f)) =
      ∫ z in Ω, dirD (f : ℂ → ℂ) (coordDir i) z * φ z := by
  rw [hardyL2TestPair_apply]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz
  simpa only [h1Gradient_smoothTraceH1, dirD] using
    congrArg (fun w : ℂ => w * φ z) hz

private theorem h1FirstOrderConjugate_green_smooth {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (f : smoothTraceTests) :
    h1FirstOrderConjugateBoundaryTest hb hL hγ hφ (smoothTraceH1 Ω f) =
      h1FirstOrderConjugateInteriorTest Ω hφ (smoothTraceH1 Ω f) := by
  let p : ℂ → ℂ := fun z => f z * φ z
  have hp : TestFunction univ p :=
    ⟨f.property.1.mul hφ.1, f.property.2.1.mul_right, subset_univ _⟩
  have hleft : h1FirstOrderConjugateBoundaryTest hb hL hγ hφ (smoothTraceH1 Ω f) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * conj (deriv γ θ) := by
    rw [h1FirstOrderConjugateBoundaryTest_apply]
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
  rw [hleft, smooth_conjugate_firstOrder_green hb hL hγ hp,
    hproduct_integral, hproduct_integral]
  have hdir0 : coordDir (0 : Fin 2) = (1 : ℂ) := rfl
  have hdir1 : coordDir (1 : Fin 2) = Complex.I := rfl
  simp only [h1FirstOrderConjugateInteriorTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, hardyL2TestPair_smooth_gradient,
    hardyL2TestPair_smooth_value, hdir0, hdir1]

/-- The first-order conjugate Green identity for every actual H¹ vector.
It is an equality of bounded functionals on a dense set of smooth restrictions. -/
theorem h1FirstOrderConjugateBoundaryTest_eq_interior {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    h1FirstOrderConjugateBoundaryTest hb hL hγ hφ = h1FirstOrderConjugateInteriorTest Ω hφ := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1FirstOrderConjugateBoundaryTest hb hL hγ hφ).continuous
    (h1FirstOrderConjugateInteriorTest Ω hφ).continuous
  funext f
  rw [Function.comp_apply, Function.comp_apply, smoothTraceH1Lin_apply]
  exact h1FirstOrderConjugate_green_smooth hb hL hγ hφ f

/-- The raw first-order formula uses the genuine value, weak gradients,
and actual trace, with the unnormalized boundary measure dθ. -/
theorem h1_firstOrder_conjugate_green {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (u : NeumannH1 Ω) :
    -Complex.I * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
      ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * conj (deriv γ θ)) := by
  rw [← h1FirstOrderConjugateInteriorTest_apply Ω hφ u,
    ← h1FirstOrderConjugateBoundaryTest_eq_interior hb hL hγ hφ,
    h1FirstOrderConjugateBoundaryTest_apply]

private theorem hardy_zeroTrace_boundary_test {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (ht : h1BoundaryTrace hb hL hγ u = 0) (a : ℝ → ℂ) :
    (∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ * a θ) = 0 := by
  apply integral_eq_zero_of_ae
  rw [ht]
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) (2 * π)))] with θ hθ
  simp only [hθ, Pi.zero_apply, zero_mul]

private theorem hardy_gradient_test_factor {Ω : Set ℂ} (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) (ψ : ℂ → ℂ) :
    (∫ z in Ω, h1Gradient Ω 0 u z * ψ z) =
      Complex.I * ∫ z in Ω, h1Gradient Ω 1 u z * ψ z := by
  rw [hCR]
  calc
    _ = ∫ z in Ω, Complex.I * (h1Gradient Ω 1 u z * ψ z) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul Complex.I (h1Gradient Ω 1 u)] with z hz
      rw [hz]
      change (Complex.I * h1Gradient Ω 1 u z) * ψ z =
        Complex.I * (h1Gradient Ω 1 u z * ψ z)
      exact mul_assoc _ _ _
    _ = _ := integral_const_mul _ _

private theorem hardy_firstOrder_algebra (A B G : ℂ)
    (h : -Complex.I * (Complex.I * G + A) - (G + B) = 0) : A = Complex.I * B := by
  have he : -Complex.I * (Complex.I * G + A) - (G + B) = -Complex.I * A - B := by
    ring_nf; simp only [Complex.I_sq]; ring
  rw [he] at h
  apply sub_eq_zero.mp
  calc
    A - Complex.I * B = Complex.I * (-Complex.I * A - B) := by
      ring_nf; simp only [Complex.I_sq]; ring
    _ = 0 := by rw [h, mul_zero]

/-- CR and zero physical trace give the first-order distribution identity
against global compact tests, rather than only tests supported inside Ω. -/
theorem h1_antiholomorphic_global_test_of_zero_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∫ z in Ω, h1Value Ω u z * dirD φ 1 z) =
      Complex.I * ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z := by
  have h := h1_firstOrder_conjugate_green hb hL hγ hφ u
  rw [hardy_zeroTrace_boundary_test hb hL hγ u ht,
    hardy_gradient_test_factor u hCR] at h
  exact hardy_firstOrder_algebra _ _ _ h

private theorem hardy_trace_dirD_comm {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v w z : ℂ) :
    dirD (dirD φ v) w z = dirD (dirD φ w) v z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiable (by simp) z
  have hv : fderiv ℝ (dirD φ v) z w = fderiv ℝ (fderiv ℝ φ) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ φ x v) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hw : fderiv ℝ (dirD φ w) z v = fderiv ℝ (fderiv ℝ φ) z v w := by
    change fderiv ℝ (fun x => fderiv ℝ φ x w) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change fderiv ℝ (dirD φ v) z w = fderiv ℝ (dirD φ w) z v
  rw [hv, hw]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).eq w v

/-- The zero extension has zero distributional Laplacian, expressed using
its domain integral and arbitrary global compact smooth tests. -/
theorem h1_antiholomorphic_global_lap_test_of_zero_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∫ z in Ω, h1Value Ω u z * lap φ z) = 0 := by
  have hx := h1_antiholomorphic_global_test_of_zero_trace hb hL hγ u hCR ht (hφ.dirD 1)
  have hy := h1_antiholomorphic_global_test_of_zero_trace hb hL hγ u hCR ht
    (hφ.dirD Complex.I)
  have hc : (∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) Complex.I z) =
      ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) 1 z := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      change h1Value Ω u z * dirD (dirD φ 1) Complex.I z =
        h1Value Ω u z * dirD (dirD φ Complex.I) 1 z
      rw [hardy_trace_dirD_comm hφ.1])
  have hix := integrable_mul_test (Lp.memLp (h1Value Ω u)) ((hφ.dirD 1).dirD 1)
  have hiy := integrable_mul_test (Lp.memLp (h1Value Ω u))
    ((hφ.dirD Complex.I).dirD Complex.I)
  calc
    _ = (∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) 1 z) +
        ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z := by
      simp only [lap, mul_add]
      exact integral_add hix hiy
    _ = Complex.I * (Complex.I * ∫ z in Ω,
        h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z) +
        ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z := by
      rw [hx, hc, hy]
    _ = 0 := by rw [← mul_assoc, Complex.I_mul_I]; ring

private theorem hardy_zeroTrace_gradient_test {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) = 0 := by
  have hg := h1_doubleLayer_green hb hL hγ hφ u
  rw [h1_antiholomorphic_global_lap_test_of_zero_trace hb hL hγ u hCR ht hφ,
    zero_add, hardy_zeroTrace_boundary_test hb hL hγ u ht] at hg
  exact hg

private theorem hardy_gradient_inner_smooth (Ω : Set ℂ) (u : NeumannH1 Ω)
    (f : smoothTraceTests) (i : Fin 2) :
    ⟪h1Gradient Ω i (smoothTraceH1 Ω f), h1Gradient Ω i u⟫_ℂ =
      ∫ z in Ω, h1Gradient Ω i u z * dirD (fun w => conj (f w)) (coordDir i) z := by
  rw [h1Gradient_smoothTraceH1, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply', hz]
  rw [dirD_conj (f.property.1.of_le (by simp))]
  exact mul_comm _ _

/-- The zero-energy form equation is proved from CR and zero trace. It is
a conclusion here, not an assumed Neumann PDE for the Hardy input. -/
theorem h1HelmholtzForm_zero_of_antiholomorphic_zero_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0) : h1HelmholtzForm Ω 0 u = 0 := by
  have heq : (fun v : NeumannH1 Ω => ⟪v, h1HelmholtzForm Ω 0 u⟫_ℂ) =
      (fun _ => (0 : ℂ)) := by
    apply (denseRange_smoothTraceH1Lin hb hL).equalizer
      (continuous_id.inner continuous_const) continuous_const
    funext f
    change ⟪smoothTraceH1 Ω f, h1HelmholtzForm Ω 0 u⟫_ℂ = 0
    rw [h1HelmholtzForm_inner]
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    simp_rw [hardy_gradient_inner_smooth]
    exact hardy_zeroTrace_gradient_test hb hL hγ u hCR ht f.property.conj
  apply ext_inner_left ℂ
  intro v
  rw [inner_zero_right]
  exact congrFun heq v

/-- A genuine weak antiholomorphic H¹ vector with zero actual physical
trace is zero. The domain and parametrization are the original physical ones. -/
theorem neumannH1_eq_zero_of_antiholomorphic_zero_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0) : u = 0 := by
  have hu := h1HelmholtzForm_zero_of_antiholomorphic_zero_trace hb hL hγ u hCR ht
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨c, hcu⟩ := (h1HelmholtzForm_zero_eq_zero_iff_constant hb hL.1 u).mp hu
  have hc : c = 0 := by
    apply (boundaryLpConst_eq_zero_iff c).mp
    rw [← h1BoundaryTrace_h1Constant hb hL hγ c, ← hcu]
    exact ht
  apply h1Value_injective hL.1.1
  simp only [hcu, h1Value_h1Constant, hc, map_zero]

/-- Equal actual traces identify actual weak antiholomorphic H¹ vectors. -/
theorem neumannH1_eq_of_antiholomorphic_same_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u v : NeumannH1 Ω)
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hv : h1Gradient Ω 0 v = Complex.I • h1Gradient Ω 1 v)
    (ht : h1BoundaryTrace hb hL hγ u = h1BoundaryTrace hb hL hγ v) : u = v := by
  apply sub_eq_zero.mp
  apply neumannH1_eq_zero_of_antiholomorphic_zero_trace hb hL hγ (u - v)
  · rw [map_sub, map_sub, hu, hv, smul_sub]
  · rw [map_sub, ht, sub_self]

end PolyaNeumann

end
