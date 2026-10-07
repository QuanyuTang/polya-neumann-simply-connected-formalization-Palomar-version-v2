module

public import RequestProject.LocalConformalTrace
public import RequestProject.NeumannNormalizedBoundary
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Topology.Order.Compact

/-!
# Actual boundary loads in supplied conformal coordinates

The physical density is an arbitrary element of the ordinary `dθ` boundary
L² space. Under the proved change of parameter its conormal density is
`τ' • (g ∘ τ)`. The one-dimensional Jacobian theorem constructs this as an
actual L² element, and density of smooth H¹ restrictions proves its pairing
with every actual H¹ trace. The normalized load is `Λ⁻¹ᐟ²` of the unitary
boundary Fourier transform, so its average Fourier coefficients carry
exactly `sqrt (2π)`. No constant-speed claim is made about the conformal
circle image, and coordinate existence remains a separate obligation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Real
open scoped InnerProductSpace ComplexConjugate

private theorem boundaryLoad_reparam_image_Icc {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) :
    τ '' Icc (0 : ℝ) (2 * π) = Icc (0 : ℝ) (2 * π) := by
  simpa only [hτ.zero, hτ.endpoint] using
    hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le
      (hτ.monotone.monotoneOn _)

private theorem boundaryLoad_integrable_reparam_weight
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) {q : ℝ → V}
    (hq : IntegrableOn q (Ioc (0 : ℝ) (2 * π))) :
    IntegrableOn (fun θ => deriv τ θ • q (τ θ)) (Ioc (0 : ℝ) (2 * π)) := by
  have hq' : IntegrableOn q (Icc (0 : ℝ) (2 * π)) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := q) (by finiteness)).mpr hq
  have hi := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Icc
    (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
    (hτ.monotone.monotoneOn (Icc (0 : ℝ) (2 * π))) q).mp
      (by simpa only [boundaryLoad_reparam_image_Icc hτ] using hq')
  exact (integrableOn_Icc_iff_integrableOn_Ioc
    (f := fun θ => deriv τ θ • q (τ θ)) (by finiteness)).mp hi

/-- Change of variables for an arbitrary complex integrand, with ordinary
coordinate measure on both cuts. -/
theorem integral_traceReparam_conormal {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (q : ℝ → ℂ) :
    (∫ θ in Ioc (0 : ℝ) (2 * π), deriv τ θ • q (τ θ)) =
      ∫ s in Ioc (0 : ℝ) (2 * π), q s := by
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Icc
    (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
    (hτ.monotone.monotoneOn (Icc (0 : ℝ) (2 * π))) q
  simpa only [boundaryLoad_reparam_image_Icc hτ, integral_Icc_eq_integral_Ioc]
    using h.symm

private theorem boundaryLoad_weighted_norm_sq_le (d K : ℝ) (z : ℂ)
    (hd : 0 ≤ d) (hdK : d ≤ K) : ‖d • z‖ ^ 2 ≤ K * (d * ‖z‖ ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, mul_pow]
  have h := mul_le_mul_of_nonneg_right hdK (mul_nonneg hd (sq_nonneg ‖z‖))
  nlinarith

/-- Every actual L² boundary density has an actual L² transformed conormal
density. The input need not have a continuous representative. -/
theorem traceReparamConormal_memLp {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) :
    MemLp (fun θ => deriv τ θ • g (τ θ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  have hg : IntegrableOn (g : ℝ → ℂ) (Ioc (0 : ℝ) (2 * π)) :=
    (Lp.memLp g).integrable (by norm_num)
  have hG := boundaryLoad_integrable_reparam_weight hτ hg
  have hg2 : IntegrableOn (fun θ => ‖g θ‖ ^ 2) (Ioc (0 : ℝ) (2 * π)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).mp (Lp.memLp g)
  have hweight : IntegrableOn (fun θ => deriv τ θ * ‖g (τ θ)‖ ^ 2)
      (Ioc (0 : ℝ) (2 * π)) := by
    simpa only [smul_eq_mul] using boundaryLoad_integrable_reparam_weight hτ hg2
  obtain ⟨K, hK⟩ := hτ.lipschitz
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr
  have hmeas : AEStronglyMeasurable (fun θ => ‖deriv τ θ • g (τ θ)‖ ^ 2)
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
    simp only [pow_two]
    exact hG.aestronglyMeasurable.norm.mul hG.aestronglyMeasurable.norm
  refine (hweight.const_mul (K : ℝ)).mono' hmeas (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact boundaryLoad_weighted_norm_sq_le (deriv τ θ) (K : ℝ) (g (τ θ))
    hτ.monotone.deriv_nonneg
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      (norm_deriv_le_of_lipschitz hK : ‖deriv τ θ‖ ≤ (K : ℝ))))

/-- The transformed conormal density in the actual ordinary boundary L²
space. Multiplication by the real derivative is the physical Jacobian. -/
def traceReparamConormalL2 {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) : BoundaryL2 :=
  (traceReparamConormal_memLp hτ g).toLp (fun θ => deriv τ θ • g (τ θ))

theorem traceReparamConormalL2_ae {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) :
    (traceReparamConormalL2 hτ g : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => deriv τ θ • g (τ θ) :=
  (traceReparamConormal_memLp hτ g).coeFn_toLp

private theorem boundaryLoad_complex_pairing_weight (a z : ℂ) (d : ℝ) :
    a * (d • z) = d • (a * z) := by
  simp only [Complex.real_smul]
  ring

/-- Reparametrization preserves the actual physical load pairing against
every H¹ vector. The identity is proved from Jacobian substitution on the
dense smooth restrictions, rather than supplied as a premise. -/
theorem h1ReparamBoundaryTrace_inner_conormalL2 {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (u : NeumannH1 Ω) (g : BoundaryL2) :
    ⟪h1ReparamBoundaryTrace hL hγ hτ u, traceReparamConormalL2 hτ g⟫_ℂ =
      ⟪h1BoundaryTrace hb hL hγ u, g⟫_ℂ := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v =>
      ⟪h1ReparamBoundaryTrace hL hγ hτ v, traceReparamConormalL2 hτ g⟫_ℂ =
        ⟪h1BoundaryTrace hb hL hγ v, g⟫_ℂ) u ?_ ?_
  · exact isClosed_eq
      ((h1ReparamBoundaryTrace hL hγ hτ).continuous.inner continuous_const)
      ((h1BoundaryTrace hb hL hγ).continuous.inner continuous_const)
  · intro f
    rw [smoothTraceH1Lin_apply, h1BoundaryTrace_inner_smooth hb hL hγ f g,
      L2.inner_def]
    calc
      _ = ∫ θ in Ioc (0 : ℝ) (2 * π),
          conj (f (γ (τ θ))) * (deriv τ θ • g (τ θ)) := by
        apply integral_congr_ae
        filter_upwards [h1ReparamBoundaryTrace_smooth_ae hb hL hγ hτ f,
          traceReparamConormalL2_ae hτ g] with θ htrace hload
        simp only [RCLike.inner_apply', htrace, hload]
      _ = ∫ θ in Ioc (0 : ℝ) (2 * π),
          deriv τ θ • (conj (f (γ (τ θ))) * g (τ θ)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun θ => boundaryLoad_complex_pairing_weight _ _ _
      _ = _ := integral_traceReparam_conormal hτ (fun θ => conj (f (γ θ)) * g θ)

private theorem boundaryLoad_sqrt_weight_cancel (w : ℝ) (hw : 0 < w) :
    (Real.sqrt w : ℂ) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
  rw [Real.rpow_neg hw.le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
  exact mul_inv_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr hw).ne')

private theorem boundaryLoad_half_pairing (q t b : L2Z)
    (hq : ∀ n, q n = (Real.sqrt (sobWeight n) : ℂ) * t n) :
    ⟪q, sobolevSmoothing (1 / 2 : ℝ) (by norm_num) b⟫_ℂ = ⟪t, b⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', hq, sobolevSmoothing, diagOp_apply,
    map_mul, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (sobWeight n) : ℂ) *
        ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (conj (t n) * b n) := by ring
    _ = _ := by rw [boundaryLoad_sqrt_weight_cancel _ (sobWeight_pos n), one_mul]

/-- The genuine weak load for the actual conformal half trace. Its unitary
Fourier normalization is `sqrt (2π) Λ⁻¹ᐟ² Ĝ`, including frequency zero. -/
def localConformalBoundaryLoad {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) : L2Z :=
  sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
    (boundaryFourier (traceReparamConormalL2 hτ g))

theorem localConformalBoundaryLoad_apply {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) (n : ℤ) :
    localConformalBoundaryLoad hτ g n =
      (Real.sqrt (2 * π) : ℂ) * ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        fourierCoeffOn two_pi_pos (traceReparamConormalL2 hτ g : ℝ → ℂ) n := by
  simp only [localConformalBoundaryLoad, sobolevSmoothing, diagOp_apply,
    boundaryFourier_apply]
  ring

section LocalConformal

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' Metric.ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' Metric.ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1))
    (hinj : InjOn F (Metric.ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' Metric.ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hhol hinj hC hcoord

/-- Pairing the actual conformal half trace with the constructed weak load
is exactly the ordinary physical boundary pairing, for all H¹ vectors. -/
theorem localConformalBoundaryLoad_inner
    (u : NeumannH1 (F '' Metric.ball (0 : ℂ) 1)) (g : BoundaryL2) :
    ⟪localConformalDiskHalfTrace hR F hFs hL u, localConformalBoundaryLoad hτ g⟫_ℂ =
      ⟪h1BoundaryTrace hb hL hγ u, g⟫_ℂ := by
  have hhalf := boundaryLoad_half_pairing
    (localConformalDiskHalfTrace hR F hFs hL u)
    (boundaryFourier (localConformalDiskH1Trace hR F hFs hL u))
    (boundaryFourier (traceReparamConormalL2 hτ g))
    (fun n => by simpa only [sobWeight] using
      localConformalDiskHalfTrace_apply hR F hFs hL u n)
  have hordinary :
      ⟪localConformalDiskH1Trace hR F hFs hL u, traceReparamConormalL2 hτ g⟫_ℂ =
        ⟪h1BoundaryTrace hb hL hγ u, g⟫_ℂ := by
    rw [← localConformalDiskH1Trace_eq_reparam hR F hFs hb hL hhol hinj hC hγ hτ hcoord]
    exact h1ReparamBoundaryTrace_inner_conormalL2 hb hL hγ hτ u g
  exact hhalf.trans ((boundaryFourier.inner_map_map _ _).trans hordinary)

/-- The same all-H¹ identity written as the actual ordinary coordinate
boundary integral; there is no hidden arc-length or Fourier scale. -/
theorem localConformalBoundaryLoad_inner_integral
    (u : NeumannH1 (F '' Metric.ball (0 : ℂ) 1)) (g : BoundaryL2) :
    ⟪localConformalDiskHalfTrace hR F hFs hL u, localConformalBoundaryLoad hτ g⟫_ℂ =
      ∫ θ in Ioc (0 : ℝ) (2 * π), conj (h1BoundaryTrace hb hL hγ u θ) * g θ := by
  rw [localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord u g,
    L2.inner_def]
  simp only [RCLike.inner_apply']

/-- An actual physical weak Neumann solution is the actual normalized
solution with the constructed conformal weak load. -/
theorem isBoundaryNeumannSolution_isNormalizedNeumannSolution {E : ℝ}
    (g : BoundaryL2) (u : NeumannH1 (F '' Metric.ball (0 : ℂ) 1))
    (hu : IsBoundaryNeumannSolution hb hL hγ E g u) :
    IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ g) u := by
  intro v
  exact (hu v).trans
    (localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord v g).symm

/-- Normalization preserves the full physical weak equation in both directions. -/
theorem isBoundaryNeumannSolution_iff_isNormalizedNeumannSolution {E : ℝ}
    (g : BoundaryL2) (u : NeumannH1 (F '' Metric.ball (0 : ℂ) 1)) :
    IsBoundaryNeumannSolution hb hL hγ E g u ↔
      IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
        (localConformalBoundaryLoad hτ g) u := by
  constructor
  · exact isBoundaryNeumannSolution_isNormalizedNeumannSolution
      hR F hFs hb hL hhol hinj hC hγ hτ hcoord g u
  · intro hu v
    exact (hu v).trans
      (localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord v g)

/-- The normalized resolvent with the constructed load solves the actual
physical Neumann problem whenever the actual Helmholtz form is invertible. -/
theorem normalizedNeumannPoisson_localConformalBoundaryLoad_isBoundarySolution
    {E : ℝ} (hE : IsUnit (h1HelmholtzForm (F '' Metric.ball (0 : ℂ) 1) E))
    (g : BoundaryL2) :
    IsBoundaryNeumannSolution hb hL hγ E g
      (normalizedNeumannPoisson (localConformalDiskHalfTrace hR F hFs hL) E
        (localConformalBoundaryLoad hτ g)) := by
  apply (isBoundaryNeumannSolution_iff_isNormalizedNeumannSolution
    hR F hFs hb hL hhol hinj hC hγ hτ hcoord g _).mpr
  exact normalizedNeumannPoisson_isSolution (localConformalDiskHalfTrace hR F hFs hL)
    hE (localConformalBoundaryLoad hτ g)

end LocalConformal

end PolyaNeumann

end
