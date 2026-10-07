module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Topology.DenseEmbedding
public import RequestProject.NeumannBoundaryResolvent
public import RequestProject.Reconstruction

/-!
# The genuine trace is injective on Neumann eigenspaces

The classical double-layer Green identity first gives an equality of
continuous functionals on the dense smooth restrictions in H¹. It therefore
holds for every actual weak-gradient H¹ vector. If a Neumann eigenvector
has zero actual trace, its zero extension solves the global homogeneous
reconstruction equation. The already proved reconstruction uniqueness at
positive energy forces that extension, and hence the vector, to be zero.

The boundary measure is ordinary `dθ`, and the conormal test contains the
full density direction `-i γ′`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate

lemma smoothConormalTest_memLp {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    MemLp (fun θ => conj (fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)))) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kφ, hKφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  have hc : Continuous (fun θ => fderiv ℝ φ (γ θ)) :=
    (hφ.1.continuous_fderiv (by simp)).comp hKγ.continuous
  have hm : AEStronglyMeasurable
      (fun θ => fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hc.aestronglyMeasurable.prodMk
        ((measurable_deriv γ).const_mul _).neg.aestronglyMeasurable)
  apply MemLp.of_bound
    (Complex.continuous_conj.comp_aestronglyMeasurable hm).restrict
    ((Kφ : ℝ) * Kγ)
  apply Eventually.of_forall
  intro θ
  rw [Complex.norm_conj]
  calc
    _ ≤ ‖fderiv ℝ φ (γ θ)‖ * ‖-(Complex.I * deriv γ θ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (Kφ : ℝ) * Kγ := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
      exact mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hKφ)
        (norm_deriv_le_of_lipschitz hKγ) (norm_nonneg _) Kφ.coe_nonneg

/-- The actual conormal test, conjugated so that its pairing is linear in
the trace. It is constructed in L² rather than assumed bounded. -/
def smoothConormalTestL2 {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) : BoundaryL2 :=
  (smoothConormalTest_memLp hγ hφ).toLp
    (fun θ => conj (fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))))

/-- The actual double-layer boundary functional on H¹. -/
def h1DoubleLayerBoundaryTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (smoothConormalTestL2 hγ hφ)).comp (h1BoundaryTrace hb hL hγ)

/-- The interior Green expression is a continuous functional on the
genuine H¹ space. Its coefficients are actual smooth Laplacian/derivative
L² classes, not unspecified boundary regularity data. -/
def h1DoubleLayerInteriorTest (Ω : Set ℂ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ ((hφ.lap.conj.memLp' 2).toLp (fun z => conj (lap φ z)))).comp (h1Value Ω) +
    ∑ i : Fin 2,
      (innerSL ℂ (((hφ.dirD (coordDir i)).conj.memLp' 2).toLp
        (fun z => conj (dirD φ (coordDir i) z)))).comp (h1Gradient Ω i)

private lemma inner_conj_test_toLp {Ω : Set ℂ} {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (u : L2 Ω) :
    ⟪(hφ.conj.memLp' 2).toLp (fun z => conj (φ z)), u⟫_ℂ =
      ∫ z in Ω, u z * φ z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hφ.conj.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply, hz, Complex.conj_conj]

theorem h1DoubleLayerInteriorTest_apply (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (u : NeumannH1 Ω) :
    h1DoubleLayerInteriorTest Ω hφ u =
      (∫ z in Ω, h1Value Ω u z * lap φ z) +
        ∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z := by
  simp only [h1DoubleLayerInteriorTest, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    innerSL_apply_apply]
  exact congrArg₂ (fun x y : ℂ => x + y)
    (inner_conj_test_toLp hφ.lap (h1Value Ω u))
    (Finset.sum_congr rfl fun i _ =>
      inner_conj_test_toLp (hφ.dirD (coordDir i)) (h1Gradient Ω i u))

theorem h1DoubleLayerBoundaryTest_apply {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (u : NeumannH1 Ω) :
    h1DoubleLayerBoundaryTest hb hL hγ hφ u =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)) := by
  change ⟪smoothConormalTestL2 hγ hφ, h1BoundaryTrace hb hL hγ u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(smoothConormalTest_memLp hγ hφ).coeFn_toLp] with θ hθ
  simp only [smoothConormalTestL2, RCLike.inner_apply, hθ, Complex.conj_conj]

private lemma h1DoubleLayerBoundaryTest_smooth {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (f : smoothTraceTests) :
    h1DoubleLayerBoundaryTest hb hL hγ hφ (smoothTraceH1 Ω f) =
      doubleLayer γ (fun θ => f (γ θ)) φ := by
  rw [h1DoubleLayerBoundaryTest_apply, doubleLayer,
    intervalIntegral.integral_of_le (by positivity)]
  apply integral_congr_ae
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
  rw [hθ]

private lemma h1DoubleLayerInteriorTest_smooth (Ω : Set ℂ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (f : smoothTraceTests) :
    h1DoubleLayerInteriorTest Ω hφ (smoothTraceH1 Ω f) =
      ∫ z in Ω, (f z * lap φ z +
        ∑ i : Fin 2, dirD (f : ℂ → ℂ) (coordDir i) z * dirD φ (coordDir i) z) := by
  rw [h1DoubleLayerInteriorTest_apply]
  have h0 : (∫ z in Ω, h1Value Ω (smoothTraceH1 Ω f) z * lap φ z) =
      ∫ z in Ω, f z * lap φ z := by
    apply integral_congr_ae
    filter_upwards [(f.property.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp] with z hz
    rw [h1Value_smoothTraceH1, hz]
  have hi : ∀ i : Fin 2,
      (∫ z in Ω, h1Gradient Ω i (smoothTraceH1 Ω f) z * dirD φ (coordDir i) z) =
        ∫ z in Ω, dirD (f : ℂ → ℂ) (coordDir i) z * dirD φ (coordDir i) z := by
    intro i
    apply integral_congr_ae
    filter_upwards [((f.property.dirD (coordDir i)).memLp' 2
      (μ := volume.restrict Ω)).coeFn_toLp] with z hz
    rw [h1Gradient_smoothTraceH1]
    exact congrArg (fun w => w * dirD φ (coordDir i) z) hz
  rw [h0]
  simp_rw [hi]
  have hmass := integrable_mul_test (f.property.memLp' 2 (μ := volume.restrict Ω)) hφ.lap
  have hgrad : ∀ i : Fin 2, IntegrableOn
      (fun z => dirD (f : ℂ → ℂ) (coordDir i) z * dirD φ (coordDir i) z) Ω :=
    fun i => integrable_mul_test ((f.property.dirD (coordDir i)).memLp' 2) (hφ.dirD _)
  simp only [Fin.sum_univ_two]
  exact ((integral_add hmass ((hgrad 0).add (hgrad 1))).trans
    (congrArg (fun x : ℂ => (∫ z in Ω, f z * lap φ z) + x)
      (integral_add (hgrad 0) (hgrad 1)))).symm

/-- Green's double-layer identity for every actual weak-gradient H¹ vector.
It follows by equality of continuous functionals on the dense smooth
restrictions, so no extra regularity of the H¹ vector is imposed. -/
theorem h1DoubleLayerBoundaryTest_eq_interior {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    h1DoubleLayerBoundaryTest hb hL hγ hφ = h1DoubleLayerInteriorTest Ω hφ := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1DoubleLayerBoundaryTest hb hL hγ hφ).continuous
    (h1DoubleLayerInteriorTest Ω hφ).continuous
  funext f
  rw [Function.comp_apply, Function.comp_apply, smoothTraceH1Lin_apply,
    h1DoubleLayerBoundaryTest_smooth, h1DoubleLayerInteriorTest_smooth Ω]
  obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    f.property.2.1 f.property.1 (by simp)
  exact doubleLayer_eq_integral hb hL hγ hKf f.property.2.1 (fun θ _ => rfl) hφ.1

/-- The raw integral version of the generalized Green identity uses the
actual L² representatives of the value, weak gradients, and boundary trace. -/
theorem h1_doubleLayer_green {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (u : NeumannH1 Ω) :
    (∫ z in Ω, h1Value Ω u z * lap φ z) +
      (∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) =
        ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
          fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)) := by
  rw [← h1DoubleLayerInteriorTest_apply Ω hφ u,
    ← h1DoubleLayerBoundaryTest_eq_interior hb hL hγ hφ,
    h1DoubleLayerBoundaryTest_apply hb hL hγ hφ u]

private lemma inner_toLp_left_integral {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict Ω)) (u : L2 Ω) :
    ⟪hf.toLp f, u⟫_ℂ = ∫ z in Ω, conj (f z) * u z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  simp only [RCLike.inner_apply', hz]

/-- Testing the actual weak Neumann eigenvalue equation against `conj φ`
gives the unconjugated distributional identity needed for reconstruction. -/
theorem h1_neumannKernel_test_integral {Ω : Set ℂ} {E : ℝ}
    {u : NeumannH1 Ω} (hu : h1HelmholtzForm Ω E u = 0)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) =
      (E : ℂ) * ∫ z in Ω, h1Value Ω u z * φ z := by
  let f : smoothTraceTests := ⟨fun z => conj (φ z), hφ.conj⟩
  have hm : ⟪h1Value Ω (smoothTraceH1 Ω f), h1Value Ω u⟫_ℂ =
      ∫ z in Ω, h1Value Ω u z * φ z := by
    rw [h1Value_smoothTraceH1, inner_toLp_left_integral]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simp only [f, Complex.conj_conj, mul_comm]
  have hg : ∀ i : Fin 2,
      ⟪h1Gradient Ω i (smoothTraceH1 Ω f), h1Gradient Ω i u⟫_ℂ =
        ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z := by
    intro i
    rw [h1Gradient_smoothTraceH1, inner_toLp_left_integral]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    change conj (dirD (fun z => conj (φ z)) (coordDir i) z) *
      h1Gradient Ω i u z = _
    rw [dirD_conj (hφ.1.of_le (by simp)), Complex.conj_conj]
    exact mul_comm _ _
  have h := h1HelmholtzForm_inner Ω E (smoothTraceH1 Ω f) u
  rw [hu, inner_zero_right, hm] at h
  simp_rw [hg] at h
  exact sub_eq_zero.mp h.symm

/-- The actual L² zero extension of a domain function to the whole plane. -/
def neumannZeroExtension {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (u : L2 Ω) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  ((memLp_indicator_iff_restrict hΩ).2 (Lp.memLp u)).toLp (Ω.indicator (u : ℂ → ℂ))

theorem neumannZeroExtension_ae {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (u : L2 Ω) :
    (neumannZeroExtension hΩ u : ℂ → ℂ) =ᵐ[volume] Ω.indicator (u : ℂ → ℂ) :=
  ((memLp_indicator_iff_restrict hΩ).2 (Lp.memLp u)).coeFn_toLp

theorem restrictL2_neumannZeroExtension {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (u : L2 Ω) :
    restrictL2 Ω (neumannZeroExtension hΩ u) = u := by
  apply Lp.ext
  filter_upwards [restrictL2_coeFn Ω (neumannZeroExtension hΩ u),
    ae_restrict_of_ae (neumannZeroExtension_ae hΩ u), ae_restrict_mem hΩ] with z h1 h2 hz
  rw [h1, h2, Set.indicator_of_mem hz]

/-- Zero trace and the genuine weak Neumann equation imply that the zero
extension solves the actual homogeneous global reconstruction equation. -/
theorem neumannZeroExtension_isReconSol_zero {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} {u : NeumannH1 Ω}
    (hu : h1HelmholtzForm Ω E u = 0) (ht : h1BoundaryTrace hb hL hγ u = 0) :
    IsReconSol γ E (fun _ => 0)
      (neumannZeroExtension hL.1.1.measurableSet (h1Value Ω u)) := by
  intro φ hφ
  have hg := h1_doubleLayer_green hb hL hγ hφ u
  have hbzero : (∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
      fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) = 0 := by
    apply integral_eq_zero_of_ae
    rw [ht]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) (2 * π)))] with θ hθ
    simp only [hθ, Pi.zero_apply, zero_mul]
  rw [hbzero, h1_neumannKernel_test_integral hu hφ] at hg
  have hΩ := hL.1.1.measurableSet
  have hmass : IntegrableOn (fun z => h1Value Ω u z * lap φ z) Ω :=
    integrable_mul_test (Lp.memLp (h1Value Ω u)) hφ.lap
  have henergy : IntegrableOn (fun z => (E : ℂ) * (h1Value Ω u z * φ z)) Ω :=
    (integrable_mul_test (Lp.memLp (h1Value Ω u)) hφ).const_mul _
  have hinterior : (∫ z in Ω, h1Value Ω u z * (lap φ z + E * φ z)) = 0 := by
    rw [show (fun z => h1Value Ω u z * (lap φ z + E * φ z)) =
      (fun z => h1Value Ω u z * lap φ z + (E : ℂ) * (h1Value Ω u z * φ z)) by
        funext z
        ring,
      integral_add hmass henergy, integral_const_mul]
    exact hg
  calc
    _ = ∫ z, Ω.indicator (h1Value Ω u : ℂ → ℂ) z * (lap φ z + E * φ z) := by
      apply integral_congr_ae
      filter_upwards [neumannZeroExtension_ae hΩ (h1Value Ω u)] with z hz
      rw [hz]
    _ = ∫ z in Ω, h1Value Ω u z * (lap φ z + E * φ z) := by
      rw [← integral_indicator hΩ]
      congr 1
      funext z
      by_cases hz : z ∈ Ω <;> simp [hz]
    _ = 0 := hinterior
    _ = _ := by simp [doubleLayer]

private lemma isReconSol_zero (γ : ℝ → ℂ) (E : ℝ) :
    IsReconSol γ E (fun _ => 0) (0 : Lp ℂ 2 (volume : Measure ℂ)) := by
  intro φ _
  rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
  · simp [doubleLayer]
  · filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz
    simp only [hz, Pi.zero_apply, zero_mul]

/-- The actual trace has zero kernel on the weak Neumann eigenspace at
positive energy. Reconstruction uniqueness supplies the conclusion,
without an elliptic regularity or boundary uniqueness assumption. -/
theorem h1BoundaryTrace_neumannKernel_eq_zero {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E)
    {u : NeumannH1 Ω} (hu : h1HelmholtzForm Ω E u = 0)
    (ht : h1BoundaryTrace hb hL hγ u = 0) : u = 0 := by
  have hext := (neumannZeroExtension_isReconSol_zero hb hL hγ hu ht).unique hE
    (isReconSol_zero γ E)
  have hu0 : h1Value Ω u = 0 := by
    rw [← restrictL2_neumannZeroExtension hL.1.1.measurableSet (h1Value Ω u), hext, map_zero]
  apply h1Value_injective hL.1.1
  simpa only [map_zero] using hu0

/-- The actual H¹ Helmholtz kernel is exactly the already defined weak
Neumann eigenspace after applying the genuine value inclusion. -/
theorem h1HelmholtzForm_eq_zero_iff_neumannEigenspace {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (E : ℝ) (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω E u = 0 ↔ h1Value Ω u ∈ neumannEigenspace Ω E := by
  constructor
  · exact h1HelmholtzForm_kernel_mem Ω E u
  · rintro ⟨g, hg, heig⟩
    have hgrad : (fun i => h1Gradient Ω i u) = g :=
      (h1Value_weakGradient Ω u).unique hΩ hg
    apply ext_inner_left ℂ
    intro v
    rw [h1HelmholtzForm_inner, inner_zero_right]
    have hv := heig (h1Value Ω v) (fun i => h1Gradient Ω i v) (h1Value_weakGradient Ω v)
    rw [← hgrad] at hv
    exact sub_eq_zero.mpr hv

theorem h1BoundaryTrace_neumannEigen_eq_zero {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E)
    {u : NeumannH1 Ω} (hu : h1Value Ω u ∈ neumannEigenspace Ω E)
    (ht : h1BoundaryTrace hb hL hγ u = 0) : u = 0 :=
  h1BoundaryTrace_neumannKernel_eq_zero hb hL hγ hE
    ((h1HelmholtzForm_eq_zero_iff_neumannEigenspace hL.1.1 E u).2 hu) ht

/-- The genuine boundary trace restricted to the actual Helmholtz kernel
is injective. This is the map used for the physical pole residue vectors. -/
theorem h1BoundaryTrace_injective_neumannKernel {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) :
    Function.Injective ((h1BoundaryTrace hb hL hγ).comp (h1HelmholtzForm Ω E).ker.subtypeL) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  apply Subtype.ext
  exact h1BoundaryTrace_neumannKernel_eq_zero hb hL hγ hE u.property hu

/-- Independent genuine Neumann eigenvectors retain independent actual
boundary traces, as required for the pole residue. -/
theorem linearIndependent_h1BoundaryTrace_neumannKernel {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E)
    {ι : Type*} {v : ι → (h1HelmholtzForm Ω E).ker} (hv : LinearIndependent ℂ v) :
    LinearIndependent ℂ (fun i => h1BoundaryTrace hb hL hγ (v i : NeumannH1 Ω)) := by
  exact hv.map' ((h1BoundaryTrace hb hL hγ).comp (h1HelmholtzForm Ω E).ker.subtypeL).toLinearMap
    (LinearMap.ker_eq_bot.mpr (h1BoundaryTrace_injective_neumannKernel hb hL hγ hE))

end PolyaNeumann

end
