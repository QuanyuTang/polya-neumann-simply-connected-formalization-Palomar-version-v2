module

public import RequestProject.RiemannMappingBoundaryDerivative
public import RequestProject.LocalDirichletGenuineChart
public import RequestProject.PhysicalHardySupport
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Recovering the actual angular boundary parametrization

A smooth, nonstationary inverse boundary trace on the unit circle has a
genuine smooth local angular inverse.  Composing its physical graph curve
with that inverse proves regularity of the actual forward circle trace.
No smoothness of the forward trace or of a collar extension is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex
open scoped Topology

/-- The actual local angular coordinate of a normalized circle-valued curve. -/
def riemannMappingBoundaryPhase (α : ℝ → ℂ) (t₀ t : ℝ) : ℝ :=
  (Complex.log (α t / α t₀)).im

theorem riemannMappingBoundaryPhase_zero {α : ℝ → ℂ} {t₀ : ℝ}
    (h₀ : α t₀ ≠ 0) : riemannMappingBoundaryPhase α t₀ t₀ = 0 := by
  simp [riemannMappingBoundaryPhase, h₀]

/-- The principal logarithm is only used in a neighborhood of the value one. -/
theorem riemannMappingBoundaryPhase_contDiffAt {α : ℝ → ℂ} {t₀ : ℝ}
    (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀) (h₀ : α t₀ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (riemannMappingBoundaryPhase α t₀) t₀ := by
  have hratio : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => α t / α t₀) t₀ :=
    hα.div_const _
  have hslit : α t₀ / α t₀ ∈ Complex.slitPlane := by simp [h₀]
  have hlogOuter : ContDiffAt ℝ (⊤ : ℕ∞) Complex.log (α t₀ / α t₀) :=
    (Complex.contDiffAt_log hslit).restrict_scalars ℝ
  have hlog : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun t => Complex.log (α t / α t₀)) t₀ :=
    hlogOuter.comp (f := fun t : ℝ => α t / α t₀) (g := Complex.log) t₀ hratio
  exact Complex.imCLM.contDiff.contDiffAt.comp t₀ hlog

/-- The actual derivative of the normalized local phase. -/
theorem riemannMappingBoundaryPhase_hasDerivAt {α : ℝ → ℂ} {t₀ : ℝ}
    (hα : DifferentiableAt ℝ α t₀) (h₀ : α t₀ ≠ 0) :
    HasDerivAt (riemannMappingBoundaryPhase α t₀)
      (deriv α t₀ / α t₀).im t₀ := by
  have hslit : α t₀ / α t₀ ∈ Complex.slitPlane := by simp [h₀]
  have hlog := (hα.hasDerivAt.div_const (α t₀)).clog_real hslit
  unfold riemannMappingBoundaryPhase
  simpa only [div_self h₀, div_one, Function.comp_def,
    Complex.imCLM_apply] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt t₀ hlog

/-- A unit-modulus value is exactly recovered from its normalized phase. -/
theorem riemannMappingBoundaryPhase_circle {α : ℝ → ℂ} {t₀ t : ℝ}
    (h₀ : ‖α t₀‖ = 1) (ht : ‖α t‖ = 1) :
    α t = α t₀ * circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t) := by
  have hn₀ : α t₀ ≠ 0 := by
    intro h
    simp [h] at h₀
  have hratio : ‖α t / α t₀‖ = 1 := by rw [norm_div, ht, h₀]; norm_num
  have hn : α t / α t₀ ≠ 0 := by
    intro h
    simp [h] at hratio
  have hre : (Complex.log (α t / α t₀)).re = 0 := by
    rw [Complex.log_re, hratio, Real.log_one]
  have hlog : Complex.log (α t / α t₀) =
      (riemannMappingBoundaryPhase α t₀ t : ℂ) * Complex.I := by
    simpa only [riemannMappingBoundaryPhase, hre, Complex.ofReal_zero, zero_add]
      using (Complex.re_add_im (Complex.log (α t / α t₀))).symm
  have hexp : circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t) = α t / α t₀ := by
    simp only [circleMap_zero, Complex.ofReal_one, one_mul]
    rw [← hlog]
    exact Complex.exp_log hn
  rw [hexp]
  field_simp [hn₀]

theorem riemannMappingBoundaryPhase_circle_eventually {α : ℝ → ℂ} {t₀ : ℝ}
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) :
    ∀ᶠ t in 𝓝 t₀,
      α t = α t₀ * circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t) :=
  hcircle.mono fun _ ht => riemannMappingBoundaryPhase_circle hcircle.self_of_nhds ht

/-- Nonstationarity of the circle curve forces a nonzero real phase derivative. -/
theorem riemannMappingBoundaryPhase_deriv_ne_zero {α : ℝ → ℂ} {t₀ : ℝ}
    (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0) :
    deriv (riemannMappingBoundaryPhase α t₀) t₀ ≠ 0 := by
  have hn₀ : α t₀ ≠ 0 := by
    intro h
    simpa [h] using hcircle.self_of_nhds
  have hphase := riemannMappingBoundaryPhase_contDiffAt hα hn₀
  have hp := (hphase.differentiableAt (by simp)).hasDerivAt
  have ha : HasDerivAt α
      (α t₀ * (deriv (riemannMappingBoundaryPhase α t₀) t₀ •
        (circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t₀) * Complex.I))) t₀ :=
    (((hasDerivAt_circleMap 0 1 _).scomp t₀ hp).const_mul (α t₀)).congr_of_eventuallyEq
      (riemannMappingBoundaryPhase_circle_eventually hcircle)
  intro hz
  apply hd
  rw [ha.deriv, hz, zero_smul, mul_zero]

/-- A smooth inverse circle curve supplies the genuine local angular inverse.
The output is an actual function obtained from the real inverse function theorem. -/
theorem exists_riemannMappingBoundaryAngularInverse {α : ℝ → ℂ} {t₀ θ₀ : ℝ}
    (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = circleMap 0 1 θ₀) :
    ∃ g : ℝ → ℝ, g θ₀ = t₀ ∧ ContDiffAt ℝ (⊤ : ℕ∞) g θ₀ ∧
      HasDerivAt g (deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ θ₀ ∧
      ∀ᶠ θ in 𝓝 θ₀, α (g θ) = circleMap 0 1 θ := by
  let φ := riemannMappingBoundaryPhase α t₀
  have hn₀ : α t₀ ≠ 0 := by
    intro h
    simpa [h] using hcircle.self_of_nhds
  have hφ : ContDiffAt ℝ (⊤ : ℕ∞) φ t₀ :=
    riemannMappingBoundaryPhase_contDiffAt hα hn₀
  have hc : deriv φ t₀ ≠ 0 := riemannMappingBoundaryPhase_deriv_ne_zero hα hcircle hd
  have hdφ : HasDerivAt φ (deriv φ t₀) t₀ :=
    (hφ.differentiableAt (by simp)).hasDerivAt
  have hfd := hdφ.hasFDerivAt_equiv hc
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let e := hφ.toOpenPartialHomeomorph φ hfd hn
  have he : (e : ℝ → ℝ) = φ := rfl
  have hs : t₀ ∈ e.source := hφ.mem_toOpenPartialHomeomorph_source hfd hn
  have hφ₀ : φ t₀ = 0 := riemannMappingBoundaryPhase_zero hn₀
  have ht : (0 : ℝ) ∈ e.target := by
    simpa only [hφ₀] using hφ.image_mem_toOpenPartialHomeomorph_target hfd hn
  have he₀ : e.symm 0 = t₀ := by
    simpa only [he, hφ₀] using e.left_inv hs
  have hid : HasDerivAt (e : ℝ → ℝ) (deriv φ t₀) (e.symm 0) := by
    simpa only [he₀, he] using hdφ
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) (e.symm : ℝ → ℝ) 0 := by
    apply e.contDiffAt_symm_deriv hc ht hid
    simpa only [he₀, he] using hφ
  have hdi : HasDerivAt (e.symm : ℝ → ℝ) (deriv φ t₀)⁻¹ 0 :=
    e.hasDerivAt_symm ht hc hid
  let g : ℝ → ℝ := fun θ => e.symm (θ - θ₀)
  have hg₀ : g θ₀ = t₀ := by simp only [g, sub_self, he₀]
  have hgs : ContDiffAt ℝ (⊤ : ℕ∞) g θ₀ := by
    have hi' : ContDiffAt ℝ (⊤ : ℕ∞) (e.symm : ℝ → ℝ) (θ₀ - θ₀) := by
      simpa only [sub_self] using hi
    have hsub : ContDiffAt ℝ (⊤ : ℕ∞) (fun θ : ℝ => θ - θ₀) θ₀ :=
      contDiffAt_id.sub contDiffAt_const
    change ContDiffAt ℝ (⊤ : ℕ∞) ((e.symm : ℝ → ℝ) ∘ (fun θ : ℝ => θ - θ₀)) θ₀
    exact hi'.comp (f := fun θ : ℝ => θ - θ₀) (g := (e.symm : ℝ → ℝ)) θ₀ hsub
  have hgd : HasDerivAt g (deriv φ t₀)⁻¹ θ₀ := by
    simpa only [g, one_mul, mul_one, Function.comp_def, id] using
      hdi.comp_of_eq θ₀ ((hasDerivAt_id θ₀).sub_const θ₀) (by simp)
  have hshift : Tendsto (fun θ : ℝ => θ - θ₀) (𝓝 θ₀) (𝓝 0) := by
    have ht : Tendsto (fun θ : ℝ => θ - θ₀) (𝓝 θ₀) (𝓝 (θ₀ - θ₀)) :=
      (continuousAt_id.sub continuousAt_const :
        ContinuousAt (fun θ : ℝ => θ - θ₀) θ₀).tendsto
    simpa only [sub_self] using ht
  have hright : ∀ᶠ θ in 𝓝 θ₀, φ (g θ) = θ - θ₀ := by
    simpa only [g, he] using
      hshift.eventually (e.eventually_right_inverse ht)
  have hgt : Tendsto g (𝓝 θ₀) (𝓝 t₀) := by
    simpa only [hg₀] using hgs.continuousAt.tendsto
  have hrecover := hgt.eventually (riemannMappingBoundaryPhase_circle_eventually hcircle)
  refine ⟨g, hg₀, hgs, hgd, ?_⟩
  filter_upwards [hright, hrecover] with θ hθ hrec
  change α (g θ) = α t₀ * circleMap 0 1 (φ (g θ)) at hrec
  rw [hrec, hcenter, hθ, circleMap_zero_mul]
  simp only [one_mul]
  congr 1
  ring

/-- Genuine inverse parametrization regularizes the actual forward circle trace.
Only the inverse curve and the physical graph curve have regularity premises. -/
theorem physicalCircleTrace_contDiffAt_of_inverse_curve {F : ℂ → ℂ}
    {α β : ℝ → ℂ} {t₀ θ₀ : ℝ}
    (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hdα : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = circleMap 0 1 θ₀)
    (hβ : ContDiffAt ℝ (⊤ : ℕ∞) β t₀) (hdβ : deriv β t₀ ≠ 0)
    (hforward : ∀ᶠ t in 𝓝 t₀, F (α t) = β t) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace F) θ₀ ∧
      deriv (physicalCircleTrace F) θ₀ ≠ 0 := by
  obtain ⟨g, hg₀, hgs, hgd, hcircleG⟩ :=
    exists_riemannMappingBoundaryAngularInverse hα hcircle hdα hcenter
  have hc := riemannMappingBoundaryPhase_deriv_ne_zero hα hcircle hdα
  have hgt : Tendsto g (𝓝 θ₀) (𝓝 t₀) := by
    simpa only [hg₀] using hgs.continuousAt.tendsto
  have heq : physicalCircleTrace F =ᶠ[𝓝 θ₀] β ∘ g := by
    filter_upwards [hcircleG, hgt.eventually hforward] with θ hcircleθ hforwardθ
    simpa only [physicalCircleTrace, Function.comp_apply, hcircleθ] using hforwardθ
  have hβg : ContDiffAt ℝ (⊤ : ℕ∞) (β ∘ g) θ₀ := by
    have hβ' : ContDiffAt ℝ (⊤ : ℕ∞) β (g θ₀) := by rw [hg₀]; exact hβ
    exact hβ'.comp θ₀ hgs
  have hdβg : HasDerivAt (β ∘ g)
      ((deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ • deriv β t₀) θ₀ := by
    apply ((hβ.differentiableAt (by simp)).hasDerivAt).scomp_of_eq θ₀ hgd hg₀.symm
  refine ⟨hβg.congr_of_eventuallyEq heq, ?_⟩
  rw [(hdβg.congr_of_eventuallyEq heq).deriv]
  exact smul_ne_zero (inv_ne_zero hc) hdβ

/-- The actual physical graph, restricted to its bottom horizontal line. -/
def riemannMappingGraphBoundaryCurve (p c : ℂ) (hc : c ≠ 0)
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) : ℂ :=
  smoothDirichletGraphChart p c hc f hf (x : ℂ)

theorem riemannMappingGraphBoundaryCurve_contDiff (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (riemannMappingGraphBoundaryCurve p c hc f hf.continuous) :=
  (smoothDirichletGraphChart_contDiff p c hc hf).comp Complex.ofRealCLM.contDiff

theorem riemannMappingGraphBoundaryCurve_hasDerivAt (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) :
    HasDerivAt (riemannMappingGraphBoundaryCurve p c hc f hf.continuous)
      (c⁻¹ * (1 + ((deriv f x : ℝ) : ℂ) * Complex.I)) x := by
  have hd := (smoothDirichletGraphChart_hasFDerivAt p c hc hf (x : ℂ)).comp_hasDerivAt
    x (Complex.ofRealCLM.hasDerivAt (x := x))
  unfold riemannMappingGraphBoundaryCurve
  simpa only [Function.comp_def,
    Complex.ofRealCLM_apply, ContinuousLinearMap.smul_apply,
    smoothDirichletGraphDifferential_apply, Complex.ofReal_re,
    Complex.ofReal_one, Complex.one_re, mul_one, Complex.real_smul, smul_eq_mul] using hd

theorem riemannMappingGraphBoundaryCurve_deriv_ne_zero (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ) :
    deriv (riemannMappingGraphBoundaryCurve p c hc f hf.continuous) x ≠ 0 := by
  rw [(riemannMappingGraphBoundaryCurve_hasDerivAt p c hc hf x).deriv]
  apply mul_ne_zero (inv_ne_zero hc)
  intro hz
  have hr := congrArg Complex.re hz
  norm_num [Complex.mul_re] at hr

@[simp] theorem riemannMappingGraphBoundaryCurve_zero (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : f 0 = 0) :
    riemannMappingGraphBoundaryCurve p c hc f hf 0 = p := by
  simp [riemannMappingGraphBoundaryCurve, smoothDirichletGraphShear, hf₀]

section ActualInverseGraph

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)

include hb hS hsc hF hinj himage

/-- This interface uses the actual closed inverse and genuine bottom frontier.
The inverse graph smoothness and nonstationarity can be supplied by the Green
boundary-field and barrier theorems. -/
theorem riemannMapping_circleTrace_contDiffAt_of_inverse_graph
    {θ : ℝ} {p c : ℂ} (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf₀ : f 0 = 0)
    (hp : p = riemannMappingClosedExtension F (circleMap 0 1 θ))
    (hfront : ∀ᶠ x : ℝ in 𝓝 0,
      riemannMappingGraphBoundaryCurve p c hc f hf.continuous x ∈ frontier Ω)
    (hα : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0)
    (hdα : deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  let β := riemannMappingGraphBoundaryCurve p c hc f hf.continuous
  let α : ℝ → ℂ := fun x => riemannMappingClosedInverse F (β x)
  have hcircle : ∀ᶠ x in 𝓝 (0 : ℝ), ‖α x‖ = 1 :=
    hfront.mono fun _ hx =>
      riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hx
  have hcenter : α 0 = circleMap 0 1 θ := by
    change riemannMappingClosedInverse F
      (riemannMappingGraphBoundaryCurve p c hc f hf.continuous 0) = _
    rw [riemannMappingGraphBoundaryCurve_zero p c hc hf.continuous hf₀, hp]
    exact riemannMappingClosedInverse_left hb hS hsc F hF hinj himage
      (circleMap_mem_closedBall 0 zero_le_one θ)
  have hforward : ∀ᶠ x in 𝓝 (0 : ℝ), riemannMappingClosedExtension F (α x) = β x :=
    hfront.mono fun _ hx =>
      (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage
        (frontier_subset_closure hx)).2
  exact physicalCircleTrace_contDiffAt_of_inverse_curve hα hcircle hdα hcenter
    (riemannMappingGraphBoundaryCurve_contDiff p c hc hf).contDiffAt
    (riemannMappingGraphBoundaryCurve_deriv_ne_zero p c hc hf 0) hforward

/-- A genuine full-box membership chart supplies the bottom frontier premise;
mere mapping of the open upper half box is not used for that implication. -/
theorem riemannMapping_circleTrace_contDiffAt_of_genuine_inverse_graph
    {θ : ℝ} {p c : ℂ} (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf₀ : f 0 = 0)
    (hp : p = riemannMappingClosedExtension F (circleMap 0 1 θ))
    {a b : ℝ} (ha : 0 < a) (hb₀ : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im))
    (hα : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0)
    (hdα : deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  apply riemannMapping_circleTrace_contDiffAt_of_inverse_graph hb hS hsc F hF hinj himage
    hc hf hf₀ hp _ hα hdα
  have hI : ∀ᶠ x : ℝ in 𝓝 0, x ∈ Ioo (-a) a :=
    Ioo_mem_nhds (by linarith) ha
  exact hI.mono fun x hx =>
    smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous
      hb₀ hchart (abs_lt.mpr hx)

/-- All genuine inverse graph packets yield global smoothness and
nonstationarity of the actual angular trace of the closed extension. -/
theorem riemannMapping_circleTrace_contDiff_of_genuine_inverse_graphs
    (hgraphs : ∀ p ∈ frontier Ω,
      ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ),
        f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
        (∀ z : ℂ, |z.re| < a → |z.im| < b →
          (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun x : ℝ => riemannMappingClosedInverse F
            (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ∧
        deriv (fun x : ℝ => riemannMappingClosedInverse F
          (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) ∧
      ∀ θ : ℝ, deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  have hall (θ : ℝ) :
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
      deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
    let p := riemannMappingClosedExtension F (circleMap 0 1 θ)
    have hp : p ∈ frontier Ω :=
      riemannMappingClosedExtension_mem_frontier hb hS.isLipschitzDomain hsc F hF hinj himage
        (by simp only [norm_circleMap_zero, abs_one])
    obtain ⟨c, hc, f, hf, a, b, hf₀, ha, hb₀, hchart, hα, hdα⟩ := hgraphs p hp
    exact riemannMapping_circleTrace_contDiffAt_of_genuine_inverse_graph
      hb hS hsc F hF hinj himage hc hf hf₀ rfl ha hb₀ hchart hα hdα
  exact ⟨contDiff_iff_contDiffAt.mpr fun θ => (hall θ).1, fun θ => (hall θ).2⟩

end ActualInverseGraph

/-- A small actual closed rectangle avoids a point avoided at its center. -/
theorem exists_riemannMapping_halfBox_avoiding {Ψ : ℂ → ℂ} {w : ℂ}
    (hΨ : ContinuousAt Ψ 0) (hne : Ψ 0 ≠ w) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
      ∀ z ∈ smoothDirichletClosedHalfBox r r, Ψ z ≠ w := by
  have hev : {z : ℂ | Ψ z ≠ w} ∈ 𝓝 0 :=
    hΨ.eventually (eventually_ne_nhds hne)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  let r := min ρ (ε / 4)
  have hr : 0 < r := lt_min hρ (by positivity)
  have hrε : r ≤ ε / 4 := min_le_right _ _
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  intro z hz
  apply hball
  rw [mem_ball_zero_iff]
  have hzI : |z.im| ≤ r := by rw [abs_of_nonneg hz.2.1]; exact hz.2.2
  have hzN : ‖z‖ ≤ 2 * r := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * r := by linarith [hz.1]
  exact hzN.trans_lt (by linarith)

/-- The genuine original-domain gradient fields are transferred to Green
by its actual pole-subtracted datum.  The whole chosen closed rectangle
avoids the original pole; no boundary derivative of Green is assumed. -/
theorem exists_riemannMapping_genuine_green_smooth_boundary_fields {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (r : ℝ) (P Q : ℂ → ℂ),
      f 0 = 0 ∧ 0 < r ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let G := riemannMappingFlattenedGreen F Ψ
       let U := smoothDirichletHalfBox r r
       let V := smoothDirichletClosedHalfBox r r
       (∀ z : ℂ, |z.re| < r → |z.im| < r → (Ψ z ∈ Ω ↔ 0 < z.im)) ∧
       MapsTo Ψ U Ω ∧ (∀ z ∈ V, Ψ z ≠ F 0) ∧
       ContinuousOn (riemannMappingClosedInverse F ∘ Ψ) V ∧
       ContinuousOn G V ∧ ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
       ContinuousOn P V ∧ ContinuousOn Q V ∧
       EqOn P (dirD G 1) U ∧ EqOn Q (dirD G Complex.I) U ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => P (x : ℂ)) 0 ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Q (x : ℂ)) 0) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, ρ, X, Y, hc₁, hLip, hf₀, hA, hb₀,
    hρ, hρA, hρb, hchart, hclosed, hmap, huc, hus, huz,
    hXc, hYc, hXu, hYu, hXsmooth, hYsmooth⟩ :=
    exists_riemannMapping_genuine_gradient_smooth_boundary_fields
      hb hS hsc F hF hinj himage hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  let L := riemannMappingGreenLogDatum F d Ψ
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (Ψ : ℂ → ℂ) :=
    smoothDirichletGraphChart_contDiff p c hc hf
  have hΨ₀ : Ψ 0 = p := by
    simpa only [riemannMappingGraphBoundaryCurve, Complex.ofReal_zero] using
      riemannMappingGraphBoundaryCurve_zero p c hc hf.continuous hf₀
  have hpne : p ≠ F 0 := by
    intro he
    rw [he, hS.1.1.frontier_eq] at hp
    exact hp.2 (riemannMapping_pole_mem F himage)
  obtain ⟨r, hr, hrρ, hne⟩ := exists_riemannMapping_halfBox_avoiding
    Ψ.continuous.continuousAt (by rw [hΨ₀]; exact hpne) hρ
  let U := smoothDirichletHalfBox r r
  let V := smoothDirichletClosedHalfBox r r
  have hrA : r < A := hrρ.trans_lt (hρA.trans (by linarith))
  have hrb : r < b := hrρ.trans_lt hρb
  have hUρ : U ⊆ smoothDirichletHalfBox ρ ρ := by
    intro z hz
    exact ⟨hz.1.trans_le hrρ, hz.2.1, hz.2.2.trans_le hrρ⟩
  have hVρ : V ⊆ smoothDirichletClosedHalfBox ρ ρ := by
    intro z hz
    exact ⟨hz.1.trans hrρ, hz.2.1, hz.2.2.trans hrρ⟩
  have hUA : U ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans hrA, hz.2.1, hz.2.2.trans hrb⟩
  have hVA : V ⊆ smoothDirichletClosedHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans hrA.le, hz.2.1, hz.2.2.trans hrb.le⟩
  have hUV : U ⊆ V := by
    intro z hz
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hclosed' : MapsTo Ψ V (closure Ω) := fun z hz => hclosed (hVA hz)
  have hmap' : MapsTo Ψ U Ω := fun z hz => hmap (hUA hz)
  have hLs (z : ℂ) (hz : z ∈ V) : ContDiffAt ℝ (⊤ : ℕ∞) L z :=
    riemannMappingGreenLogDatum_contDiffAt F d hΨ.contDiffAt (hne z hz)
  have hLc : ContinuousOn L V := fun z hz => (hLs z hz).continuousAt.continuousWithinAt
  have hDs (w : ℂ) (z : ℂ) (hz : z ∈ V) : ContDiffAt ℝ (⊤ : ℕ∞) (dirD L w) z :=
    contDiffAt_infty_dirD (hLs z hz) w
  have hDc (w : ℂ) : ContinuousOn (dirD L w) V :=
    fun z hz => (hDs w z hz).continuousAt.continuousWithinAt
  have hV₀ : (0 : ℂ) ∈ V := by
    change |(0 : ℂ).re| ≤ r ∧ 0 ≤ (0 : ℂ).im ∧ (0 : ℂ).im ≤ r
    simpa only [Complex.zero_re, Complex.zero_im, abs_zero] using
      (show (0 : ℝ) ≤ r ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ r from ⟨hr.le, le_rfl, hr.le⟩)
  have hLsmooth (w : ℂ) : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => dirD L w (x : ℂ)) 0 :=
    (hDs w 0 hV₀).comp (f := fun x : ℝ => (x : ℂ)) (g := dirD L w) 0
      Complex.ofRealCLM.contDiff.contDiffAt
  let P : ℂ → ℂ := fun z => X z + dirD L 1 z
  let Q : ℂ → ℂ := fun z => Y z + dirD L Complex.I z
  let G := riemannMappingFlattenedGreen F Ψ
  have hsum : EqOn G (fun z => u z + L z) V := by
    intro z hz
    exact riemannMappingFlattenedGreen_eq_remainder_add_datum
      hb hS hsc F hF hinj himage d Ψ (hclosed' hz) (hne z hz)
  have hGc : ContinuousOn G V := ((huc.mono hVA).add hLc).congr hsum
  have hus' : ContDiffOn ℝ (⊤ : ℕ∞) u U := hus.mono hUA
  have hLs' : ContDiffOn ℝ (⊤ : ℕ∞) L U :=
    fun z hz => (hLs z (hUV hz)).contDiffWithinAt
  have hGs : ContDiffOn ℝ (⊤ : ℕ∞) G U :=
    (hus'.add hLs').congr (hsum.mono hUV)
  have hU : IsOpen U := isOpen_smoothDirichletHalfBox r r
  have hd (w : ℂ) : EqOn (dirD G w)
      (fun z => dirD u w z + dirD L w z) U := by
    intro z hz
    rw [dirichlet_bootstrap_dirD_eqOn hU (hsum.mono hUV) w hz]
    exact dirichlet_normal_dirD_add
      ((hus'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hLs z (hUV hz)).differentiableAt (by simp)) w
  have hP : EqOn P (dirD G 1) U := by
    intro z hz
    rw [hd 1 hz]
    change X z + dirD L 1 z = _
    rw [hXu (hUρ hz)]
  have hQ : EqOn Q (dirD G Complex.I) U := by
    intro z hz
    rw [hd Complex.I hz]
    change Y z + dirD L Complex.I z = _
    rw [hYu (hUρ hz)]
  refine ⟨c, hc, f, hf, r, P, Q, hf₀, hr, ?_, hmap', hne,
    (riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage).comp
      Ψ.continuous.continuousOn hclosed',
    hGc, hGs, (hXc.mono hVρ).add (hDc 1),
    (hYc.mono hVρ).add (hDc Complex.I), hP, hQ, hXsmooth.add (hLsmooth 1),
    hYsmooth.add (hLsmooth Complex.I)⟩
  intro z hzre hzim
  exact hchart z (hzre.trans hrA) (hzim.trans hrb)

/-- Genuine inverse graph regularity follows from the original physical
domain, its actual Green function and the proved finite-order boundary fields. -/
theorem exists_riemannMapping_genuine_regular_inverse_graph {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ),
      f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : ℝ => riemannMappingClosedInverse F
          (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ∧
      deriv (fun x : ℝ => riemannMappingClosedInverse F
        (riemannMappingGraphBoundaryCurve p c hc f hf.continuous x)) 0 ≠ 0 := by
  obtain ⟨c, hc, f, hf, r, P, Q, hf₀, hr, hchart, hmap, hne,
    hJ, hGc, hGs, hPc, hQc, hP, hQ, hPsmooth, hQsmooth⟩ :=
    exists_riemannMapping_genuine_green_smooth_boundary_fields hb hS hsc F hF hinj himage hp
  have hpole : ∀ z ∈ smoothDirichletHalfBox r r,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0 := by
    intro z hz
    exact hne z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hα := riemannMappingBoundaryTrace_contDiffAt_of_green_fields
    hb hS hsc F hF hinj himage p c hc hf hr hr hmap hpole hJ hPc hQc hP hQ hPsmooth hQsmooth
  have hdα := riemannMappingBoundaryTrace_deriv_ne_zero_of_green_fields
    hb hS hsc F hF hinj himage p c hc hf hf₀ hp hr hr hchart hmap hpole
      hJ hGc hGs hPc hQc hP hQ
  exact ⟨c, hc, f, hf, r, r, hf₀, hr, hr, hchart, hα, hdα⟩

/-- The actual closed Riemann map has a smooth, nonstationary angular
boundary trace under the original smooth-domain hypotheses. -/
theorem riemannMapping_circleTrace_contDiff {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) ∧
      ∀ θ : ℝ, deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 :=
  riemannMapping_circleTrace_contDiff_of_genuine_inverse_graphs hb hS hsc F hF hinj himage
    (fun _ hp => exists_riemannMapping_genuine_regular_inverse_graph hb hS hsc F hF hinj himage hp)

end PolyaNeumann

end
