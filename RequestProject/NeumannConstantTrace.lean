module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import RequestProject.TraceH1
public import RequestProject.NeumannZero
public import RequestProject.NeumannBoundaryPole
public import RequestProject.ReconTrace

/-!
# Constants and the actual boundary trace at zero energy

A compactly supported smooth function which is constant near the closure
of the domain represents the genuine weak-gradient H¹ constant. Agreement
of the constructed trace with smooth boundary values then identifies its
trace with the ordinary `dθ` boundary constant. The zero eigenspace consists
exactly of these constants, so the trace is injective on the zero form kernel.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Metric
open scoped Real InnerProductSpace

/-- The genuine constant H¹ vector, with zero weak derivatives. Finiteness
of the restricted measure follows from the boundedness of the domain. -/
def h1Constant {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (c : ℂ) : NeumannH1 Ω :=
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  h1Vector (isWeakGradient_const Ω c)

@[simp] theorem h1Value_h1Constant {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (c : ℂ) :
    h1Value Ω (h1Constant hb c) = Lp.const 2 (volume.restrict Ω) c := rfl

@[simp] theorem h1Gradient_h1Constant {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (c : ℂ) (i : Fin 2) : h1Gradient Ω i (h1Constant hb c) = 0 := rfl

/-- A real compact cutoff equals one on an open neighbourhood of the entire
closure of a bounded set. -/
theorem exists_cutoff_one_near_closure {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) :
    ∃ (χ : ℂ → ℝ) (U : Set ℂ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      IsOpen U ∧ closure Ω ⊆ U ∧ ∀ z ∈ U, χ z = 1 := by
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ closure Ω ⊆ ball (0 : ℂ) R := by
    obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : ℂ)
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  obtain ⟨χ, hχs, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  exact ⟨χ, ball (0 : ℂ) R, hχs, hχc, isOpen_ball, hR,
    fun z hz => hχ1 z (ball_subset_closedBall hz)⟩

/-- The actual H¹ constant has a compactly supported smooth representative
which agrees with the constant on a neighbourhood of the domain closure. -/
theorem exists_smoothTraceTest_h1Constant {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) (c : ℂ) :
    ∃ f : smoothTraceTests, smoothTraceH1 Ω f = h1Constant hb c ∧
      ∀ z ∈ closure Ω, f z = c := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨χ, U, hχs, hχc, _, hU, hχ1⟩ := exists_cutoff_one_near_closure hb
  let f : smoothTraceTests := ⟨fun z => (χ z : ℂ) * c,
    ⟨(Complex.ofRealCLM.contDiff.comp hχs).mul contDiff_const,
      (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right,
      subset_univ _⟩⟩
  have hf : ∀ z ∈ closure Ω, f z = c := by
    intro z hz
    simp [f, hχ1 z (hU hz)]
  refine ⟨f, ?_, hf⟩
  apply h1Value_injective hΩ
  rw [h1Value_smoothTraceH1, h1Value_h1Constant]
  apply Lp.ext
  filter_upwards [(f.property.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp,
    Lp.coeFn_const 2 (volume.restrict Ω) c,
    ae_restrict_mem hΩ.measurableSet] with z hto hconst hz
  exact hto.trans ((hf z (subset_closure hz)).trans hconst.symm)

/-- The actual trace of a genuine H¹ constant is the same boundary constant,
with respect to ordinary parameter measure `dθ`. -/
theorem h1BoundaryTrace_h1Constant {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (c : ℂ) :
    h1BoundaryTrace hb hL hγ (h1Constant hb c) =
      Lp.const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c := by
  obtain ⟨f, hfu, hf⟩ := exists_smoothTraceTest_h1Constant hb hL.1.1 c
  rw [← hfu]
  apply Lp.ext
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f,
    Lp.coeFn_const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c,
    ae_restrict_mem measurableSet_Ioc] with θ htrace hconst hθ
  have hmem : γ θ ∈ closure Ω :=
    frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ (Ioc_subset_Icc_self hθ))
  exact htrace.trans ((hf (γ θ) hmem).trans hconst.symm)

/-- A boundary constant vanishes as an L² class exactly when its value is
zero; the ordinary parameter interval has positive measure. -/
theorem boundaryLpConst_eq_zero_iff (c : ℂ) :
    Lp.const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c = 0 ↔ c = 0 := by
  haveI : NeZero (volume.restrict (Ioc (0 : ℝ) (2 * π))) := ⟨by
    intro hzero
    have hvol := Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Ioc, sub_zero] at hvol
    exact (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) hvol⟩
  constructor
  · intro hc
    have h : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * π)), c = 0 := by
      filter_upwards [Lp.coeFn_const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c,
        Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) (2 * π)))] with θ hconst hzero
      have heq := congrArg (fun u : BoundaryL2 => (u : ℝ → ℂ) θ) hc
      exact hconst.symm.trans (heq.trans hzero)
    obtain ⟨_, hc0⟩ := h.exists
    exact hc0
  · rintro rfl
    exact map_zero _

/-- The entire actual zero form kernel consists of the genuine constants. -/
theorem h1HelmholtzForm_zero_eq_zero_iff_constant {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω) (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω 0 u = 0 ↔ ∃ c : ℂ, u = h1Constant hb c := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := (mem_neumannEigenspace_zero_iff hΩ (h1Value Ω u)).mp
      (h1HelmholtzForm_kernel_mem Ω 0 u hu)
    refine ⟨c, h1Value_injective hΩ.1 ?_⟩
    simpa only [h1Value_h1Constant] using hc
  · rintro ⟨c, rfl⟩
    apply ext_inner_left ℂ
    intro v
    rw [h1HelmholtzForm_inner, inner_zero_right]
    simp

/-- Zero boundary trace forces a zero actual zero-energy Neumann vector. -/
theorem h1BoundaryTrace_neumannKernel_zero_eq_zero {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {u : NeumannH1 Ω}
    (hu : h1HelmholtzForm Ω 0 u = 0) (ht : h1BoundaryTrace hb hL hγ u = 0) :
    u = 0 := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨c, hcu⟩ := (h1HelmholtzForm_zero_eq_zero_iff_constant hb hL.1 u).mp hu
  have hconst : Lp.const 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) c = 0 := by
    rw [← h1BoundaryTrace_h1Constant hb hL hγ c, ← hcu]
    exact ht
  have hc : c = 0 := (boundaryLpConst_eq_zero_iff c).mp hconst
  apply h1Value_injective hL.1.1
  simp only [hcu, h1Value_h1Constant, hc, map_zero]

/-- The genuine boundary trace is injective on the actual zero-energy form
resonance space. Together with the positive-energy result this covers zero. -/
theorem h1BoundaryTrace_injective_neumannKernel_zero {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    Function.Injective ((h1BoundaryTrace hb hL hγ).comp (h1ResonantSpace Ω 0).subtypeL) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  apply Subtype.ext
  exact h1BoundaryTrace_neumannKernel_zero_eq_zero hb hL hγ u.property hu

end PolyaNeumann

end
