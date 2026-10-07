module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.DenseEmbedding
public import RequestProject.NeumannBoundaryResolvent

/-!
# The genuine Herglotz wave as Neumann boundary data

The H¹ lift below is built from the actual Herglotz coefficient and its
actual classical derivatives. Complex Green's formula gives its prescribed
conormal load with ordinary parameter measure `dθ`. The continuous trace is
identified with its actual boundary values by a smooth cutoff which is one
near the closure of the domain.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Metric
open scoped Real InnerProductSpace ComplexConjugate

/-- Closing the derivative formula under differentiation proves genuine
smoothness of every Herglotz coefficient. -/
theorem contDiff_herglotzCoeff_infty {a : ℝ → ℂ}
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (herglotzCoeff k a m) := by
  have hn : ∀ n : ℕ, ∀ m : ℤ, ContDiff ℝ n (herglotzCoeff k a m) := by
    intro n
    induction n with
    | zero =>
        intro m
        exact contDiff_zero.2 (continuous_herglotzCoeff ha k m)
    | succ n ih =>
        intro m
        rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
          contDiff_succ_iff_fderiv]
        refine ⟨differentiable_herglotzCoeff ha k m, by simp, ?_⟩
        have hfd : fderiv ℝ (herglotzCoeff k a m) = fun z =>
            (-(Complex.I * k / 2) * herglotzCoeff k a (m + 1) z) • ContinuousLinearMap.id ℝ ℂ +
            (-(Complex.I * k / 2) * herglotzCoeff k a (m - 1) z) •
              Complex.conjCLE.toContinuousLinearMap := by
          funext z
          ext1 w
          rw [fderiv_herglotzCoeff_apply ha]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
            Complex.conjCLE_apply, smul_eq_mul]
          ring
        rw [hfd]
        exact ((contDiff_const.mul (ih (m + 1))).smul_const _).add
          ((contDiff_const.mul (ih (m - 1))).smul_const _)
  exact contDiff_infty.2 (fun n => hn n m)

lemma herglotzCoeff_memLp_domain {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) (m : ℤ) :
    MemLp (herglotzCoeff k a m) 2 (volume.restrict Ω) :=
  memLp_of_continuous_bounded hb (continuous_herglotzCoeff ha.intervalIntegrable k m)
    (fun z => norm_herglotzCoeff_le k m z)

lemma herglotzCoeff_memLp_deriv_domain {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) (m : ℤ) (i : Fin 2) :
    MemLp (fun z => fderiv ℝ (herglotzCoeff k a m) z (coordDir i)) 2 (volume.restrict Ω) := by
  have hc : Continuous (fun z => fderiv ℝ (herglotzCoeff k a m) z (coordDir i)) :=
    ((contDiff_herglotzCoeff ha.intervalIntegrable k m).continuous_fderiv (by simp)).clm_apply
      continuous_const
  apply memLp_of_continuous_bounded hb hc
  intro z
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_herglotzCoeff_le ha.intervalIntegrable k m z)
      (norm_nonneg _))

/-- The actual Herglotz wave in the weak-gradient H¹ space. Coefficient zero
is exactly `herglotzWave`, and its classical derivatives are retained. -/
def herglotzWaveH1 {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_of_contDiff_one (contDiff_herglotzCoeff ha.intervalIntegrable k 0)
    (herglotzCoeff_memLp_domain hb ha k 0)
    (herglotzCoeff_memLp_deriv_domain hb ha k 0))

@[simp] theorem h1Value_herglotzWaveH1 {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    h1Value Ω (herglotzWaveH1 hb ha k) =
      (herglotzCoeff_memLp_domain hb ha k 0).toLp (herglotzCoeff k a 0) := rfl

@[simp] theorem h1Gradient_herglotzWaveH1 {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) (i : Fin 2) :
    h1Gradient Ω i (herglotzWaveH1 hb ha k) =
      (herglotzCoeff_memLp_deriv_domain hb ha k 0 i).toLp
        (fun z => fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) := rfl

lemma herglotzTrace_memLp {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    MemLp (fun θ => herglotzCoeff k a 0 (γ θ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  exact MemLp.of_bound ((continuous_herglotzCoeff ha.intervalIntegrable k 0).comp
    hK.continuous).aestronglyMeasurable _
    (Eventually.of_forall fun θ => norm_herglotzCoeff_le k 0 (γ θ))

/-- The actual Dirichlet boundary values of the Herglotz wave, in ordinary
boundary L². -/
def herglotzDirichletL2 {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) : BoundaryL2 :=
  (herglotzTrace_memLp hγ ha k).toLp (fun θ => herglotzCoeff k a 0 (γ θ))

theorem herglotzDirichletL2_ae {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    (herglotzDirichletL2 hγ ha k : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => herglotzWave k a (γ θ) := by
  filter_upwards [(herglotzTrace_memLp hγ ha k).coeFn_toLp] with θ hθ
  exact hθ.trans (herglotzWave_eq k a (γ θ)).symm

lemma herglotzConormal_memLp_boundary {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    MemLp (herglotzConormal k a γ) 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable k hK
  exact MemLp.of_bound hgm.restrict B (Eventually.of_forall hgB)

/-- The actual density `D u(γ θ)(-i γ'(θ))`, not the unweighted unit-normal
derivative. Its boundary measure is ordinary `dθ`. -/
def herglotzConormalL2 {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) : BoundaryL2 :=
  (herglotzConormal_memLp_boundary hγ ha k).toLp (herglotzConormal k a γ)

theorem herglotzConormalL2_ae {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    (herglotzConormalL2 hγ ha k : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] herglotzConormal k a γ :=
  (herglotzConormal_memLp_boundary hγ ha k).coeFn_toLp

/-- A smooth compactly supported representative equal to the actual wave
near the closure of the domain identifies its genuine trace. -/
theorem exists_smoothTraceTest_herglotz {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    ∃ f : smoothTraceTests, smoothTraceH1 Ω f = herglotzWaveH1 hb ha k ∧
      ∀ θ ∈ Icc (0 : ℝ) (2 * π), f (γ θ) = herglotzCoeff k a 0 (γ θ) := by
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ closure Ω ⊆ ball (0 : ℂ) R := by
    obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : ℂ)
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  obtain ⟨χ, hχs, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  let f : smoothTraceTests := ⟨fun z => (χ z : ℂ) * herglotzCoeff k a 0 z,
    ⟨(Complex.ofRealCLM.contDiff.comp hχs).mul
      (contDiff_herglotzCoeff_infty ha.intervalIntegrable k 0),
      (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right,
      subset_univ _⟩⟩
  have hf : ∀ z ∈ closure Ω, f z = herglotzCoeff k a 0 z := by
    intro z hz
    simp [f, hχ1 z (ball_subset_closedBall (hR hz))]
  refine ⟨f, ?_, ?_⟩
  · apply h1Value_injective hL.1.1
    rw [h1Value_smoothTraceH1, h1Value_herglotzWaveH1]
    apply MemLp.toLp_congr
    filter_upwards [ae_restrict_mem hL.1.1.measurableSet] with z hz
    exact hf z (subset_closure hz)
  · intro θ hθ
    exact hf _ (frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ))

/-- The constructed continuous H¹ trace agrees with the actual Herglotz
boundary values; no trace identity is assumed. -/
theorem h1BoundaryTrace_herglotzWaveH1 {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    h1BoundaryTrace hb hL hγ (herglotzWaveH1 hb ha k) = herglotzDirichletL2 hγ ha k := by
  obtain ⟨f, hfu, hfγ⟩ := exists_smoothTraceTest_herglotz hb hL hγ ha k
  rw [← hfu]
  apply Lp.ext
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f,
    (herglotzTrace_memLp hγ ha k).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioc] with θ hθ ht hmem
  exact hθ.trans ((hfγ θ (Ioc_subset_Icc_self hmem)).trans ht.symm)

private lemma mixedHerglotzGreen_pointwise {a : ℝ → ℂ}
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (f : smoothTraceTests) (z : ℂ) :
    -(Complex.I * k) *
      (dbar (fun x => conj (f x) * herglotzCoeff k a 1 x) z +
        conj (dbar (fun x => f x * conj (herglotzCoeff k a (-1) x)) z)) =
      (∑ i : Fin 2, conj (fderiv ℝ (f : ℂ → ℂ) z (coordDir i)) *
        fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) -
          ((k ^ 2 : ℝ) : ℂ) * (conj (f z) * herglotzCoeff k a 0 z) := by
  have hf : DifferentiableAt ℝ (f : ℂ → ℂ) z := f.property.1.differentiable (by simp) z
  have h1 := differentiable_herglotzCoeff ha k 1 z
  have hm := differentiable_herglotzCoeff ha k (-1) z
  have hcf : DifferentiableAt ℝ (fun x => conj (f x)) z :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hf
  have hcm : DifferentiableAt ℝ (fun x => conj (herglotzCoeff k a (-1) x)) z :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hm
  unfold dbar
  simp only [fderiv_fun_mul hcf h1, fderiv_fun_mul hf hcm,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_conj_apply hf, fderiv_conj_apply hm, fderiv_herglotzCoeff_apply ha,
    Fin.sum_univ_two, coordDir, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num only [Int.reduceAdd, Int.reduceSub]
  simp only [map_add, map_mul, map_div₀, map_neg, map_one, map_ofNat,
    Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  push_cast
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four]
  ring

/-- Mixed Green identity between a genuine Herglotz wave and a smooth test
function. This is derived from the actual complex boundary Green formula. -/
theorem integral_test_mul_herglotzConormal {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) (f : smoothTraceTests) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (f (γ θ)) * herglotzConormal k a γ θ =
      ∫ z in Ω, ((∑ i : Fin 2, conj (fderiv ℝ (f : ℂ → ℂ) z (coordDir i)) *
        fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) -
          ((k ^ 2 : ℝ) : ℂ) * (conj (f z) * herglotzCoeff k a 0 z)) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    f.property.2.1 f.property.1 (by simp)
  obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
  obtain ⟨K1, hK1⟩ := lipschitzWith_herglotzCoeff ha.intervalIntegrable k 1
  obtain ⟨Km, hKm⟩ := lipschitzWith_herglotzCoeff ha.intervalIntegrable k (-1)
  let A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖
  have hA : ∀ m z, ‖herglotzCoeff k a m z‖ ≤ A := fun m z => norm_herglotzCoeff_le k m z
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hcfB : ∀ z, ‖conj (f z)‖ ≤ B := fun z => by rw [Complex.norm_conj]; exact hB z
  have hcmB : ∀ z, ‖conj (herglotzCoeff k a (-1) z)‖ ≤ A := fun z => by
    rw [Complex.norm_conj]
    exact hA (-1) z
  obtain ⟨KP, hKP⟩ := lipschitzWith_mul_of_bounded
    (Complex.isometry_conj.lipschitz.comp hKf) hK1 hcfB (hA 1)
  obtain ⟨KQ, hKQ⟩ := lipschitzWith_mul_of_bounded hKf
    (Complex.isometry_conj.lipschitz.comp hKm) hB hcmB
  let P : ℂ → ℂ := fun z => conj (f z) * herglotzCoeff k a 1 z
  let Q : ℂ → ℂ := fun z => f z * conj (herglotzCoeff k a (-1) z)
  have hPB : ∀ z, ‖P z‖ ≤ B * A := fun z => by
    rw [norm_mul]
    exact mul_le_mul (hcfB z) (hA 1 z) (norm_nonneg _) hB0
  have hQB : ∀ z, ‖Q z‖ ≤ B * A := fun z => by
    rw [norm_mul]
    exact mul_le_mul (hB z) (hcmB z) (norm_nonneg _) hB0
  have gP := integral_boundary_eq_dbar_of_bounded hb hL hγ hKP hPB
  have gQ := integral_boundary_eq_dbar_of_bounded hb hL hγ hKQ hQB
  have hiP := intervalIntegrable_comp_mul_deriv hKγ hKP.continuous
  have hiQ := intervalIntegrable_comp_mul_deriv hKγ hKQ.continuous
  change IntervalIntegrable (fun θ => P (γ θ) * deriv γ θ) volume 0 (2 * π) at hiP
  change IntervalIntegrable (fun θ => Q (γ θ) * deriv γ θ) volume 0 (2 * π) at hiQ
  change (∫ θ in (0 : ℝ)..(2 * π), P (γ θ) * deriv γ θ) =
    2 * Complex.I * ∫ z in Ω, dbar P z at gP
  change (∫ θ in (0 : ℝ)..(2 * π), Q (γ θ) * deriv γ θ) =
    2 * Complex.I * ∫ z in Ω, dbar Q z at gQ
  have hiQc : IntervalIntegrable (fun θ => conj (Q (γ θ) * deriv γ θ)) volume 0 (2 * π) := by
    rw [intervalIntegrable_iff] at hiQ ⊢
    exact hiQ.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      hiQ.aestronglyMeasurable) (Eventually.of_forall fun θ => by simp [Q])
  have hpt : ∀ θ, conj (f (γ θ)) * herglotzConormal k a γ θ =
      (k / 2 : ℂ) * (conj (Q (γ θ) * deriv γ θ) - P (γ θ) * deriv γ θ) := by
    intro θ
    rw [herglotzConormal_eq ha.intervalIntegrable]
    simp only [P, Q, map_mul, Complex.conj_conj]
    ring
  have hconj : ∫ θ in (0 : ℝ)..(2 * π), conj (Q (γ θ) * deriv γ θ) =
      conj (∫ θ in (0 : ℝ)..(2 * π), Q (γ θ) * deriv γ θ) := by
    rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le
      (by positivity), integral_conj]
  have hPd : IntegrableOn (dbar P) Ω :=
    Measure.integrableOn_of_bounded (M := (KP : ℝ)) hb.measure_lt_top.ne
      (measurable_dbar P).aestronglyMeasurable (Eventually.of_forall (norm_dbar_le hKP))
  have hQd : IntegrableOn (dbar Q) Ω :=
    Measure.integrableOn_of_bounded (M := (KQ : ℝ)) hb.measure_lt_top.ne
      (measurable_dbar Q).aestronglyMeasurable (Eventually.of_forall (norm_dbar_le hKQ))
  have hQc : IntegrableOn (fun z => conj (dbar Q z)) Ω :=
    hQd.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      hQd.aestronglyMeasurable) (Eventually.of_forall fun z => by simp)
  calc
    _ = -(Complex.I * k) * ((∫ z in Ω, dbar P z) + ∫ z in Ω, conj (dbar Q z)) := by
      simp_rw [hpt]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hiQc hiP,
        hconj, gQ, gP]
      simp only [map_mul, map_ofNat, Complex.conj_I]
      rw [← integral_conj]
      ring
    _ = ∫ z in Ω, -(Complex.I * k) * (dbar P z + conj (dbar Q z)) := by
      rw [integral_const_mul, integral_add hPd hQc]
    _ = _ := by
      refine setIntegral_congr_fun hL.1.1.measurableSet fun z _ => ?_
      exact mixedHerglotzGreen_pointwise ha.intervalIntegrable k f z

private lemma inner_toLp_pair {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, conj (f x) * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [RCLike.inner_apply', hfx, hgx]

private lemma integrable_conj_mul_of_memLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => conj (f x) * g x) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [RCLike.inner_apply', hfx, hgx]

/-- The mixed Green identity in the actual H¹ form, with the constructed
continuous trace and the actual conormal L² class. -/
theorem herglotzWaveH1_green_smooth {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) (f : smoothTraceTests) :
    ⟪smoothTraceH1 Ω f, h1HelmholtzForm Ω (k ^ 2) (herglotzWaveH1 hb ha k)⟫_ℂ =
      ⟪h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f), herglotzConormalL2 hγ ha k⟫_ℂ := by
  have hi : ∀ i : Fin 2, IntegrableOn
      (fun z => conj (fderiv ℝ (f : ℂ → ℂ) z (coordDir i)) *
        fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) Ω := fun i =>
    integrable_conj_mul_of_memLp ((f.property.dirD (coordDir i)).memLp' 2)
      (herglotzCoeff_memLp_deriv_domain hb ha k 0 i)
  have hm : IntegrableOn (fun z => conj (f z) * herglotzCoeff k a 0 z) Ω :=
    integrable_conj_mul_of_memLp (f.property.memLp' 2)
      (herglotzCoeff_memLp_domain hb ha k 0)
  rw [h1HelmholtzForm_inner, h1BoundaryTrace_inner_smooth]
  simp only [h1Value_smoothTraceH1, h1Gradient_smoothTraceH1,
    h1Value_herglotzWaveH1, h1Gradient_herglotzWaveH1, inner_toLp_pair]
  have hboundary : (∫ θ in Ioc (0 : ℝ) (2 * π),
      conj (f (γ θ)) * (herglotzConormalL2 hγ ha k : ℝ → ℂ) θ) =
      ∫ θ in (0 : ℝ)..(2 * π), conj (f (γ θ)) * herglotzConormal k a γ θ := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    apply integral_congr_ae
    filter_upwards [herglotzConormalL2_ae hγ ha k] with θ hθ
    rw [hθ]
  rw [hboundary, integral_test_mul_herglotzConormal hb hL hγ ha k f]
  simp only [Fin.sum_univ_two] at hi ⊢
  symm
  refine (integral_sub ((hi 0).add (hi 1))
    (hm.const_mul ((k ^ 2 : ℝ) : ℂ))).trans ?_
  exact congrArg₂ (fun x y : ℂ => x - y)
    (integral_add (hi 0) (hi 1))
    (integral_const_mul ((k ^ 2 : ℝ) : ℂ) (fun z => conj (f z) * herglotzCoeff k a 0 z))

/-- Every genuine Herglotz wave solves the weak Helmholtz equation with its
own actual conormal data. Smooth Green's formula extends to all H¹ tests
through the already established density theorem. -/
theorem herglotzWaveH1_isBoundaryNeumannSolution {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {a : ℝ → ℂ}
    (ha : IsDirDensity a) (k : ℝ) :
    IsBoundaryNeumannSolution hb hL hγ (k ^ 2)
      (herglotzConormalL2 hγ ha k) (herglotzWaveH1 hb ha k) := by
  apply (isBoundaryNeumannSolution_iff_form_eq hb hL hγ (k ^ 2) _ _).2
  apply ext_inner_left ℂ
  intro v
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on v
    (isClosed_eq (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro f
  rw [smoothTraceH1Lin_apply, h1BoundaryLoad_inner]
  exact herglotzWaveH1_green_smooth hb hL hγ ha k f

theorem herglotzWaveH1_sqrt_isBoundaryNeumannSolution {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {a : ℝ → ℂ}
    (ha : IsDirDensity a) {E : ℝ} (hE : 0 ≤ E) :
    IsBoundaryNeumannSolution hb hL hγ E
      (herglotzConormalL2 hγ ha (Real.sqrt E))
      (herglotzWaveH1 hb ha (Real.sqrt E)) := by
  simpa only [Real.sq_sqrt hE] using
    herglotzWaveH1_isBoundaryNeumannSolution hb hL hγ ha (Real.sqrt E)

/-- The actual variational NtD map takes the genuine conormal density of a
Herglotz wave to its genuine boundary values. Neither the BVP identity nor
its solvability is assumed. The nonresonance condition is used for uniqueness. -/
theorem neumannToDirichletL2_herglotzConormal {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    neumannToDirichletL2 hb hL hγ E (herglotzConormalL2 hγ ha (Real.sqrt E)) =
      herglotzDirichletL2 hγ ha (Real.sqrt E) := by
  rw [neumannToDirichletL2_trace_of_solution hb hL hγ hE hnr
    (herglotzWaveH1_sqrt_isBoundaryNeumannSolution hb hL hγ ha hE),
    h1BoundaryTrace_herglotzWaveH1 hb hL hγ ha (Real.sqrt E)]

/-- The quadratic form of the genuine NtD map on Herglotz data is the actual
interior Helmholtz energy. No Fourier or normalized Haar factor occurs,
because both boundary L² and the conormal density use ordinary `dθ`. -/
theorem neumannToDirichletL2_herglotz_energy {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    ⟪herglotzConormalL2 hγ ha (Real.sqrt E),
      neumannToDirichletL2 hb hL hγ E (herglotzConormalL2 hγ ha (Real.sqrt E))⟫_ℂ =
      ((E / 2 * ∫ z in Ω,
        (‖herglotzCoeff (Real.sqrt E) a 1 z‖ ^ 2 +
          ‖herglotzCoeff (Real.sqrt E) a (-1) z‖ ^ 2 -
            2 * ‖herglotzCoeff (Real.sqrt E) a 0 z‖ ^ 2) : ℝ) : ℂ) := by
  rw [neumannToDirichletL2_herglotzConormal hb hL hγ hE hnr ha]
  change ⟪(herglotzConormal_memLp_boundary hγ ha (Real.sqrt E)).toLp _,
    (herglotzTrace_memLp hγ ha (Real.sqrt E)).toLp _⟫_ℂ = _
  rw [inner_toLp_pair, ← intervalIntegral.integral_of_le (by positivity)]
  calc
    _ = ∫ θ in (0 : ℝ)..(2 * π),
        conj (herglotzConormal (Real.sqrt E) a γ θ) *
          herglotzWave (Real.sqrt E) a (γ θ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      change conj (herglotzConormal (Real.sqrt E) a γ θ) *
          herglotzCoeff (Real.sqrt E) a 0 (γ θ) =
        conj (herglotzConormal (Real.sqrt E) a γ θ) *
          herglotzWave (Real.sqrt E) a (γ θ)
      rw [herglotzWave_eq]
    _ = _ := by
      simpa only [Real.sq_sqrt hE] using
        integral_conj_herglotzConormal_mul_wave hb hL hγ ha.intervalIntegrable (Real.sqrt E)

end PolyaNeumann

end
