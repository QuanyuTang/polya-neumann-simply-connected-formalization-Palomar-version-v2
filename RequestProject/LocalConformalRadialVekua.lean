module

public import RequestProject.PhysicalDrivenKernelConormal
public import RequestProject.NeumannHerglotzBoundary
public import RequestProject.HerglotzReduction
public import RequestProject.LocalConformalBoundaryGeometry
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The actual full zero-mode Vekua vector is the centered radial wave

The input sqrt(2pi) times the zero Fourier basis vector represents the
ordinary Hardy constant one. Its genuine primitive iterates are identified
with compact smooth restrictions of conj(z-p)^j/j!, using actual CR trace
uniqueness. The genuine H1 series then has the same L2 limit as the actual
centered Herglotz wave. The center is the boundary origin p=F(1).

This radial construction does not turn arbitrary normalized H^(-1/2)
conormal data into L2 boundary data.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate InnerProductSpace

local instance radialVekuaTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Normalized half-trace input for the actual ordinary Hardy constant one. -/
def radialVekuaInput : L2Z := (Real.sqrt (2 * Real.pi) : ℂ) • stdBasisZ 0

theorem radialVekuaInput_apply (n : ℤ) :
    radialVekuaInput n = if n = 0 then (Real.sqrt (2 * Real.pi) : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [radialVekuaInput, stdBasisZ_apply, lp.single_apply]
  · simp [radialVekuaInput, stdBasisZ_apply, lp.single_apply, hn]

theorem radialVekuaInput_nonpositive : IsNonpositiveFourierSupport radialVekuaInput := by
  intro n hn
  rw [radialVekuaInput_apply, if_neg (ne_of_gt hn)]

theorem normalizedHardyAverage_radialVekuaInput (n : ℤ) :
    normalizedHardyAverage radialVekuaInput n = if n = 0 then 1 else 0 := by
  have hc : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  by_cases hn : n = 0
  · subst n
    simp only [normalizedHardyAverage, fromL2, radialVekuaInput_apply,
      sobWeight, Int.cast_zero, abs_zero]
    norm_num
    have h2 : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have hπ : (Real.sqrt (Real.pi) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp [h2, hπ]
  · simp [normalizedHardyAverage, fromL2, radialVekuaInput_apply, hn]

theorem radialVekuaInput_raw_H1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) radialVekuaInput) := by
  classical
  unfold IsSobolevSeq
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  have hn0 : n ≠ 0 := by simpa only [Finset.mem_singleton] using hn
  simp [fromL2, radialVekuaInput_apply, hn0]

theorem hardyFourierTrace_radialVekuaInput (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage radialVekuaInput) θ = 1 := by
  classical
  simp only [hardyFourierTrace, normalizedHardyAverage_radialVekuaInput]
  simp

private def radialPrimitivePolynomial (p : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  conj (z - p) ^ j / (j.factorial : ℂ)

private theorem radialPrimitivePolynomial_contDiff (p : ℂ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPrimitivePolynomial p j) :=
  ((Complex.conjCLE.contDiff.comp (contDiff_id.sub contDiff_const)).pow j).div_const _

private theorem radialPrimitivePolynomial_fderiv (p : ℂ) (j : ℕ) (z v : ℂ) :
    fderiv ℝ (radialPrimitivePolynomial p j) z v =
      ((j : ℂ) * conj (z - p) ^ (j - 1) * conj v) / (j.factorial : ℂ) := by
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) z).sub_const p
  have hc := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z - p)).comp z hsub
  have h := congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
    ((hc.pow j).mul_const (j.factorial : ℂ)⁻¹).fderiv
  change fderiv ℝ (fun y : ℂ => conj (y - p) ^ j / (j.factorial : ℂ)) z v = _
  simpa only [radialPrimitivePolynomial, div_eq_mul_inv, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply, id_eq,
    Complex.conjCLE_apply, nsmul_eq_mul, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc]
    using h

private theorem exists_radialPrimitiveTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (j : ℕ) : ∃ f : smoothTraceTests,
      ∀ z ∈ closure Ω, (f : ℂ → ℂ) =ᶠ[𝓝 z] radialPrimitivePolynomial p j := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (radialPrimitivePolynomial_contDiff p j).contDiffOn
  exact ⟨⟨f, hf⟩, heq⟩

private def radialPrimitiveTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (j : ℕ) : smoothTraceTests :=
  Classical.choose (exists_radialPrimitiveTest hb p j)

private theorem radialPrimitiveTest_near {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (j : ℕ) {z : ℂ} (hz : z ∈ closure Ω) :
    (radialPrimitiveTest hb p j : ℂ → ℂ) =ᶠ[𝓝 z] radialPrimitivePolynomial p j :=
  Classical.choose_spec (exists_radialPrimitiveTest hb p j) z hz

private theorem radialPrimitiveTest_value_ae {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) (p : ℂ) (j : ℕ) :
    (h1Value Ω (smoothTraceH1 Ω (radialPrimitiveTest hb p j)) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] radialPrimitivePolynomial p j := by
  rw [h1Value_smoothTraceH1]
  filter_upwards [(smoothTraceTests_memLp Ω (radialPrimitiveTest hb p j)).coeFn_toLp,
    ae_restrict_mem hΩ.measurableSet] with z hz hmem
  exact hz.trans (radialPrimitiveTest_near hb p j (subset_closure hmem)).self_of_nhds

private theorem radialPrimitiveTest_cauchyRiemann {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (p : ℂ) (j : ℕ) :
    h1Gradient Ω 0 (smoothTraceH1 Ω (radialPrimitiveTest hb p j)) =
      Complex.I • h1Gradient Ω 1 (smoothTraceH1 Ω (radialPrimitiveTest hb p j)) := by
  apply Lp.ext
  rw [h1Gradient_smoothTraceH1, h1Gradient_smoothTraceH1]
  filter_upwards [(smoothTraceTests_memLp_deriv Ω (radialPrimitiveTest hb p j) 0).coeFn_toLp,
    (smoothTraceTests_memLp_deriv Ω (radialPrimitiveTest hb p j) 1).coeFn_toLp,
    Lp.coeFn_smul Complex.I
      ((smoothTraceTests_memLp_deriv Ω (radialPrimitiveTest hb p j) 1).toLp _),
    ae_restrict_mem hΩ.measurableSet] with z hx hy hs hz
  have hd : fderiv ℝ (radialPrimitiveTest hb p j : ℂ → ℂ) z =
      fderiv ℝ (radialPrimitivePolynomial p j) z :=
    (radialPrimitiveTest_near hb p j (subset_closure hz)).fderiv_eq
  calc
    _ = fderiv ℝ (radialPrimitiveTest hb p j : ℂ → ℂ) z (coordDir 0) := hx
    _ = Complex.I * fderiv ℝ (radialPrimitiveTest hb p j : ℂ → ℂ) z (coordDir 1) := by
      rw [hd]
      simp only [radialPrimitivePolynomial_fderiv,
        show coordDir 0 = (1 : ℂ) from rfl,
        show coordDir 1 = Complex.I from rfl, map_one, Complex.conj_I, mul_one]
      have hI : (Complex.I : ℂ) * (-Complex.I) = 1 := by
        rw [mul_neg, Complex.I_mul_I, neg_neg]
      simp only [div_eq_mul_inv]
      calc
        _ = (Complex.I * (-Complex.I)) *
            (↑j * (starRingEnd ℂ) (z - p) ^ (j - 1) * (↑j.factorial)⁻¹) := by
          rw [hI, one_mul]
        _ = _ := by ring
    _ = Complex.I * ((((smoothTraceTests_memLp_deriv Ω
        (radialPrimitiveTest hb p j) 1).toLp _ : L2 Ω) : ℂ → ℂ) z) := by rw [hy]
    _ = _ := by simpa only [Pi.smul_apply, smul_eq_mul] using hs.symm

private theorem radial_volterra_primitive_polynomial
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (j : ℕ) (θ : ℝ) :
    volterraPrimitiveIterate (fun s => conj (deriv γ s)) (fun _ => 1) j θ =
      conj (γ θ - γ 0) ^ j / (j.factorial : ℂ) := by
  induction j generalizing θ with
  | zero => simp [volterraPrimitiveIterate]
  | succ j ih =>
    have hd (s : ℝ) : HasDerivAt
        (fun t => conj (γ t - γ 0) ^ (j + 1) / ((j + 1).factorial : ℂ))
        (conj (deriv γ s) * (conj (γ s - γ 0) ^ j / (j.factorial : ℂ))) s := by
      have hz : HasDerivAt (fun t => conj (γ t - γ 0)) (conj (deriv γ s)) s := by
        simpa only [Complex.star_def] using
          ((hγ.differentiable_one s).hasDerivAt.sub_const (γ 0)).star
      convert (hz.pow (j + 1)).div_const ((j + 1).factorial : ℂ) using 1
      have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
      have hj : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
      field_simp [hf, hj]
    have hc : Continuous (fun s => conj (deriv γ s) *
        (conj (γ s - γ 0) ^ j / (j.factorial : ℂ))) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul
        (((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow j).div_const _)
    change (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      volterraPrimitiveIterate (fun t => conj (deriv γ t)) (fun _ => 1) j s) = _
    rw [show (fun s => conj (deriv γ s) *
        volterraPrimitiveIterate (fun t => conj (deriv γ t)) (fun _ => 1) j s) =
        (fun s => conj (deriv γ s) * (conj (γ s - γ 0) ^ j / (j.factorial : ℂ))) by
          funext s; rw [ih s]]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hc.intervalIntegrable _ _)]
    simp

private theorem radial_Lp_series_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (u : ℕ → Lp ℂ 2 μ) (v : Lp ℂ 2 μ)
    (f : ℕ → α → ℂ) (g : α → ℂ) (hs : HasSum u v)
    (hf : ∀ j, (u j : α → ℂ) =ᵐ[μ] f j)
    (hfm : ∀ j, AEStronglyMeasurable (f j) μ)
    (hpt : ∀ x, HasSum (fun j => f j x) (g x)) : (v : α → ℂ) =ᵐ[μ] g := by
  classical
  have heq (s : Finset ℕ) : ((∑ j ∈ s, u j : Lp ℂ 2 μ) : α → ℂ)
      =ᵐ[μ] fun x => ∑ j ∈ s, f j x := by
    induction s using Finset.induction_on with
    | empty => simpa [Pi.zero_def] using (Lp.coeFn_zero ℂ 2 μ)
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (u a) (∑ j ∈ s, u j), hf a, ih] with x hsum hfa his
      simp only [Pi.add_apply] at hsum
      rw [hsum, hfa, his]
  have hLp : TendstoInMeasure μ
      (fun N => ((∑ j ∈ Finset.range N, u j : Lp ℂ 2 μ) : α → ℂ)) atTop v :=
    tendstoInMeasure_of_tendsto_Lp hs.tendsto_sum_nat
  have hlim : TendstoInMeasure μ (fun N x => ∑ j ∈ Finset.range N, f j x) atTop g :=
    tendstoInMeasure_of_tendsto_ae
      (fun N => by
        have hfun : (∑ j ∈ Finset.range N, f j) =
            (fun x => ∑ j ∈ Finset.range N, f j x) := by
          funext x
          simp
        rw [← hfun]
        exact Finset.aestronglyMeasurable_sum (Finset.range N) fun j _ => hfm j)
      (Eventually.of_forall fun x => (hpt x).tendsto_sum_nat)
  exact tendstoInMeasure_ae_unique (hLp.congr (fun N => heq _) EventuallyEq.rfl) hlim

/-- Genuine centered radial Herglotz density, with ordinary value one at p. -/
def radialVekuaDensity (k : ℝ) (p : ℂ) : ℝ → ℂ :=
  centeredPolyDensity k p {0} (fun _ => 1)

theorem isDirDensity_radialVekuaDensity (k : ℝ) (p : ℂ) :
    IsDirDensity (radialVekuaDensity k p) :=
  isDirDensity_centeredPolyDensity k p {0} (fun _ => 1)

/-- Actual centered radial density with the indicated ordinary amplitude. -/
def radialVekuaScaledDensity (k : ℝ) (p a : ℂ) : ℝ → ℂ :=
  centeredPolyDensity k p {0} (fun _ => a)

theorem isDirDensity_radialVekuaScaledDensity (k : ℝ) (p a : ℂ) :
    IsDirDensity (radialVekuaScaledDensity k p a) :=
  isDirDensity_centeredPolyDensity k p {0} (fun _ => a)

theorem radialVekuaScaledDensity_eq_smul (k : ℝ) (p a : ℂ) :
    radialVekuaScaledDensity k p a = a • radialVekuaDensity k p := by
  funext φ
  simp [radialVekuaScaledDensity, radialVekuaDensity, centeredPolyDensity, polyDensity]
  ; ring

theorem radialVekuaScaledDensity_one (k : ℝ) (p : ℂ) :
    radialVekuaScaledDensity k p 1 = radialVekuaDensity k p := rfl

private theorem radial_boundaryFourier_ae {f : ℝ → ℂ} (v : BoundaryL2)
    (hv : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f) (n : ℤ) :
    boundaryFourier v n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

private theorem radial_herglotzWaveH1_smul {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) {a : ℝ → ℂ}
    (ha : IsDirDensity a) (c : ℂ) (k : ℝ) :
    herglotzWaveH1 hb (ha.const_smul c) k = c • herglotzWaveH1 hb ha k := by
  apply h1Value_injective hΩ
  rw [map_smul, h1Value_herglotzWaveH1, h1Value_herglotzWaveH1]
  apply Lp.ext
  filter_upwards [(herglotzCoeff_memLp_domain hb (ha.const_smul c) k 0).coeFn_toLp,
    (herglotzCoeff_memLp_domain hb ha k 0).coeFn_toLp,
    Lp.coeFn_smul c ((herglotzCoeff_memLp_domain hb ha k 0).toLp _)] with z hc hcoeff hs
  calc
    _ = herglotzCoeff k (c • a) 0 z := hc
    _ = c * herglotzCoeff k a 0 z := herglotzCoeff_smul_density a c k 0 z
    _ = c * ((((herglotzCoeff_memLp_domain hb ha k 0).toLp _ : L2 Ω) : ℂ → ℂ) z) := by
      rw [hcoeff]
    _ = (c • ((((herglotzCoeff_memLp_domain hb ha k 0).toLp _ : L2 Ω) : ℂ → ℂ) z)) := by
      rfl
     _ = (((c • (herglotzCoeff_memLp_domain hb ha k 0).toLp _) : L2 Ω) : ℂ → ℂ) z := by
       simpa only [Pi.smul_apply, smul_eq_mul] using hs.symm

private theorem exists_radialWaveTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    ∃ f : smoothTraceTests, smoothTraceH1 Ω f = herglotzWaveH1 hb ha k ∧
      ∀ z ∈ closure Ω, f z = herglotzCoeff k a 0 z := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (contDiff_herglotzCoeff_infty ha.intervalIntegrable k 0).contDiffOn
  let ff : smoothTraceTests := ⟨f, hf⟩
  have hval : ∀ z ∈ closure Ω, ff z = herglotzCoeff k a 0 z :=
    fun z hz => (heq z hz).self_of_nhds
  refine ⟨ff, ?_, hval⟩
  apply h1Value_injective hΩ
  rw [h1Value_smoothTraceH1, h1Value_herglotzWaveH1]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
  exact hval z (subset_closure hz)

private theorem exists_radialCoeffTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) (m : ℤ) :
    ∃ f : smoothTraceTests, ∀ z ∈ closure Ω, f z = herglotzCoeff k a m z := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (contDiff_herglotzCoeff_infty ha.intervalIntegrable k m).contDiffOn
  exact ⟨⟨f, hf⟩, fun z hz => (heq z hz).self_of_nhds⟩

private theorem radial_herglotzWirtingerD_ae {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    (h1WirtingerD Ω (herglotzWaveH1 hb ha k) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] fun z => -(Complex.I * k / 2) * herglotzCoeff k a 1 z := by
  let x : L2 Ω := (herglotzCoeff_memLp_deriv_domain hb ha k 0 0).toLp
    (fun z => fderiv ℝ (herglotzCoeff k a 0) z (coordDir 0))
  let y : L2 Ω := (herglotzCoeff_memLp_deriv_domain hb ha k 0 1).toLp
    (fun z => fderiv ℝ (herglotzCoeff k a 0) z (coordDir 1))
  rw [h1WirtingerD_apply, h1Gradient_herglotzWaveH1, h1Gradient_herglotzWaveH1]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (x - Complex.I • y),
    Lp.coeFn_sub x (Complex.I • y), Lp.coeFn_smul Complex.I y,
    (herglotzCoeff_memLp_deriv_domain hb ha k 0 0).coeFn_toLp,
    (herglotzCoeff_memLp_deriv_domain hb ha k 0 1).coeFn_toLp] with z hs hsub hi hx hy
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hi]
  simp only [Pi.smul_apply]
  rw [hx, hy]
  simp only [smul_eq_mul,
    fderiv_herglotzCoeff_apply ha.intervalIntegrable,
    show coordDir 0 = (1 : ℂ) from rfl,
    show coordDir 1 = Complex.I from rfl,
    zero_add, zero_sub, map_one, Complex.conj_I,
    one_mul]
  ring_nf
  rw [show (Complex.I : ℂ) ^ 3 = -Complex.I by
    rw [show (Complex.I : ℂ) ^ 3 = Complex.I ^ 2 * Complex.I by ring]
    rw [Complex.I_sq]
    ring]
  ring

private theorem radialVekuaDensity_wave (k : ℝ) (p z : ℂ) :
    herglotzWave k (radialVekuaDensity k p) z =
      herglotzWave k (monoDensity 0) (z - p) := by
  have hpoly : polyDensity k {0} (fun _ => (1 : ℂ)) = monoDensity 0 := by
    funext φ
    simp [polyDensity]
  rw [herglotzWave_eq, herglotzWave_eq]
  unfold radialVekuaDensity centeredPolyDensity
  rw [hpoly]
  unfold herglotzCoeff
  congr 2
  funext φ
  dsimp
  have hprod : monoDensity 0 φ * planeWave k (-p) φ * planeWave k z φ =
      monoDensity 0 φ * planeWave k (z - p) φ := by
    rw [mul_assoc]
    rw [mul_comm (planeWave k (-p) φ) (planeWave k z φ)]
    rw [← planeWave_add k z (-p) φ]
    rw [sub_eq_add_neg]
  rw [hprod]

private theorem radial_wave_hasSum {E : ℝ} (hE : 0 < E) (p z : ℂ) :
    HasSum (fun j : ℕ => physicalVekuaCoeff (E : ℂ) j * (z - p) ^ j *
      radialPrimitivePolynomial p j z)
      (herglotzWave (Real.sqrt E) (radialVekuaDensity (Real.sqrt E) p) z) := by
  have hk : Real.sqrt E ≠ 0 := (Real.sqrt_pos.mpr hE).ne'
  have hs := hasSum_vekuaMonoTerm hk 0 (z - p)
  rw [Real.sq_sqrt hE.le] at hs
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, inv_one, one_mul] at hs
  rw [radialVekuaDensity_wave]
  convert hs using 1
  funext j
  simp only [physicalVekuaCoeff, radialPrimitivePolynomial, vekuaMonoTerm,
    Nat.factorial_zero, Nat.cast_one, zero_add, mul_one, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem radial_affine_value_ae {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) (f : ℂ → ℂ)
    (hf : (h1Value Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω] f) (j : ℕ) :
    (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] fun z => (z - p) ^ j * f z := by
  induction j with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply, one_mul] using hf
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, h1Value_neumannH1AffineMultiplier]
    filter_upwards [neumannAffineL2Multiplier_ae p (neumannH1AffineBound_spec hb p)
      (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u)), ih] with z hm hi
    rw [hm, hi, pow_succ']
    ring

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "UF" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "VF" => localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "PB" => localConformalH1Pullback hR F hFs hL
local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
local notation "AF" => localConformalVekuaGradientA hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "VelF" => boundaryContinuousMultiplier (localConformalVelocityCircle F)
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NCF" => normalizedConormal hβF haF hgF

include hhol in
private theorem radial_primitive_trace (j : ℕ) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage ((JF ^ j) radialVekuaInput)) θ =
      radialPrimitivePolynomial (F 1) j (ΓF θ) := by
  rw [localConformalHardyPrimitive_pow_volterra_of_H1 hR F hFs hhol
    radialVekuaInput radialVekuaInput_nonpositive
    (isSobolevSeq_smul _ radialVekuaInput_raw_H1)]
  have hf : hardyFourierTrace (normalizedHardyAverage radialVekuaInput) = fun _ => 1 :=
    funext hardyFourierTrace_radialVekuaInput
  rw [hf, radial_volterra_primitive_polynomial hΓF]
  simp only [radialPrimitivePolynomial, physicalCircleTrace, circleMap_zero]
  norm_num

/-- The completed physical Hardy primitive iterates are the actual
antiholomorphic polynomials, proved using genuine CR trace uniqueness. -/
private theorem localConformalHardy_radial_primitive_eq (j : ℕ) :
    UF ((JF ^ j) radialVekuaInput) =
      smoothTraceH1 ΩF (radialPrimitiveTest hb (F 1) j) := by
  apply localConformalH1Pullback_injective hR F hFs hb hL hhol hinj hC hK
  apply neumannH1_eq_of_antiholomorphic_same_trace unitDisk_bounded
    isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
  · rw [localConformalH1Pullback_hardyExtension]
    exact diskHardyExtension_cauchyRiemann _
  · exact (localConformalH1Pullback_antiholomorphic_iff hR F hFs hb hL hhol hinj hC _).mpr
      (radialPrimitiveTest_cauchyRiemann hb hL.1.1 (F 1) j)
  · change TF (UF ((JF ^ j) radialVekuaInput)) =
      TF (smoothTraceH1 ΩF (radialPrimitiveTest hb (F 1) j))
    apply Lp.ext
    have hu := localConformalHardy_affine_primitive_trace_ae hR F hFs hb hL
      hhol hinj hC hK e he hsource hes radialVekuaInput
      radialVekuaInput_nonpositive radialVekuaInput_raw_H1 0 j
    simp only [pow_zero, ContinuousLinearMap.one_apply, one_mul] at hu
    filter_upwards [hu, localConformalDiskH1Trace_smooth_ae hR F hFs hb hL
      hhol hinj hC (radialPrimitiveTest hb (F 1) j)] with θ hu ht
    rw [hu, ht, radial_primitive_trace hR F hFs hhol j θ]
    have hz : F (circleMap 0 1 θ) ∈ closure ΩF := by
      rw [← localConformal_closedDisk_image_eq_closure hR F hFs]
      exact mem_image_of_mem F (sphere_subset_closedBall
        (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))
    exact ((radialPrimitiveTest_near hb (F 1) j hz).self_of_nhds).symm

/-- Actual L2 values of every completed primitive iterate retain the
factorial, full constant mode, and the physical boundary center. -/
theorem localConformalHardy_radial_primitive_value_ae (j : ℕ) :
    (h1Value ΩF (UF ((JF ^ j) radialVekuaInput)) : ℂ → ℂ)
      =ᵐ[volume.restrict ΩF] fun z => conj (z - F 1) ^ j / (j.factorial : ℂ) := by
  rw [localConformalHardy_radial_primitive_eq hR F hFs hb hL hhol hinj hC hK e he hsource hes]
  exact radialPrimitiveTest_value_ae hb hL.1.1 (F 1) j

/-- The actual physical H1 Vekua vector for the full zero Fourier mode
equals the actual centered radial Herglotz H1 vector. This equality comes
from the true completed H1 series and pointwise entire-wave series. -/
theorem localConformalVekuaH1_radial_eq_herglotz {E : ℝ} (hE : 0 < E) :
    VF (E : ℂ) radialVekuaInput =
      herglotzWaveH1 hb (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1))
        (Real.sqrt E) := by
  haveI : IsFiniteMeasure (volume.restrict ΩF) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  let term : ℕ → L2 ΩF := fun j => physicalVekuaCoeff (E : ℂ) j •
    h1Value ΩF ((neumannH1AffineMultiplier hb (F 1) ^ j)
      (UF ((JF ^ j) radialVekuaInput)))
  have hs : HasSum term (h1Value ΩF (VF (E : ℂ) radialVekuaInput)) := by
    simpa only [term, map_smul, localConformalVekuaH1AtBoundaryOrigin] using
      (h1Value ΩF).hasSum (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (F 1) (E : ℂ) radialVekuaInput)
  have ht (j : ℕ) : (term j : ℂ → ℂ) =ᵐ[volume.restrict ΩF]
      fun z => physicalVekuaCoeff (E : ℂ) j * (z - F 1) ^ j *
        radialPrimitivePolynomial (F 1) j z := by
    have hu := localConformalHardy_radial_primitive_value_ae hR F hFs hb hL hhol hinj hC hK
      e he hsource hes j
    have hm := radial_affine_value_ae hb (F 1) (UF ((JF ^ j) radialVekuaInput))
      (radialPrimitivePolynomial (F 1) j) hu j
    filter_upwards [Lp.coeFn_smul (physicalVekuaCoeff (E : ℂ) j)
      (h1Value ΩF ((neumannH1AffineMultiplier hb (F 1) ^ j)
        (UF ((JF ^ j) radialVekuaInput)))), hm] with z hs hm
    change (physicalVekuaCoeff (E : ℂ) j •
      h1Value ΩF ((neumannH1AffineMultiplier hb (F 1) ^ j)
        (UF ((JF ^ j) radialVekuaInput)))) z = _
    simp only [Pi.smul_apply, smul_eq_mul, hs, hm]
    ring
  have hval := radial_Lp_series_ae term (h1Value ΩF (VF (E : ℂ) radialVekuaInput))
    (fun j z => physicalVekuaCoeff (E : ℂ) j * (z - F 1) ^ j *
      radialPrimitivePolynomial (F 1) j z)
    (herglotzWave (Real.sqrt E) (radialVekuaDensity (Real.sqrt E) (F 1))) hs ht
    (fun j => ((continuous_const.mul ((continuous_id.sub continuous_const).pow j)).mul
      (radialPrimitivePolynomial_contDiff (F 1) j).continuous).aestronglyMeasurable)
    (fun z => radial_wave_hasSum hE (F 1) z)
  apply h1Value_injective hL.1.1
  apply Lp.ext
  rw [h1Value_herglotzWaveH1]
  filter_upwards [hval, (herglotzCoeff_memLp_domain hb
    (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)) (Real.sqrt E) 0).coeFn_toLp]
    with z hv hh
  exact hv.trans ((herglotzWave_eq _ _ z).trans hh.symm)

/-- Genuine initial jet of the actual radial wave at the actual boundary
origin; constant one gives e0/sqrt(2). -/
theorem localConformalRadial_herglotzVec_at_boundary_origin (E : ℝ) :
    herglotzVec (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1))
      (Real.sqrt E) (F 1) = (1 / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
  simpa only [radialVekuaDensity, antiPoly, Finset.sum_singleton, pow_zero, mul_one] using
    herglotzVec_centeredPolyDensity (Real.sqrt E) (F 1) {0} (fun _ => (1 : ℂ))

/-- The actual scaled radial density has its exact initial jet, including
the full zero component and the sqrt(2) convention of the jet space. -/
theorem localConformalRadial_scaled_herglotzVec_at_boundary_origin (E : ℝ) (a : ℂ) :
    herglotzVec (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a)
      (Real.sqrt E) (F 1) = (a / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
  simpa only [radialVekuaScaledDensity, antiPoly, Finset.sum_singleton, pow_zero, mul_one] using
    herglotzVec_centeredPolyDensity (Real.sqrt E) (F 1) {0} (fun _ => a)

/-- Amplitude sqrt(2) gives the genuine initial Hilbert jet e0. -/
theorem localConformalRadial_initial_e0 (E : ℝ) :
    herglotzVec (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1)
      (Real.sqrt 2 : ℂ)) (Real.sqrt E) (F 1) = basisVec 0 := by
  rw [localConformalRadial_scaled_herglotzVec_at_boundary_origin]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [div_self h2, one_smul]

/-- The scalar-normalized full zero mode has the genuine initial jet e0;
the physical H1 vector is sqrt(2) times the actual radial wave. -/
theorem localConformalVekuaH1_radial_initial_e0 {E : ℝ} (hE : 0 < E) :
    VF (E : ℂ) ((Real.sqrt 2 : ℂ) • radialVekuaInput) =
      herglotzWaveH1 hb (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1)
        (Real.sqrt 2 : ℂ)) (Real.sqrt E) := by
  rw [map_smul, localConformalVekuaH1_radial_eq_herglotz hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE]
  simpa only [radialVekuaScaledDensity_eq_smul] using
    (radial_herglotzWaveH1_smul hb hL.1.1
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1))
      (Real.sqrt 2 : ℂ) (Real.sqrt E)).symm

/-- Arbitrary scalar multiples preserve the actual radial realization,
so the projected observation correction is a true zero-mode Vekua vector. -/
theorem localConformalVekuaH1_radial_smul_eq {E : ℝ} (hE : 0 < E) (a : ℂ) :
    VF (E : ℂ) (a • radialVekuaInput) = a •
      herglotzWaveH1 hb (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1))
        (Real.sqrt E) := by
  rw [map_smul, localConformalVekuaH1_radial_eq_herglotz hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE]

/-- Equality with the actual amplitude-a Herglotz H1 vector, rather than
merely equality of formal coefficients. -/
theorem localConformalVekuaH1_radial_smul_eq_herglotz {E : ℝ} (hE : 0 < E) (a : ℂ) :
    VF (E : ℂ) (a • radialVekuaInput) =
      herglotzWaveH1 hb (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a)
        (Real.sqrt E) := by
  rw [localConformalVekuaH1_radial_smul_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE]
  simpa only [radialVekuaScaledDensity_eq_smul] using
    (radial_herglotzWaveH1_smul hb hL.1.1
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)) a (Real.sqrt E)).symm

/-- The actual coordinate trace of the radial completed vector equals the
ordinary centered Herglotz wave. No constant-speed property of Gamma is
used: Gamma is the true conformal circle trace. -/
theorem localConformalVekuaH1_radial_coordinate_trace_ae {E : ℝ}
    (hE : 0 < E) (a : ℂ) :
    (TF (VF (E : ℂ) (a • radialVekuaInput)) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
        fun θ => herglotzWave (Real.sqrt E)
          (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (ΓF θ) := by
  rw [localConformalVekuaH1_radial_smul_eq_herglotz hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE]
  obtain ⟨f, hfu, hf⟩ := exists_radialWaveTest hb hL.1.1
    (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (Real.sqrt E)
  rw [← hfu]
  filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f] with θ ht
  rw [ht, herglotzWave_eq]
  apply hf
  rw [← localConformal_closedDisk_image_eq_closure hR F hFs]
  exact mem_image_of_mem F (sphere_subset_closedBall
    (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))

/-- The true derivative companion A of the radial Vekua series has the
actual smooth coefficient-one trace. This follows from the genuine
Wirtinger derivative in L2 and value injectivity in the real H1 graph. -/
theorem localConformalRadial_gradientA_coordinate_trace_ae {E : ℝ} (hE : 0 < E) :
    (TF (AF (F 1) (E : ℂ) radialVekuaInput) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
        fun θ => -(Complex.I * (Real.sqrt E : ℂ) / 2) *
          herglotzCoeff (Real.sqrt E) (radialVekuaDensity (Real.sqrt E) (F 1)) 1 (ΓF θ) := by
  let ρ : ℝ → ℂ := radialVekuaDensity (Real.sqrt E) (F 1)
  let c : ℂ := -(Complex.I * (Real.sqrt E : ℂ) / 2)
  obtain ⟨f, hf⟩ := exists_radialCoeffTest hb
    (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)) (Real.sqrt E) 1
  have hAvalue : (h1Value ΩF (AF (F 1) (E : ℂ) radialVekuaInput) : ℂ → ℂ)
      =ᵐ[volume.restrict ΩF] fun z => c * herglotzCoeff (Real.sqrt E) ρ 1 z := by
    have hD : h1Value ΩF (AF (F 1) (E : ℂ) radialVekuaInput) =
        h1WirtingerD ΩF (VF (E : ℂ) radialVekuaInput) := by
      rw [localConformalVekuaGradientA_apply, map_smul]
      exact (localConformalVekuaH1_wirtingerD hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (F 1) (E : ℂ) radialVekuaInput).symm
    rw [hD, localConformalVekuaH1_radial_eq_herglotz hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hE]
    exact radial_herglotzWirtingerD_ae hb
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)) (Real.sqrt E)
  have hA : AF (F 1) (E : ℂ) radialVekuaInput = c • smoothTraceH1 ΩF f := by
    apply h1Value_injective hL.1.1
    rw [map_smul, h1Value_smoothTraceH1]
    apply Lp.ext
    filter_upwards [hAvalue, Lp.coeFn_smul c ((smoothTraceTests_memLp ΩF f).toLp _),
      (smoothTraceTests_memLp ΩF f).coeFn_toLp,
      ae_restrict_mem hL.1.1.measurableSet] with z ha hs hfv hz
    simp only [Pi.smul_apply, smul_eq_mul, ha, hs, hfv,
      hf z (subset_closure hz), ρ]
  rw [hA, map_smul]
  filter_upwards [Lp.coeFn_smul c (TF (smoothTraceH1 ΩF f)),
    localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f] with θ hs ht
  simp only [Pi.smul_apply, smul_eq_mul, hs, ht]
  have hz : F (circleMap 0 1 θ) ∈ closure ΩF := by
    rw [← localConformal_closedDisk_image_eq_closure hR F hFs]
    exact mem_image_of_mem F (sphere_subset_closedBall
      (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))
  exact congrArg (fun z : ℂ => c * z) (hf _ hz)

/-- The actual radial conormal belongs to genuine parameter L2 even for
the variable-speed conformal circle trace. This is a property of this
constructed smooth wave, not a gain for arbitrary normalized loads. -/
theorem localConformalRadial_conormal_memLp {L : NNReal}
    (hΓLip : LipschitzWith L ΓF) (E : ℝ) (a : ℂ) :
    MemLp (herglotzConormal (Real.sqrt E)
      (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) ΓF) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
  memLp_herglotzConormal
    (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (Real.sqrt E) hΓLip

/-- The true radial conormal has precisely the missing cut direction in
the original observation adjoint: amplitude one gives i times cutC. -/
theorem localConformalRadial_observationAdj_conormal {L : NNReal}
    (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W) (a : ℂ) :
    observationAdj W (herglotzConormal (Real.sqrt E)
      (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) ΓF) =
        (Complex.I * a) • cutC (W (2 * Real.pi)) (basisVec 0) := by
  have hclosed : ΓF (2 * Real.pi) = ΓF 0 := by
    simpa only [zero_add] using physicalCircleTrace_periodic F 0
  have hbase : ΓF 0 = F 1 := by
    simp [physicalCircleTrace, circleMap_zero]
  rw [(herglotzForm_eq hΓLip hclosed hW
    (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a)).1,
    hbase, localConformalRadial_scaled_herglotzVec_at_boundary_origin,
    map_smul, smul_smul]
  change (((Real.sqrt 2 : ℂ) * Complex.I) * (a / (Real.sqrt 2 : ℂ))) •
      cutC (W (2 * Real.pi)) (basisVec 0) = _
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  congr 1
  field_simp [h2]
  -- `field_simp` closes the scalar identity after clearing the nonzero square root.

/-- The genuine variable-speed coordinate conormal as an ordinary L2
class. Its measure is dtheta and its velocity is the actual Gamma'. -/
def localConformalRadialCoordinateLoad {L : NNReal}
    (hΓLip : LipschitzWith L ΓF) (E : ℝ) (a : ℂ) : BoundaryL2 :=
  (localConformalRadial_conormal_memLp F hΓLip E a).toLp
    (herglotzConormal (Real.sqrt E) (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) ΓF)

theorem localConformalRadialCoordinateLoad_ae {L : NNReal}
    (hΓLip : LipschitzWith L ΓF) (E : ℝ) (a : ℂ) :
    (localConformalRadialCoordinateLoad F hΓLip E a : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        herglotzConormal (Real.sqrt E)
          (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) ΓF :=
  (localConformalRadial_conormal_memLp F hΓLip E a).coeFn_toLp

theorem localConformalRadialCoordinateLoad_smul {L : NNReal}
    (hΓLip : LipschitzWith L ΓF) (E : ℝ) (a : ℂ) :
    localConformalRadialCoordinateLoad F hΓLip E a =
      a • localConformalRadialCoordinateLoad F hΓLip E 1 := by
  apply Lp.ext
  filter_upwards [localConformalRadialCoordinateLoad_ae F hΓLip E a,
    localConformalRadialCoordinateLoad_ae F hΓLip E 1,
    Lp.coeFn_smul a (localConformalRadialCoordinateLoad F hΓLip E 1)] with θ ha h1 hs
  simp only [Pi.smul_apply, smul_eq_mul, ha, hs, h1,
    radialVekuaScaledDensity_eq_smul,
    herglotzConormal_smul_density
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1))]
  simp only [one_mul]

/-- The actual ordinary L2 representative retains exactly the original
observation adjoint, including the boundary-origin cut direction. -/
theorem localConformalRadialCoordinateLoad_observationAdj {L : NNReal}
    (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W) (a : ℂ) :
    observationAdj W (localConformalRadialCoordinateLoad F hΓLip E a : ℝ → ℂ) =
      (Complex.I * a) • cutC (W (2 * Real.pi)) (basisVec 0) := by
  rw [← localConformalRadial_observationAdj_conormal F hΓLip hW a]
  rw [observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_congr_ae
  filter_upwards [localConformalRadialCoordinateLoad_ae F hΓLip E a] with θ hθ
  rw [hθ]

include hb hL hhol hinj hC hK e he hsource hes in
private theorem radial_normalizedConormal_eq_coordinateLoad_one {L : NNReal}
    (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E) :
    NCF (E : ℂ) radialVekuaInput =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
        (boundaryFourier (localConformalRadialCoordinateLoad F hΓLip E 1)) := by
  let ρ : ℝ → ℂ := radialVekuaDensity (Real.sqrt E) (F 1)
  let c : ℂ := -(Complex.I * (Real.sqrt E : ℂ) / 2)
  let f : ℝ → ℂ := fun θ => herglotzCoeff (Real.sqrt E) ρ 0 (ΓF θ)
  let df : ℝ → ℂ := fun θ => c *
    (deriv ΓF θ * herglotzCoeff (Real.sqrt E) ρ 1 (ΓF θ) +
      conj (deriv ΓF θ) * herglotzCoeff (Real.sqrt E) ρ (-1) (ΓF θ))
  let A : BoundaryL2 := VelF (TF (AF (F 1) (E : ℂ) radialVekuaInput))
  let r : BoundaryL2 := localConformalRadialCoordinateLoad F hΓLip E 1
  let d : BoundaryL2 := (2 : ℂ) • A - Complex.I • r
  have hA : (A : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      fun θ => deriv ΓF θ * (c * herglotzCoeff (Real.sqrt E) ρ 1 (ΓF θ)) := by
    filter_upwards [boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
        (TF (AF (F 1) (E : ℂ) radialVekuaInput)),
      localConformalRadial_gradientA_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hE] with θ hm ha
    rw [hm, ha, localConformalVelocityCircle_apply hR F hFs]
  have hd : (d : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] df := by
    filter_upwards [Lp.coeFn_sub ((2 : ℂ) • A) (Complex.I • r),
      Lp.coeFn_smul (2 : ℂ) A, Lp.coeFn_smul Complex.I r, hA,
      localConformalRadialCoordinateLoad_ae F hΓLip E 1] with θ hs h2 hi ha hr
    simp only [d, r, hs, h2, hi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hr,
      radialVekuaScaledDensity_one, herglotzConormal_eq
        (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)).intervalIntegrable, df, c, ρ]
    ring_nf
  have ht : (TF (VF (E : ℂ) radialVekuaInput) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f := by
    simpa only [one_smul, radialVekuaScaledDensity_one, herglotzWave_eq, f, ρ] using
      localConformalVekuaH1_radial_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hE 1
  have hdf (θ : ℝ) : HasDerivAt f (df θ) θ := by
    have h := (differentiable_herglotzCoeff
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)).intervalIntegrable
        (Real.sqrt E) 0 (ΓF θ)).hasFDerivAt.comp_hasDerivAt θ
          ((hΓF).differentiable_one θ).hasDerivAt
    simpa only [f, df, c, ρ, Function.comp_def,
      fderiv_herglotzCoeff_apply
        (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)).intervalIntegrable,
      zero_add, zero_sub] using h
  have hdc : Continuous df := by
    exact continuous_const.mul
      (((hΓF).continuous_deriv_one.mul
        ((continuous_herglotzCoeff
          (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)).intervalIntegrable
            (Real.sqrt E) 1).comp (hΓF).continuous)).add
        ((Complex.continuous_conj.comp (hΓF).continuous_deriv_one).mul
          ((continuous_herglotzCoeff
            (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1)).intervalIntegrable
              (Real.sqrt E) (-1)).comp (hΓF).continuous)))
  have hp : f 0 = f (2 * Real.pi) := by
    have hclosed : ΓF (2 * Real.pi) = ΓF 0 := by
      simpa only [zero_add] using physicalCircleTrace_periodic F 0
    dsimp only [f]
    rw [hclosed]
  have hcoeff (n : ℤ) : boundaryFourier d n =
      (Complex.I * (n : ℂ)) * boundaryFourier (TF (VF (E : ℂ) radialVekuaInput)) n := by
    rw [radial_boundaryFourier_ae d hd n,
      radial_boundaryFourier_ae _ ht n, fourierCoeffOn_deriv hdf hdc hp n]
    ring
  apply lp.ext
  funext n
  have hn := hcoeff n
  simp only [d, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hn
  have hi := congrArg (fun z : ℂ => Complex.I * z) hn
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hi
  rw [localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
    e he hsource hes (E : ℂ) radialVekuaInput radialVekuaInput_nonpositive
      radialVekuaInput_raw_H1 n]
  simp only [sobolevSmoothing, diagOp_apply]
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (-(n : ℂ) * boundaryFourier (TF (VF (E : ℂ) radialVekuaInput)) n -
        2 * Complex.I * boundaryFourier A n) =
    ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boundaryFourier r n
  linear_combination -((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * hi

include hb hL hhol hinj hC hK e he hsource hes in
/-- The genuine normalized conormal of every scalar full zero mode is
exactly the half-smoothed unitary Fourier transform of its actual L2
radial conormal, including the zero mode and variable circle speed. -/
theorem localConformalRadial_normalizedConormal_eq_coordinateLoad {L : NNReal}
    (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E) (a : ℂ) :
    NCF (E : ℂ) (a • radialVekuaInput) =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
        (boundaryFourier (localConformalRadialCoordinateLoad F hΓLip E a)) := by
  rw [map_smul, radial_normalizedConormal_eq_coordinateLoad_one hR F hFs hb hL hhol hinj
    hC hK e he hsource hes hΓLip hE]
  have hload := localConformalRadialCoordinateLoad_smul (F := F) hΓLip E a
  rw [hload]
  simp only [map_smul]

end PhysicalCoordinates

end PolyaNeumann

end
