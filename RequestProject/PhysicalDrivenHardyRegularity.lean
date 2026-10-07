module

public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.PhysicalDrivenReconstruction
public import RequestProject.FourierLipschitz
public import RequestProject.CutFourier
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Actual zeroth driven gauge with L² forcing

The exceptional zeroth row is differentiated with its true `sqrt 2`
normalization. Finite factorial gauges are integrated by the actual
Banach-valued absolutely-continuous FTC. Their genuine summable tails
then give an integral representation of the zeroth gauge with an L²
derivative. Complex Fourier integration by parts and averaged Parseval
give H¹ coefficients, and hence the half-order coefficients required by
the physical Hardy extension. No regularity of an unknown kernel vector
or approximation within that kernel is assumed.

This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate

local instance physicalDrivenRegularityTwoPiPos : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

/-- The exceptional physical row contains twice the positive-row coupling
and the actual unscaled forcing `-i g`. -/
theorem physicalDrivenScaledRow_hasDerivAt_zero
    (γ : ℝ → ℂ) (E : ℝ) (g : ℝ → ℂ) (y : ℝ → Ell2) {θ : ℝ}
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * g θ) • basisVec 0) θ) :
    HasDerivAt (physicalDrivenScaledRow E y 0)
      (2 * deriv γ θ * physicalDrivenScaledRow E y 1 θ - Complex.I * g θ) θ := by
  have hd := (((innerSL ℂ (basisVec 0)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    θ hy).const_mul (Real.sqrt 2 : ℂ)
  change HasDerivAt (fun s : ℝ => (Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0) (y s))
    ((Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0) (transportCoeff γ E θ (y θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * g θ) • basisVec 0)) θ at hd
  simp only [inner_basisVec] at hd
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hcoup (a b c : ℂ) :
      (Real.sqrt 2 : ℂ) * (a * (b * ((Real.sqrt 2 : ℂ) * c))) = 2 * b * (a * c) := by
    calc
      _ = (Real.sqrt 2 : ℂ) ^ 2 * (b * (a * c)) := by ring
      _ = _ := by rw [hs]; ring
  have hforce : (Real.sqrt 2 : ℂ) * (-(Complex.I / (Real.sqrt 2 : ℂ)) * g θ) =
      -Complex.I * g θ := by
    field_simp [hs0]
  have he : physicalDrivenScaledRow E y 0 =
      fun s : ℝ => (Real.sqrt 2 : ℂ) * (y s : ℕ → ℂ) 0 := by
    funext s
    simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_zero, one_mul, if_true]
  rw [he]
  apply hd.congr_deriv
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, basisVec_coord, if_true, mul_one]
  rw [transportCoeff_apply_coord, shiftN_apply_zero]
  simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_one, physicalDrivenQ,
    Nat.one_ne_zero, if_false, shiftWeight, if_true, mul_zero, add_zero]
  rw [mul_add, hcoup, hforce]
  ring

/-- The exceptional zeroth row has its actual a.e. forced derivative for
merely interval-integrable data. -/
theorem physicalDrivenScaledRow_zero_ae_hasDerivAt_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenScaledRow E (physicalDrivenVector W g) 0)
        (2 * deriv γ θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ -
          Complex.I * g θ) θ := by
  filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg]
    with θ hθ hmem
  exact physicalDrivenScaledRow_hasDerivAt_zero γ E g _ (hθ hmem)

/-- The shifted factorial term occurring only in the exceptional gauge. -/
def physicalDrivenShiftedGaugeTerm (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2)
    (l : ℕ) (θ : ℝ) : ℂ :=
  physicalDrivenPower γ (l + 1) θ * physicalDrivenScaledRow E y l θ

def physicalDrivenShiftedGauge (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (θ : ℝ) : ℂ :=
  ∑' l : ℕ, physicalDrivenShiftedGaugeTerm γ E y l θ

private theorem physicalDrivenShiftedGaugeTerm_mul_nat
    (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (l : ℕ) (θ : ℝ) :
    physicalDrivenShiftedGaugeTerm γ E y l θ * ((l + 1 : ℕ) : ℂ) =
      -physicalDrivenCentered γ θ * physicalDrivenGaugeTerm γ E y 0 l θ := by
  simp only [physicalDrivenShiftedGaugeTerm, physicalDrivenGaugeTerm,
    Nat.add_zero, physicalDrivenPower, Nat.factorial_succ, pow_succ]
  have hn : ((l + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : l + 1 ≠ 0)
  have hf : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  push_cast
  field_simp [hn, hf]

theorem norm_physicalDrivenShiftedGaugeTerm_le
    (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (l : ℕ) (θ : ℝ) :
    ‖physicalDrivenShiftedGaugeTerm γ E y l θ‖ ≤
      ‖physicalDrivenCentered γ θ‖ * ‖physicalDrivenGaugeTerm γ E y 0 l θ‖ := by
  have h := congrArg norm (physicalDrivenShiftedGaugeTerm_mul_nat γ E y l θ)
  simp only [norm_mul, Complex.norm_natCast, norm_neg] at h
  have hn : (1 : ℝ) ≤ (l + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ l + 1)
  have ha := norm_nonneg (physicalDrivenShiftedGaugeTerm γ E y l θ)
  nlinarith

theorem physicalDrivenShiftedGaugeTerm_continuousOn
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y (Icc 0 (2 * Real.pi))) (l : ℕ) :
    ContinuousOn (physicalDrivenShiftedGaugeTerm γ E y l) (Icc 0 (2 * Real.pi)) := by
  have hp : Continuous (physicalDrivenPower γ (l + 1)) := by
    unfold physicalDrivenPower physicalDrivenCentered
    fun_prop
  exact hp.continuousOn.mul
    (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy l))

theorem exists_physicalDrivenShiftedGaugeTerm_majorant
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y (Icc 0 (2 * Real.pi))) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ l θ, θ ∈ Icc 0 (2 * Real.pi) →
      ‖physicalDrivenShiftedGaugeTerm γ E y l θ‖ ≤ u l := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenGaugeTerm_majorant γ hγ E y hy 0
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.sub continuous_const : Continuous (physicalDrivenCentered γ)).continuousOn
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  refine ⟨fun l => R * u l, hu.mul_left R, ?_⟩
  intro l θ hθ
  exact (norm_physicalDrivenShiftedGaugeTerm_le γ E y l θ).trans
    (mul_le_mul (hR θ hθ) (hbd l θ hθ) (norm_nonneg _) hR0)

theorem physicalDrivenShiftedGauge_continuousOn
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y (Icc 0 (2 * Real.pi))) :
    ContinuousOn (physicalDrivenShiftedGauge γ E y) (Icc 0 (2 * Real.pi)) := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenShiftedGaugeTerm_majorant γ hγ E y hy
  have hsum : HasSumUniformlyOn (physicalDrivenShiftedGaugeTerm γ E y)
      (physicalDrivenShiftedGauge γ E y) (Icc 0 (2 * Real.pi)) :=
    HasSumUniformlyOn.of_norm_le_summable hu hbd
  apply hsum.tendstoUniformlyOn.continuousOn
  exact (Eventually.of_forall fun s : Finset ℕ => continuousOn_finset_sum s
    (fun l _ => physicalDrivenShiftedGaugeTerm_continuousOn γ hγ E y hy l)).frequently

theorem physicalDrivenShiftedGauge_weightedIntegral_hasSum_to
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y (Icc 0 (2 * Real.pi))) (w : ℝ → ℂ)
    (hw : ContinuousOn w (Icc 0 (2 * Real.pi))) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    HasSum (fun l : ℕ => ∫ s in (0 : ℝ)..θ,
      w s * physicalDrivenShiftedGaugeTerm γ E y l s)
      (∫ s in (0 : ℝ)..θ, w s * physicalDrivenShiftedGauge γ E y s) := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenShiftedGaugeTerm_majorant γ hγ E y hy
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hsub : uIoc (0 : ℝ) θ ⊆ Icc 0 (2 * Real.pi) := by
    rw [uIoc_of_le hθ.1]
    exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hθ.2)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (bound := fun l _ => C * u l) ?_ ?_ ?_ intervalIntegrable_const ?_
  · intro l
    exact ((hw.mul (physicalDrivenShiftedGaugeTerm_continuousOn γ hγ E y hy l)).mono
      hsub).aestronglyMeasurable measurableSet_uIoc
  · intro l
    exact Eventually.of_forall fun s hs => by
      rw [norm_mul]
      exact mul_le_mul (hC s (hsub hs)) (hbd l s (hsub hs)) (norm_nonneg _) hC0
  · exact Eventually.of_forall fun _ _ => hu.mul_left C
  · refine Eventually.of_forall fun s hs => ?_
    have hsn : Summable (fun l => ‖physicalDrivenShiftedGaugeTerm γ E y l s‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => hbd l s (hsub hs)) hu
    exact hsn.of_norm.hasSum.mul_left (w s)

private theorem driven_c1_absolutelyContinuous {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    AbsolutelyContinuousOnInterval f 0 (2 * Real.pi) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le Real.two_pi_pos.le] using hK

private theorem driven_ac_congr {f h : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 (2 * Real.pi))
    (he : EqOn f h (Icc 0 (2 * Real.pi))) :
    AbsolutelyContinuousOnInterval h 0 (2 * Real.pi) := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  refine hf.congr' ?_
  unfold Filter.EventuallyEq
  rw [eventually_inf_principal]
  exact Eventually.of_forall fun E hE => Finset.sum_congr rfl fun i hi => by
    have hx := (hE.1 i hi).1
    have hy := (hE.1 i hi).2
    rw [uIcc_of_le Real.two_pi_pos.le] at hx hy
    rw [← he hx, ← he hy]

theorem physicalDrivenGaugePartial_zero_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (N : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 N) 0 (2 * Real.pi) := by
  have ht (l : ℕ) : AbsolutelyContinuousOnInterval
      (physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) 0 l) 0 (2 * Real.pi) := by
    have hp : ContDiff ℝ 1 (physicalDrivenPower γ l) := by
      unfold physicalDrivenPower physicalDrivenCentered
      exact ((hγ.sub contDiff_const).neg.pow l).div_const _
    have h_simpa := (driven_c1_absolutelyContinuous hp).smul
      (physicalDrivenScaledRow_absolutelyContinuous_of_intervalIntegrable hK hW g hg l)
    simp only [physicalDrivenGaugeTerm, Nat.add_zero, Pi.smul_apply, smul_eq_mul] at h_simpa ⊢
    exact h_simpa
  induction N with
  | zero =>
      have he : physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 0 =
          physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) 0 0 := by
        funext s
        exact Finset.sum_range_one _
      rw [he]
      exact ht 0
  | succ N ih =>
      have he : physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 (N + 1) =
          fun s => physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 N s +
            physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) 0 (N + 1) s := by
        funext s
        exact Finset.sum_range_succ _ _
      rw [he]
      exact ih.add (ht (N + 1))

/-- Finite exceptional-gauge cancellation, retaining its true tail and
the forcing at frequency zero. -/
theorem physicalDrivenGaugePartial_zero_hasDerivAt
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (E : ℝ) (g : ℝ → ℂ) (y : ℝ → Ell2)
    {θ : ℝ} (hy : HasDerivAt y (transportCoeff γ E θ (y θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * g θ) • basisVec 0) θ) (N : ℕ) :
    HasDerivAt (physicalDrivenGaugePartial γ E y 0 N)
      (deriv γ θ * physicalDrivenScaledRow E y 1 θ - Complex.I * g θ +
        deriv γ θ * physicalDrivenGaugeTerm γ E y 1 N θ +
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l θ) θ := by
  induction N with
  | zero =>
      have he : physicalDrivenGaugePartial γ E y 0 0 = physicalDrivenScaledRow E y 0 := by
        funext s
        simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower]
      rw [he]
      apply (physicalDrivenScaledRow_hasDerivAt_zero γ E g y hy).congr_deriv
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero,
        physicalDrivenGaugeTerm, physicalDrivenPower, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, one_mul, Nat.zero_add]
      ring
  | succ N ih =>
      have hp := physicalDrivenPower_hasDerivAt_succ hγ N θ
      have hd := physicalDrivenScaledRow_hasDerivAt_succ γ E g y hy N
      have he : physicalDrivenGaugePartial γ E y 0 (N + 1) =
          fun s => physicalDrivenGaugePartial γ E y 0 N s +
            physicalDrivenGaugeTerm γ E y 0 (N + 1) s := by
        funext s
        exact Finset.sum_range_succ _ _
      have hf : (fun s => physicalDrivenGaugePartial γ E y 0 N s +
          physicalDrivenGaugeTerm γ E y 0 (N + 1) s) =
          physicalDrivenGaugePartial γ E y 0 N +
            physicalDrivenPower γ (N + 1) * physicalDrivenScaledRow E y (N + 1) := by
        funext s
        simp only [physicalDrivenGaugeTerm, Nat.add_zero, Pi.add_apply, Pi.mul_apply]
      rw [he, hf]
      apply (ih.add (hp.mul hd)).congr_deriv
      rw [Finset.sum_range_succ]
      simp only [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm]
      ring

/-- The continuous part of the actual derivative of gauge zero. -/
def physicalDrivenGaugeZeroContinuousPart (γ : ℝ → ℂ) (E : ℝ)
    (y : ℝ → Ell2) (θ : ℝ) : ℂ :=
  deriv γ θ * physicalDrivenScaledRow E y 1 θ +
    physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenShiftedGauge γ E y θ

theorem physicalDrivenGaugeZeroContinuousPart_continuousOn
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y (Icc 0 (2 * Real.pi))) :
    ContinuousOn (physicalDrivenGaugeZeroContinuousPart γ E y) (Icc 0 (2 * Real.pi)) := by
  exact (hγ.continuous_deriv_one.continuousOn.mul
    (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy 1))).add
      ((continuousOn_const.mul
        (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn).mul
        (physicalDrivenShiftedGauge_continuousOn γ hγ.continuous E y hy))

private theorem driven_continuousOn_memLp_two {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 (2 * Real.pi))) :
    MemLp f 2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    C ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
    hC x (Ioc_subset_Icc_self hx)

private theorem physicalDrivenGaugePartial_zero_primitive
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 N θ =
      (∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 s - Complex.I * g s) +
      (∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) 1 N s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ,
        conj (deriv γ s) *
          ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E (physicalDrivenVector W g) l s) := by
  classical
  let y := physicalDrivenVector W g
  let a : ℝ → ℂ := fun s => deriv γ s * physicalDrivenScaledRow E y 1 s - Complex.I * g s
  let t : ℝ → ℂ := fun s => deriv γ s * physicalDrivenGaugeTerm γ E y 1 N s
  let b : ℝ → ℂ := fun s => conj (deriv γ s) *
    ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l s
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hc : ContinuousOn (fun s => deriv γ s * physicalDrivenScaledRow E y 1 s)
      (Icc 0 (2 * Real.pi)) := hγ.continuous_deriv_one.continuousOn.mul
        (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy 1))
  have hgi : IntegrableOn g (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
  have ha : IntegrableOn a (Icc 0 (2 * Real.pi)) :=
    hc.integrableOn_Icc.sub (hgi.const_mul Complex.I)
  have ht : ContinuousOn t (Icc 0 (2 * Real.pi)) := hγ.continuous_deriv_one.continuousOn.mul
    (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E y hy 1 N)
  have hb : ContinuousOn b (Icc 0 (2 * Real.pi)) :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (continuousOn_finset_sum _ fun l _ =>
        physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E y hy l)
  have hd : ∀ᵐ s, s ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenGaugePartial γ E y 0 N)
        (a s + t s + physicalDrivenQ E ^ 2 * b s) s := by
    filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg]
      with s hs hmem
    simpa only [a, t, b, mul_assoc] using
      physicalDrivenGaugePartial_zero_hasDerivAt hγ E g y (hs hmem) N
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (physicalDrivenGaugePartial_zero_absolutelyContinuous_of_intervalIntegrable hK hγ hW g hg N)
    ((ha.add ht.integrableOn_Icc).add (hb.integrableOn_Icc.const_mul (physicalDrivenQ E ^ 2))) hd θ hθ
  have hp0 := physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y 0 N
    (physicalDrivenVector_zero W g)
  rw [hp0, zero_add] at he
  have hsub : uIcc 0 θ ⊆ Icc 0 (2 * Real.pi) := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have hia : IntervalIntegrable a volume 0 θ := (ha.mono_set hsub).intervalIntegrable
  have hit : IntervalIntegrable t volume 0 θ := (ht.mono hsub).intervalIntegrable
  have hib : IntervalIntegrable b volume 0 θ := (hb.mono hsub).intervalIntegrable
  simp only [Pi.add_apply] at he
  rw [intervalIntegral.integral_add (hia.add hit) (hib.const_mul _),
    intervalIntegral.integral_add hia hit, intervalIntegral.integral_const_mul] at he
  exact he

/-- Actual integral representation of gauge zero. The continuous term is
constructed from the genuine rows; the forcing remains `-i g`. -/
theorem physicalDrivenGauge_zero_primitive_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) 0 θ =
      ∫ s in (0 : ℝ)..θ,
        physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) s - Complex.I * g s := by
  classical
  let y := physicalDrivenVector W g
  let a : ℝ → ℂ := fun s => deriv γ s * physicalDrivenScaledRow E y 1 s - Complex.I * g s
  let b : ℝ → ℂ := fun s => conj (deriv γ s) * physicalDrivenShiftedGauge γ E y s
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hp : Tendsto (fun N : ℕ => physicalDrivenGaugePartial γ E y 0 N θ) atTop
      (𝓝 (physicalDrivenGauge γ E y 0 θ)) := by
    have h_simpa := ((summable_norm_physicalDrivenGaugeTerm γ E y 0 θ).of_norm.hasSum.tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 1)
    simp only [physicalDrivenGaugePartial, Function.comp_apply, Function.comp_def] at h_simpa ⊢
    exact h_simpa
  have ht := (physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ.continuous E y hy 1
    (deriv γ) hγ.continuous_deriv_one.continuousOn hθ).summable.tendsto_atTop_zero
  have hs := physicalDrivenShiftedGauge_weightedIntegral_hasSum_to γ hγ.continuous E y hy
    (fun s => conj (deriv γ s))
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn hθ
  have hsub : uIcc 0 θ ⊆ Icc 0 (2 * Real.pi) := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have he (N : ℕ) : (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l s) =
      ∑ l ∈ Finset.range N, ∫ s in (0 : ℝ)..θ,
        conj (deriv γ s) * physicalDrivenShiftedGaugeTerm γ E y l s := by
    simp_rw [Finset.mul_sum]
    apply intervalIntegral.integral_finset_sum
    intro l _
    exact (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E y hy l)).mono
        hsub).intervalIntegrable
  have hb : Tendsto (fun N : ℕ => ∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l s) atTop
      (𝓝 (∫ s in (0 : ℝ)..θ, b s)) :=
    hs.tendsto_sum_nat.congr' (Eventually.of_forall fun N => (he N).symm)
  have hr : Tendsto (fun N : ℕ => (∫ s in (0 : ℝ)..θ, a s) +
      (∫ s in (0 : ℝ)..θ, deriv γ s * physicalDrivenGaugeTerm γ E y 1 N s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l s)) atTop
      (𝓝 ((∫ s in (0 : ℝ)..θ, a s) + physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, b s))) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds (x := ∫ s in (0 : ℝ)..θ, a s)).add ht).add
        (hb.const_mul (physicalDrivenQ E ^ 2))
  have hlim : physicalDrivenGauge γ E y 0 θ =
      (∫ s in (0 : ℝ)..θ, a s) + physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, b s) :=
    tendsto_nhds_unique hp (hr.congr' (Eventually.of_forall fun N =>
      (physicalDrivenGaugePartial_zero_primitive hK hγ hW g hg N hθ).symm))
  have ha : IntervalIntegrable a volume 0 θ := by
    have hc : ContinuousOn (fun s => deriv γ s * physicalDrivenScaledRow E y 1 s)
        (Icc 0 (2 * Real.pi)) := hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy 1))
    have hgt : IntervalIntegrable g volume 0 θ := hg.mono_set (by
      simpa only [uIcc_of_le Real.two_pi_pos.le] using hsub)
    exact ((hc.mono hsub).intervalIntegrable).sub (hgt.const_mul Complex.I)
  have hbi : IntervalIntegrable b volume 0 θ :=
    (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGauge_continuousOn γ hγ.continuous E y hy)).mono
        hsub).intervalIntegrable
  rw [hlim, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ha (hbi.const_mul _)]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [a, b, physicalDrivenGaugeZeroContinuousPart]
  ring

theorem physicalDrivenGauge_zero_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) 0 (2 * Real.pi) := by
  have hc := physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg)
  have hi : IntervalIntegrable
      (fun s => physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) s -
        Complex.I * g s) volume 0 (2 * Real.pi) := by
    have hcc : ContinuousOn (physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g))
        (uIcc 0 (2 * Real.pi)) := by simpa only [uIcc_of_le Real.two_pi_pos.le] using hc
    exact hcc.intervalIntegrable.sub (hg.const_mul Complex.I)
  apply driven_ac_congr (absolutelyContinuousOnInterval_intervalIntegral_banach hi
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩))
  intro θ hθ
  exact (physicalDrivenGauge_zero_primitive_of_intervalIntegrable hK hγ hW g hg hθ).symm

theorem physicalDrivenGauge_zero_ae_hasDerivAt_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenGauge γ E (physicalDrivenVector W g) 0)
        (physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) θ -
          Complex.I * g θ) θ := by
  have hc := physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg)
  have hi : IntervalIntegrable
      (fun s => physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) s -
        Complex.I * g s) volume 0 (2 * Real.pi) := by
    have hcc : ContinuousOn (physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g))
        (uIcc 0 (2 * Real.pi)) := by simpa only [uIcc_of_le Real.two_pi_pos.le] using hc
    exact hcc.intervalIntegrable.sub (hg.const_mul Complex.I)
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hi]
    with θ hθ hmem
  refine (hθ hmem).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with s hs
  exact physicalDrivenGauge_zero_primitive_of_intervalIntegrable hK hγ hW g hg
    (Ioo_subset_Icc_self hs)

/-- The derivative of the actual zeroth gauge is L² for actual L² forcing. -/
theorem physicalDrivenGauge_zero_derivative_memLp
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    MemLp (fun θ => physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) θ -
      Complex.I * g θ) 2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  have hc := physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g
      (intervalIntegrable_boundary_of_memLp g hg))
  exact (driven_continuousOn_memLp_two hc).sub (by
    exact hg.const_smul Complex.I)

/-- Genuine complex Fourier integration by parts for an absolutely
continuous function and its actual a.e. derivative. This includes mode
zero and uses the averaged Fourier normalization. -/
theorem fourierCoeffOn_of_ac_ae_hasDerivAt
    {f f' : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 (2 * Real.pi))
    (hf' : MemLp f' 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt f (f' θ) θ)
    (hp : f 0 = f (2 * Real.pi)) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos f' n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos f n := by
  let e : ℝ → ℂ := fun θ => fourier (-n) (θ : AddCircle (2 * Real.pi))
  let α : ℂ := -(Complex.I * (n : ℂ))
  have hec : Continuous e := (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  have hen (θ : ℝ) : ‖e θ‖ = 1 := norm_fourier_coe (-n) θ
  have he1 : ContDiff ℝ 1 e := by
    dsimp only [e]
    simp_rw [fourier_coe_two_pi]
    have harg : ContDiff ℝ 1 (fun θ : ℝ => ((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const
    exact harg.cexp
  have heD (θ : ℝ) : HasDerivAt e (α * e θ) θ := by
    have hα : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) /
        ((2 * Real.pi : ℝ) : ℂ) = α := by
      dsimp only [α]
      push_cast
      field_simp [Real.pi_ne_zero]
    simpa only [hα] using hasDerivAt_fourier_neg (2 * Real.pi) n θ
  have hfC : ContinuousOn f (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf.continuousOn
  have hfi : IntegrableOn f (Icc 0 (2 * Real.pi)) := hfC.integrableOn_Icc
  have hf'i : IntegrableOn f' (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hf'
  have hfe : IntegrableOn (fun θ => f θ * e θ) (Icc 0 (2 * Real.pi)) :=
    hfi.mul_bdd hec.aestronglyMeasurable.restrict
      (Eventually.of_forall fun θ => (hen θ).le)
  have hf'e : IntegrableOn (fun θ => f' θ * e θ) (Icc 0 (2 * Real.pi)) :=
    hf'i.mul_bdd hec.aestronglyMeasurable.restrict
      (Eventually.of_forall fun θ => (hen θ).le)
  have hprodAC : AbsolutelyContinuousOnInterval (fun θ => f θ * e θ) 0 (2 * Real.pi) := by
    exact hf.smul (driven_c1_absolutelyContinuous he1)
  have hprodD : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (fun θ => f θ * e θ) (f' θ * e θ + α * (f θ * e θ)) θ := by
    filter_upwards [hd] with θ hθ hmem
    convert (hθ hmem).mul (heD θ) using 1; ring
  have hprodI : IntegrableOn (fun θ => f' θ * e θ + α * (f θ * e θ))
      (Icc 0 (2 * Real.pi)) := hf'e.add (hfe.const_mul α)
  have hFTC := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    hprodAC hprodI hprodD (2 * Real.pi) ⟨Real.two_pi_pos.le, le_rfl⟩
  have he0 : e 0 = 1 := by
    change fourier (-n) ((0 : ℝ) : AddCircle (2 * Real.pi)) = 1
    rw [AddCircle.coe_zero, fourier_eval_zero]
  have heL : e (2 * Real.pi) = 1 := by
    have hper : ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      have h0 := AddCircle.coe_add_period (2 * Real.pi) (0 : ℝ)
      rw [zero_add, AddCircle.coe_zero] at h0
      exact h0
    change fourier (-n) ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = 1
    rw [hper, fourier_eval_zero]
  have hi0 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      f' θ * e θ + α * (f θ * e θ)) = 0 := by
    rw [he0, heL, mul_one, mul_one, ← hp] at hFTC
    exact add_left_cancel (show f 0 + (∫ θ in (0 : ℝ)..(2 * Real.pi),
      f' θ * e θ + α * (f θ * e θ)) = f 0 + 0 from by
        simpa only [add_zero] using hFTC.symm)
  have hife : IntervalIntegrable (fun θ => f θ * e θ) volume 0 (2 * Real.pi) := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hfe
  have hif'e : IntervalIntegrable (fun θ => f' θ * e θ) volume 0 (2 * Real.pi) := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf'e
  rw [intervalIntegral.integral_add hif'e (hife.const_mul α),
    intervalIntegral.integral_const_mul] at hi0
  have hi : (∫ θ in (0 : ℝ)..(2 * Real.pi), f' θ * e θ) =
      (Complex.I * (n : ℂ)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * e θ) := by
    dsimp only [α] at hi0
    exact eq_of_sub_eq_zero (by simpa only [neg_mul, ← sub_eq_add_neg] using hi0)
  have hi' : (∫ θ in (0 : ℝ)..(2 * Real.pi), e θ * f' θ) =
      (Complex.I * (n : ℂ)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), e θ * f θ) := by
    simpa only [mul_comm] using hi
  simp only [e, fourier_coe_apply] at hi'
  simp only [fourierCoeffOn_eq_integral, smul_eq_mul, Complex.real_smul,
    fourier_coe_apply, sub_zero]
  rw [hi']
  ring

/-- Actual AC and an L² a.e. derivative give the project's true Fourier
H¹ sequence, using Parseval for both value and derivative. -/
theorem isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    {f f' : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 (2 * Real.pi))
    (hf' : MemLp f' 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt f (f' θ) θ)
    (hp : f 0 = f (2 * Real.pi)) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos f) := by
  have hfC : ContinuousOn f (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf.continuousOn
  have hs := (hasSum_sq_fourierCoeffOn Real.two_pi_pos
    (driven_continuousOn_memLp_two hfC)).summable
  have hs' := (hasSum_sq_fourierCoeffOn Real.two_pi_pos hf').summable
  have hdn (n : ℤ) : ‖fourierCoeffOn Real.two_pi_pos f' n‖ ^ 2 =
      (n : ℝ) ^ 2 * ‖fourierCoeffOn Real.two_pi_pos f n‖ ^ 2 := by
    rw [fourierCoeffOn_of_ac_ae_hasDerivAt hf hf' hd hp n]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast,
      mul_pow, sq_abs]
  change Summable (fun n : ℤ => (sobWeight n ^ (1 : ℝ) *
    ‖fourierCoeffOn Real.two_pi_pos f n‖) ^ 2)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((hs.mul_left 2).add (hs'.mul_left 2))
  rw [hdn]
  simp only [sobWeight, Real.rpow_one]
  have h0 := norm_nonneg (fourierCoeffOn Real.two_pi_pos f n)
  have ha := abs_nonneg (n : ℝ)
  have hsq := sq_nonneg ((|(n : ℝ)| - 1) * ‖fourierCoeffOn Real.two_pi_pos f n‖)
  rw [← sq_abs (n : ℝ)]
  nlinarith

/-- The actual zeroth gauge of an L² driven observation-kernel vector has
H¹ coefficients. No Sobolev premise on that vector is needed. -/
theorem physicalDrivenPeriodicGauge_zero_isSobolevSeq_one
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0)) := by
  have hgi := intervalIntegrable_boundary_of_memLp g hg
  have hends := physicalDrivenGauge_actual_endpoints γ E W g hO 0
  have hreg := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalDrivenGauge_zero_absolutelyContinuous_of_intervalIntegrable hK hγ hW g hgi)
    (physicalDrivenGauge_zero_derivative_memLp hγ hW g hg)
    (physicalDrivenGauge_zero_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hgi)
    (hends.1.trans hends.2.symm)
  have hc (n : ℤ) : fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) n =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) n := by
    simp only [fourierCoeffOn_eq_integral, sub_zero]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    dsimp only
    rw [physicalDrivenPeriodicGauge_eqOn γ E W g hO 0 hθ]
  exact hreg.congr fun n => by rw [hc n]

theorem physicalDrivenPeriodicGauge_zero_isSobolevSeq_half
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) :
    IsSobolevSeq (1 / 2 : ℝ)
      (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0)) :=
  (sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hK hγ hW g hg hO)).1

theorem physicalDrivenPeriodicGauge_zero_isSobolevSeq_one_boundaryL2
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) (hO : observationAdj W g = 0) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0)) :=
  physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hK hγ hW g (Lp.memLp g) hO

theorem physicalDrivenPeriodicGauge_zero_isSobolevSeq_half_boundaryL2
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) (hO : observationAdj W g = 0) :
    IsSobolevSeq (1 / 2 : ℝ)
      (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0)) :=
  physicalDrivenPeriodicGauge_zero_isSobolevSeq_half hK hγ hW g (Lp.memLp g) hO

end PolyaNeumann

end
