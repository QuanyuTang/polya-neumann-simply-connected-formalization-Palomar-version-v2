module

public import RequestProject.RoughVekuaTransport
public import RequestProject.PhysicalDrivenReconstruction

/-
The factorial gauge of the genuine rough driven vector.  Only its zeroth
row contains the L2 primitive.  The entire regular correction is retained,
and the positive-row AC equations give the actual moment recurrence.
This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate

local instance roughGaugeTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

private theorem roughGauge_c1_ac {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    AbsolutelyContinuousOnInterval f 0 (2 * Real.pi) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le Real.two_pi_pos.le] using hK

private theorem roughGauge_continuous_memLp {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 (2 * Real.pi))) : MemLp f 2 μB := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    C ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ =>
    hC θ (Ioc_subset_Icc_self hθ)

private theorem roughGauge_continuous_mul_memLp {a f : ℝ → ℂ}
    (ha : Continuous a) (hf : MemLp f 2 μB) : MemLp (fun θ => a θ * f θ) 2 μB := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  apply hf.of_le_mul (c := C) (ha.aestronglyMeasurable.restrict.mul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change ‖a θ * f θ‖ ≤ C * ‖f θ‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC θ (Ioc_subset_Icc_self hθ)) (norm_nonneg _)

private theorem roughGauge_continuousOn_mul_memLp {a f : ℝ → ℂ}
    (ha : ContinuousOn a (Icc 0 (2 * Real.pi))) (hf : MemLp f 2 μB) :
    MemLp (fun θ => a θ * f θ) 2 μB := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  apply hf.of_le_mul (c := C)
    (((ha.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).mul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change ‖a θ * f θ‖ ≤ C * ‖f θ‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC θ (Ioc_subset_Icc_self hθ)) (norm_nonneg _)

private theorem roughGauge_ac_congr {f g : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 (2 * Real.pi))
    (he : EqOn f g (Icc 0 (2 * Real.pi))) :
    AbsolutelyContinuousOnInterval g 0 (2 * Real.pi) := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  refine hf.congr' ?_
  unfold Filter.EventuallyEq
  rw [eventually_inf_principal]
  exact Eventually.of_forall fun B hB => Finset.sum_congr rfl fun i hi => by
    have hx := (hB.1 i hi).1
    have hy := (hB.1 i hi).2
    rw [uIcc_of_le Real.two_pi_pos.le] at hx hy
    rw [← he hx, ← he hy]

section GenuineGauge

variable {γ : ℝ → ℂ} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

theorem roughVekuaGauge_scaledRow_zero_split (p : BoundaryL2) (m α : ℂ) (θ : ℝ) :
    physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) 0 θ =
      -Complex.I * p θ +
        physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0 θ := by
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [physicalDrivenScaledRow, pow_zero, one_mul, physicalDrivenRow, if_true,
    roughVekuaDrivenVector, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, basisVec_coord, mul_one]
  field_simp [hs0] <;> ring

theorem roughVekuaGauge_scaledRow_succ_eq (p : BoundaryL2) (m α : ℂ) (n : ℕ) (θ : ℝ) :
    physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 1) θ =
      physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 1) θ := by
  simp only [physicalDrivenScaledRow, physicalDrivenRow, Nat.succ_ne_zero, if_false,
    roughVekuaDrivenVector_positive_coord]

theorem roughVekuaGauge_partial_succ_eq (p : BoundaryL2) (m α : ℂ) (j N : ℕ) (θ : ℝ) :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N θ =
      physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) (j + 1) N θ := by
  apply Finset.sum_congr rfl
  intro l _
  simp only [physicalDrivenGaugeTerm, ← Nat.add_assoc, roughVekuaGauge_scaledRow_succ_eq]

theorem roughVekuaGauge_succ_eq (p : BoundaryL2) (m α : ℂ) (j : ℕ) (θ : ℝ) :
    physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) θ =
      physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) (j + 1) θ := by
  apply tsum_congr
  intro l
  simp only [physicalDrivenGaugeTerm, ← Nat.add_assoc, roughVekuaGauge_scaledRow_succ_eq]

/-- The full zeroth gauge includes the actual rough primitive, with its
original scalar and its entire regular correction. -/
theorem roughVekuaGauge_zero_split (p : BoundaryL2) (m α : ℂ) (θ : ℝ) :
    physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) 0 θ =
      -Complex.I * p θ + physicalDrivenGauge γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 θ := by
  have hs := (summable_norm_physicalDrivenGaugeTerm γ E
    (roughVekuaDrivenVector γ E W p m α) 0 θ).of_norm
  have ht := (summable_norm_physicalDrivenGaugeTerm γ E
    (roughVekuaRegularCorrection γ E W p m α) 0 θ).of_norm
  rw [physicalDrivenGauge, hs.tsum_eq_zero_add, physicalDrivenGauge, ht.tsum_eq_zero_add]
  have he : (fun l : ℕ => physicalDrivenGaugeTerm γ E
      (roughVekuaDrivenVector γ E W p m α) 0 (l + 1) θ) =
      fun l => physicalDrivenGaugeTerm γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 (l + 1) θ := by
    funext l
    simp only [physicalDrivenGaugeTerm, Nat.add_zero, roughVekuaGauge_scaledRow_succ_eq]
  rw [he]
  simp only [physicalDrivenGaugeTerm, physicalDrivenPower, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, Nat.zero_add, roughVekuaGauge_scaledRow_zero_split]
  ring

theorem roughVekuaGauge_partial_zero_split (p : BoundaryL2) (m α : ℂ) (N : ℕ) (θ : ℝ) :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) 0 N θ =
      -Complex.I * p θ + physicalDrivenGaugePartial γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 N θ := by
  induction N with
  | zero =>
    simpa [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower] using
      roughVekuaGauge_scaledRow_zero_split p m α θ
  | succ N ih =>
    simp only [physicalDrivenGaugePartial, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp only [physicalDrivenGaugeTerm, Nat.add_zero, roughVekuaGauge_scaledRow_succ_eq]
    ring

variable {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    (hW : IsTransport γ E W)

include hK hγ hW in
theorem roughVekuaGauge_regular_memLp (p : BoundaryL2) (m α : ℂ) (j : ℕ) :
    MemLp (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) j) 2 μB := by
  exact roughGauge_continuous_memLp (physicalDrivenGauge_continuousOn γ hγ.continuous E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) j)

include hK hγ hW in
theorem roughVekuaGauge_zero_memLp (p : BoundaryL2) (m α : ℂ) :
    MemLp (physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) 0) 2 μB := by
  have h := ((Lp.memLp p).const_smul (-Complex.I)).add
    (roughVekuaGauge_regular_memLp hK hγ hW p m α 0)
  exact MemLp.ae_eq (Eventually.of_forall fun θ => by
    change (-Complex.I) * (p θ) +
      physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0 θ = _
    rw [roughVekuaGauge_zero_split]) h

include hK hγ hW in
private theorem roughGauge_regular_row_ac (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) n)
      0 (2 * Real.pi) := by
  have hc := absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec n))
    (roughVekuaRegularCorrection_absolutelyContinuous hK hγ hW p m α)
  by_cases hn : n = 0
  · subst n
    convert hc.const_smul (Real.sqrt 2 : ℂ) using 1 <;>
      ext θ <;>
      simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_zero, one_mul,
        if_true, innerSL_apply_apply, inner_basisVec, smul_eq_mul]
  · convert hc.const_smul (physicalDrivenQ E ^ n) using 1 <;>
      ext θ <;>
      simp only [physicalDrivenScaledRow, physicalDrivenRow, hn, if_false,
        innerSL_apply_apply, inner_basisVec, smul_eq_mul]

include hK hγ hW in
private theorem roughGauge_regular_partial_ac (p : BoundaryL2) (m α : ℂ) (j N : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j N)
      0 (2 * Real.pi) := by
  have ht (l : ℕ) : AbsolutelyContinuousOnInterval
      (physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j l)
      0 (2 * Real.pi) := by
    have hp : ContDiff ℝ 1 (physicalDrivenPower γ l) := by
      unfold physicalDrivenPower physicalDrivenCentered
      exact ((hγ.sub contDiff_const).neg.pow l).div_const _
    unfold physicalDrivenGaugeTerm
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using
      (roughGauge_c1_ac hp).smul (roughGauge_regular_row_ac hK hγ hW p m α (l + j))
  induction N with
  | zero =>
    have he : physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j 0 =
        physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j 0 := by
      funext θ
      exact Finset.sum_range_one _
    rw [he]
    exact ht 0
  | succ N ih =>
    have he : physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α)
        j (N + 1) = fun θ =>
          physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j N θ +
            physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j (N + 1) θ := by
      funext θ
      exact Finset.sum_range_succ _ _
    rw [he]
    exact ih.add (ht (N + 1))

include hK hγ hW in
private theorem roughGauge_partial_succ_ac (p : BoundaryL2) (m α : ℂ) (j N : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N)
      0 (2 * Real.pi) := by
  have he : physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N =
      physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) (j + 1) N :=
    funext (roughVekuaGauge_partial_succ_eq p m α j N)
  rw [he]
  exact roughGauge_regular_partial_ac hK hγ hW p m α (j + 1) N

include hK hγ hW in
theorem roughVekuaGauge_partial_succ_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) (j N : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt
        (physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N)
        (physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) j N θ +
          deriv γ θ * physicalDrivenPower γ N θ * physicalDrivenScaledRow E
            (roughVekuaDrivenVector γ E W p m α) (N + j + 2) θ) θ := by
  induction N with
  | zero =>
    filter_upwards [roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α j]
      with θ hθ hmem
    convert hθ hmem using 1
    · funext s
      simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower,
        physicalDrivenScaledRow, physicalDrivenRow, Finset.sum_range_succ,
        Finset.range_zero, Nat.add_assoc, add_comm]
    · simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower,
        physicalDrivenScaledRow, physicalDrivenRow]
      ring
  | succ N ih =>
    filter_upwards [ih, roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α
      (N + j + 1)] with θ hθ hd hmem
    have hp := physicalDrivenPower_hasDerivAt_succ hγ N θ
    have he (k : ℕ) : physicalDrivenGaugePartial γ E
        (roughVekuaDrivenVector γ E W p m α) k (N + 1) = fun s =>
          physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) k N s +
            physicalDrivenGaugeTerm γ E (roughVekuaDrivenVector γ E W p m α) k (N + 1) s := by
      funext s
      exact Finset.sum_range_succ _ _
    rw [he]
    convert (hθ hmem).add (hp.mul (hd hmem)) using 1
    · funext s
      simp only [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Pi.add_apply, Pi.mul_apply]
    · rw [he]
      simp only [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      ring

include hK hγ hW in
private theorem roughGauge_partial_memLp (p : BoundaryL2) (m α : ℂ) (j N : ℕ) :
    MemLp (physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) j N) 2 μB := by
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have hc := physicalDrivenGaugePartial_continuousOn γ hγ.continuous E _ hv j N
  cases j with
  | zero =>
    exact MemLp.ae_eq (Eventually.of_forall fun θ => by
      change (-Complex.I) * (p θ) +
        physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 N θ = _
      rw [roughVekuaGauge_partial_zero_split])
      (((Lp.memLp p).const_smul (-Complex.I)).add (roughGauge_continuous_memLp hc))
  | succ j =>
    exact MemLp.ae_eq (Eventually.of_forall fun θ => by
      rw [roughVekuaGauge_partial_succ_eq]) (roughGauge_continuous_memLp hc)

include hW in
private theorem roughGauge_partial_succ_zero (p : BoundaryL2) (m α : ℂ) (j N : ℕ) :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N 0 = 0 := by
  apply Finset.sum_eq_zero
  intro l _
  rw [physicalDrivenGaugeTerm, show l + (j + 1) = (l + j) + 1 by omega,
    physicalDrivenScaledRow, roughVekuaDrivenRow_succ_zero hW]
  simp

private theorem roughGauge_partial_succ_endpoint (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0)
    (j N : ℕ) :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N
      (2 * Real.pi) = 0 := by
  apply Finset.sum_eq_zero
  intro l _
  rw [physicalDrivenGaugeTerm, show l + (j + 1) = (l + j) + 1 by omega,
    physicalDrivenScaledRow, roughVekuaDrivenRow_succ_endpoint p m α hα]
  simp

include hK hγ hW in
/-- Actual AC integration by parts for the positive finite gauge. The
zeroth gauge is used only as an L2 integrand, and the finite tail remains. -/
theorem roughVekuaGauge_momentPartial_recurrence (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0)
    (j N k : ℕ) :
    physicalDrivenQ E ^ 2 * physicalDrivenMomentPartial γ E
      (roughVekuaDrivenVector γ E W p m α) j N k +
      (k : ℂ) * physicalDrivenMomentPartial γ E
        (roughVekuaDrivenVector γ E W p m α) (j + 1) N (k - 1) =
      -physicalDrivenTailMoment γ E (roughVekuaDrivenVector γ E W p m α) j N k := by
  let f := roughVekuaDrivenVector γ E W p m α
  let z : ℝ → ℂ := fun θ => conj (physicalDrivenCentered γ θ)
  let s := physicalDrivenGaugePartial γ E f (j + 1) N
  let a : ℝ → ℂ := fun θ => conj (deriv γ θ) * physicalDrivenGaugePartial γ E f j N θ * z θ ^ k
  let b : ℝ → ℂ := fun θ => conj (deriv γ θ) * s θ * z θ ^ (k - 1)
  let t : ℝ → ℂ := fun θ => deriv γ θ * physicalDrivenPower γ N θ *
    physicalDrivenScaledRow E f (N + j + 2) θ * z θ ^ k
  let r : ℝ → ℂ := fun θ => physicalDrivenQ E ^ 2 * a θ + (k : ℂ) * b θ + t θ
  have hz1 : ContDiff ℝ 1 z :=
    Complex.conjCLE.contDiff.comp (hγ.sub contDiff_const)
  have hsz := (roughGauge_partial_succ_ac hK hγ hW p m α j N).smul
    (roughGauge_c1_ac (hz1.pow k))
  have hsz' : AbsolutelyContinuousOnInterval (fun θ => s θ * z θ ^ k) 0 (2 * Real.pi) := by
    simpa only [s, f, Pi.smul_apply, smul_eq_mul, Pi.mul_def] using hsz
  have ha : MemLp a 2 μB := by
    have hw : Continuous (fun θ => conj (deriv γ θ) * z θ ^ k) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz1.continuous.pow k)
    simpa only [a, f, mul_assoc, mul_left_comm, mul_comm] using
      roughGauge_continuous_mul_memLp hw (roughGauge_partial_memLp hK hγ hW p m α j N)
  have hb : MemLp b 2 μB := by
    have hw : Continuous (fun θ => conj (deriv γ θ) * z θ ^ (k - 1)) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz1.continuous.pow (k - 1))
    simpa only [b, s, f, mul_assoc, mul_left_comm, mul_comm] using
      roughGauge_continuous_mul_memLp hw (roughGauge_partial_memLp hK hγ hW p m α (j + 1) N)
  have ht : MemLp t 2 μB := by
    have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
    have hc : ContinuousOn t (Icc 0 (2 * Real.pi)) := by
      have hp : Continuous (physicalDrivenPower γ N) := by
        unfold physicalDrivenPower physicalDrivenCentered
        exact ((hγ.continuous.sub continuous_const).neg.pow N).div_const _
      have hd : ContinuousOn
          (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (N + j + 2))
          (Icc 0 (2 * Real.pi)) := continuousOn_const.mul
        (physicalDrivenRow_continuousOn _ hv (N + j + 2))
      have he : (fun θ => physicalDrivenScaledRow E f (N + j + 2) θ) =
          physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (N + j + 2) := by
        funext θ
        exact roughVekuaGauge_scaledRow_succ_eq p m α (N + j + 1) θ
      dsimp only [t]
      have hcont := ((hγ.continuous_deriv_one.mul hp).continuousOn.mul hd).mul
        (hz1.continuous.pow k).continuousOn
      convert hcont using 1
      ext θ
      dsimp only [f]
      exact congrArg (fun q => deriv γ θ * physicalDrivenPower γ N θ * q * z θ ^ k)
        (roughVekuaGauge_scaledRow_succ_eq p m α (N + j + 1) θ)
    exact roughGauge_continuous_memLp hc
  have hr : MemLp r 2 μB := by
    simpa only [r, smul_eq_mul, Pi.add_def, Pi.smul_def] using
      ((ha.const_smul (physicalDrivenQ E ^ 2)).add (hb.const_smul (k : ℂ))).add ht
  have hd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (fun θ => s θ * z θ ^ k) (r θ) θ := by
    filter_upwards [roughVekuaGauge_partial_succ_ae_hasDerivAt hK hγ hW p m α j N]
      with θ hθ hmem
    have hdz : HasDerivAt z (conj (deriv γ θ)) θ := by
      simpa only [z, physicalDrivenCentered, Complex.star_def] using
        ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).star
    convert (hθ hmem).mul (hdz.pow k) using 1
    · dsimp only [r, a, b, t, s, f]
      simp only [Pi.pow_apply]
      ring
  have hri : IntegrableOn r (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hr.integrable (by norm_num)
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    hsz' hri hd (2 * Real.pi) ⟨Real.two_pi_pos.le, le_rfl⟩
  have hs0 : s 0 = 0 := roughGauge_partial_succ_zero hW p m α j N
  have hsT : s (2 * Real.pi) = 0 := roughGauge_partial_succ_endpoint p m α hα j N
  simp only [hs0, hsT, zero_mul, zero_add] at he
  have hia := intervalIntegrable_boundary_of_memLp a ha
  have hib := intervalIntegrable_boundary_of_memLp b hb
  have hit := intervalIntegrable_boundary_of_memLp t ht
  dsimp only [r] at he
  rw [intervalIntegral.integral_add ((hia.const_mul _).add (hib.const_mul _)) hit,
    intervalIntegral.integral_add (hia.const_mul _) (hib.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  change 0 = physicalDrivenQ E ^ 2 * physicalDrivenMomentPartial γ E f j N k +
    (k : ℂ) * physicalDrivenMomentPartial γ E f (j + 1) N (k - 1) +
      physicalDrivenTailMoment γ E f j N k at he
  exact eq_neg_of_add_eq_zero_left he.symm

include hK hγ hW in
theorem roughVekuaGauge_momentPartial_tendsto (p : BoundaryL2) (m α : ℂ) (j k : ℕ) :
    Tendsto (fun N : ℕ => physicalDrivenMomentPartial γ E
      (roughVekuaDrivenVector γ E W p m α) j N k) atTop
      (𝓝 (physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k)) := by
  let v := roughVekuaRegularCorrection γ E W p m α
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  cases j with
  | succ j =>
    have he (N : ℕ) : physicalDrivenMomentPartial γ E
        (roughVekuaDrivenVector γ E W p m α) (j + 1) N k =
        physicalDrivenMomentPartial γ E v (j + 1) N k := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [v]
      rw [roughVekuaGauge_partial_succ_eq p m α j N θ]
    have he' : physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) k =
        physicalDrivenMoment γ E v (j + 1) k := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [v]
      rw [roughVekuaGauge_succ_eq p m α j θ]
    simpa only [he, he'] using physicalDrivenMomentPartial_tendsto γ hγ E v hv (j + 1) k
  | zero =>
    let w : ℝ → ℂ := fun θ => conj (deriv γ θ) * conj (physicalDrivenCentered γ θ) ^ k
    let c : ℂ := ∫ θ in (0 : ℝ)..(2 * Real.pi), w θ * (-Complex.I * p θ)
    have hw : Continuous w := (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul
      ((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow k)
    have hbase : MemLp (fun θ : ℝ => w θ * (-Complex.I * p θ)) 2 μB := by
      simpa only [Pi.smul_def, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        (roughGauge_continuous_mul_memLp hw (Lp.memLp p)).const_smul (-Complex.I)
    have hi := intervalIntegrable_boundary_of_memLp _ hbase
    have he (N : ℕ) : physicalDrivenMomentPartial γ E
        (roughVekuaDrivenVector γ E W p m α) 0 N k = c + physicalDrivenMomentPartial γ E v 0 N k := by
      have ht := intervalIntegrable_boundary_of_memLp _ (roughGauge_continuous_mul_memLp hw
        (roughGauge_continuous_memLp (physicalDrivenGaugePartial_continuousOn γ hγ.continuous E v hv 0 N)))
      calc
        _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), w θ * (-Complex.I * p θ) +
            w θ * physicalDrivenGaugePartial γ E v 0 N θ := by
          apply intervalIntegral.integral_congr
          intro θ _
          dsimp only [w, v]
          rw [roughVekuaGauge_partial_zero_split p m α N θ]
          ring
        _ = c + physicalDrivenMomentPartial γ E v 0 N k := by
          rw [intervalIntegral.integral_add hi ht]
          congr 1
          apply intervalIntegral.integral_congr
          intro θ _
          dsimp only [physicalDrivenMomentPartial, w]
          ring
    have he' : physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) 0 k =
        c + physicalDrivenMoment γ E v 0 k := by
      have ht := intervalIntegrable_boundary_of_memLp _ (roughGauge_continuous_mul_memLp hw
        (roughVekuaGauge_regular_memLp hK hγ hW p m α 0))
      calc
        _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), w θ * (-Complex.I * p θ) +
            w θ * physicalDrivenGauge γ E v 0 θ := by
          apply intervalIntegral.integral_congr
          intro θ _
          dsimp only [w, v]
          rw [roughVekuaGauge_zero_split p m α θ]
          ring
        _ = c + physicalDrivenMoment γ E v 0 k := by
          rw [intervalIntegral.integral_add hi ht]
          congr 1
          apply intervalIntegral.integral_congr
          intro θ _
          dsimp only [physicalDrivenMoment, w]
          ring
    simpa only [he, he'] using
      (physicalDrivenMomentPartial_tendsto γ hγ E v hv 0 k).const_add c

include hK hγ hW in
theorem roughVekuaGauge_tailMoment_tendsto_zero (p : BoundaryL2) (m α : ℂ) (j k : ℕ) :
    Tendsto (fun N : ℕ => physicalDrivenTailMoment γ E
      (roughVekuaDrivenVector γ E W p m α) j N k) atTop (𝓝 0) := by
  have he (N : ℕ) : physicalDrivenTailMoment γ E (roughVekuaDrivenVector γ E W p m α) j N k =
      physicalDrivenTailMoment γ E (roughVekuaRegularCorrection γ E W p m α) j N k := by
    apply intervalIntegral.integral_congr
    intro θ _
    change deriv γ θ * physicalDrivenPower γ N θ *
      physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (N + j + 2) θ *
      conj (physicalDrivenCentered γ θ) ^ k = _
    rw [roughVekuaGauge_scaledRow_succ_eq p m α (N + j + 1) θ]
  simpa only [he] using physicalDrivenTailMoment_tendsto_zero γ hγ E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) j k

include hK hγ hW in
theorem roughVekuaGauge_moment_recurrence (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0)
    (j k : ℕ) :
    physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k +
      (k : ℂ) * physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) (k - 1) = 0 := by
  have hl := ((roughVekuaGauge_momentPartial_tendsto hK hγ hW p m α j k).const_mul (physicalDrivenQ E ^ 2)).add
      ((roughVekuaGauge_momentPartial_tendsto hK hγ hW p m α (j + 1) (k - 1)).const_mul (k : ℂ))
  have hr : Tendsto (fun N => physicalDrivenQ E ^ 2 * physicalDrivenMomentPartial γ E
      (roughVekuaDrivenVector γ E W p m α) j N k + (k : ℂ) * physicalDrivenMomentPartial γ E
        (roughVekuaDrivenVector γ E W p m α) (j + 1) N (k - 1)) atTop (𝓝 0) := by
    simpa only [roughVekuaGauge_momentPartial_recurrence hK hγ hW p m α hα, neg_zero] using
      (roughVekuaGauge_tailMoment_tendsto_zero hK hγ hW p m α j k).neg
  exact tendsto_nhds_unique hl hr

include hK hγ hW in
/-- Every original physical moment vanishes, including all moments of
the rough zeroth gauge. No trace point value of its primitive is used. -/
theorem roughVekuaGauge_physicalMoment_eq_zero (hE : 0 < E) (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0)
    (j k : ℕ) :
    physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k = 0 := by
  induction k generalizing j with
  | zero =>
    have h := roughVekuaGauge_moment_recurrence hK hγ hW p m α hα j 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)
  | succ k ih =>
    have h := roughVekuaGauge_moment_recurrence hK hγ hW p m α hα j (k + 1)
    rw [Nat.add_sub_cancel, ih (j + 1), mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)

include hK hγ hW in
private theorem roughGauge_regular_zero_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0)
        (2 * deriv γ θ * physicalDrivenScaledRow E
          (roughVekuaRegularCorrection γ E W p m α) 1 θ - Complex.I * m) θ := by
  filter_upwards [roughVekuaRegularCorrection_ae_hasDerivAt hK hγ hW p m α]
    with θ hθ hmem
  have hd := (((innerSL ℂ (basisVec 0)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hθ hmem)).const_mul (Real.sqrt 2 : ℂ)
  change HasDerivAt
    (fun t : ℝ => (Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0)
      (roughVekuaRegularCorrection γ E W p m α t))
    ((Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0)
      (transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
        (-(Complex.I / (Real.sqrt 2 : ℂ))) • roughVekuaRegularForce γ E p m θ)) θ at hd
  rw [roughVekuaRegularCorrection_derivative_eq_transportCoeff] at hd
  simp only [inner_basisVec] at hd
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hcoup (a b c : ℂ) :
      (Real.sqrt 2 : ℂ) * (a * (b * ((Real.sqrt 2 : ℂ) * c))) =
        2 * b * (a * c) := by
    calc
      _ = (Real.sqrt 2 : ℂ) ^ 2 * (b * (a * c)) := by ring
      _ = _ := by rw [hs]; ring
  have hforce : (Real.sqrt 2 : ℂ) * (-(Complex.I / (Real.sqrt 2 : ℂ)) * m) =
      -Complex.I * m := by
    field_simp [hs0]
  have he : physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0 =
      fun t : ℝ => (Real.sqrt 2 : ℂ) *
        (roughVekuaRegularCorrection γ E W p m α t : ℕ → ℂ) 0 := by
    funext t
    simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_zero, one_mul, if_true]
  rw [he]
  apply hd.congr_deriv
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, basisVec_coord, if_true, mul_one]
  rw [transportCoeff_apply_coord, shiftN_apply_zero,
    roughVekuaDrivenVector_positive_coord]
  simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_one, physicalDrivenQ,
    Nat.one_ne_zero, if_false, shiftWeight, if_true, mul_zero, add_zero]
  rw [mul_add, hcoup, hforce]
  ring

include hK hγ hW in
private theorem roughGauge_regular_positive_ae_hasDerivAt
    (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt
        (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 1))
        (deriv γ θ * physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 2) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ((if n = 0 then -Complex.I * p θ else 0) +
              physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) n θ)) θ := by
  filter_upwards [roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α n]
    with θ hθ hmem
  have he : physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 1) =
      physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 1) :=
    funext (roughVekuaGauge_scaledRow_succ_eq p m α n)
  rw [he] at hθ
  convert hθ hmem using 1
  cases n with
  | zero => rw [roughVekuaGauge_scaledRow_succ_eq, roughVekuaGauge_scaledRow_zero_split]; rfl
  | succ n => simp only [Nat.succ_ne_zero, if_false, zero_add, roughVekuaGauge_scaledRow_succ_eq]

/-- The actual L2 derivative of the continuous correction gauge. The
rough primitive occurs only multiplied by a true continuous coefficient. -/
def roughVekuaGaugeRegularDerivative (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (p : BoundaryL2) (m α : ℂ) (θ : ℝ) : ℂ :=
  physicalDrivenGaugeZeroContinuousPart γ E (roughVekuaRegularCorrection γ E W p m α) θ -
    Complex.I * m - Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
      physicalDrivenPower γ 1 θ * p θ

include hK hγ hW in
theorem roughVekuaGauge_regular_derivative_memLp (p : BoundaryL2) (m α : ℂ) :
    MemLp (roughVekuaGaugeRegularDerivative γ E W p m α) 2 μB := by
  have hc := physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α)
  have ha : Continuous (fun θ => Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
      physicalDrivenPower γ 1 θ) := by
    have hp : Continuous (physicalDrivenPower γ 1) := by
      unfold physicalDrivenPower physicalDrivenCentered
      exact ((hγ.continuous.sub continuous_const).neg.pow 1).div_const _
    exact ((continuous_const.mul (Complex.continuous_conj.comp hγ.continuous_deriv_one)).mul hp)
  exact ((roughGauge_continuous_memLp hc).sub (memLp_const (Complex.I * m))).sub
    (roughGauge_continuous_mul_memLp ha (Lp.memLp p))

include hK hγ hW in
private theorem roughGauge_regular_partial_zero_ae_hasDerivAt
    (p : BoundaryL2) (m α : ℂ) (N : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt
        (physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 1))
        (deriv γ θ * physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 1 θ -
          Complex.I * m + deriv γ θ * physicalDrivenGaugeTerm γ E
            (roughVekuaRegularCorrection γ E W p m α) 1 (N + 1) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E
              (roughVekuaRegularCorrection γ E W p m α) l θ -
          Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenPower γ 1 θ * p θ) θ := by
  induction N with
  | zero =>
    filter_upwards [roughGauge_regular_zero_ae_hasDerivAt hK hγ hW p m α,
      roughGauge_regular_positive_ae_hasDerivAt hK hγ hW p m α 0] with θ h0 h1 hmem
    have hd := (h0 hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ 0 θ).mul (h1 hmem))
    convert hd using 1
    · funext s
      norm_num [physicalDrivenGaugePartial, Finset.sum_range_succ,
        physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm, physicalDrivenPower,
        physicalDrivenScaledRow, physicalDrivenRow, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
      simp [physicalDrivenGaugeTerm,
        physicalDrivenShiftedGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow,
        physicalDrivenRow, Nat.factorial] ; ring
  | succ N ih =>
    filter_upwards [ih, roughGauge_regular_positive_ae_hasDerivAt hK hγ hW p m α (N + 1)]
      with θ hθ hd hmem
    have he : physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α)
        0 (N + 2) = fun t =>
          physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 1) t +
            physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 2) t := by
      funext t
      exact Finset.sum_range_succ _ _
    rw [show N + 1 + 1 = N + 2 by omega, he]
    have hsum :
        (∑ l ∈ Finset.range (N + 2), physicalDrivenShiftedGaugeTerm γ E
          (roughVekuaRegularCorrection γ E W p m α) l θ) =
        (∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E
          (roughVekuaRegularCorrection γ E W p m α) l θ) +
          physicalDrivenShiftedGaugeTerm γ E
            (roughVekuaRegularCorrection γ E W p m α) (N + 1) θ := by
      rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ]
    have hweighted := congrArg
      (fun q : ℂ => physicalDrivenQ E ^ 2 * conj (deriv γ θ) * q) hsum
    have hweighted' :
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            (∑ l ∈ Finset.range (N + 2), physicalDrivenShiftedGaugeTerm γ E
              (roughVekuaRegularCorrection γ E W p m α) l θ) =
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ((∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E
              (roughVekuaRegularCorrection γ E W p m α) l θ) +
              physicalDrivenShiftedGaugeTerm γ E
                (roughVekuaRegularCorrection γ E W p m α) (N + 1) θ) := by
      simpa only using hweighted
    convert (hθ hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ (N + 1) θ).mul (hd hmem)) using 1
    · funext t
      simp only [Pi.add_apply, Pi.mul_apply, physicalDrivenGaugeTerm]
    · rw [hweighted']
      simp only [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm,
        Nat.succ_ne_zero, if_false, zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      simp only [physicalDrivenPower, physicalDrivenCentered, physicalDrivenScaledRow,
        physicalDrivenRow]
      rw [show N + 2 = (N + 1) + 1 by omega, Nat.factorial_succ]
      have hf : ((N + 1).factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (N + 1)
      field_simp [hf]
      ring

private theorem roughGauge_regular_partial_at_initial_vector
    (p : BoundaryL2) (m α : ℂ) (N : ℕ) {θ : ℝ}
    (hv : roughVekuaRegularCorrection γ E W p m α θ = α • basisVec 0) :
    physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 N θ =
      (Real.sqrt 2 : ℂ) * α := by
  induction N with
  | zero => simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower,
      physicalDrivenScaledRow, physicalDrivenRow, hv, basisVec_coord]
  | succ N ih =>
    rw [physicalDrivenGaugePartial, Finset.sum_range_succ]
    change physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 N θ + _ = _
    rw [ih]
    simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow,
      hv, basisVec_coord]

include hK hγ hW in
private theorem roughGauge_regular_partial_zero_primitive
    (p : BoundaryL2) (m α : ℂ) (N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 1) θ =
      (Real.sqrt 2 : ℂ) * α +
      (∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 1 s -
          Complex.I * m - Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) *
            physicalDrivenPower γ 1 s * p s) +
      (∫ s in (0 : ℝ)..θ, deriv γ s * physicalDrivenGaugeTerm γ E
        (roughVekuaRegularCorrection γ E W p m α) 1 (N + 1) s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E
          (roughVekuaRegularCorrection γ E W p m α) l s) := by
  let v := roughVekuaRegularCorrection γ E W p m α
  let a : ℝ → ℂ := fun s => deriv γ s * physicalDrivenScaledRow E v 1 s - Complex.I * m -
    Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) * physicalDrivenPower γ 1 s * p s
  let t : ℝ → ℂ := fun s => deriv γ s * physicalDrivenGaugeTerm γ E v 1 (N + 1) s
  let b : ℝ → ℂ := fun s => conj (deriv γ s) *
    ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have ha : MemLp a 2 μB := by
    have hc : ContinuousOn (fun s => deriv γ s * physicalDrivenScaledRow E v 1 s)
        (Icc 0 (2 * Real.pi)) := hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn v hv 1))
    have hp : Continuous (fun s => Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) *
        physicalDrivenPower γ 1 s) := by
      have hp' : Continuous (physicalDrivenPower γ 1) := by
        unfold physicalDrivenPower physicalDrivenCentered
        exact ((hγ.continuous.sub continuous_const).neg.pow 1).div_const _
      exact ((continuous_const.mul (Complex.continuous_conj.comp hγ.continuous_deriv_one)).mul hp')
    exact ((roughGauge_continuous_memLp hc).sub (memLp_const (Complex.I * m))).sub
      (roughGauge_continuous_mul_memLp hp (Lp.memLp p))
  have ht : ContinuousOn t (Icc 0 (2 * Real.pi)) :=
    hγ.continuous_deriv_one.continuousOn.mul
      (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E v hv 1 (N + 1))
  have hb : ContinuousOn b (Icc 0 (2 * Real.pi)) :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (continuousOn_finset_sum _ fun l _ =>
        physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E v hv l)
  have hr : MemLp (fun s => a s + t s + physicalDrivenQ E ^ 2 * b s) 2 μB := by
    simpa only [smul_eq_mul, Pi.add_def, Pi.smul_def] using (ha.add (roughGauge_continuous_memLp ht)).add
      ((roughGauge_continuous_memLp hb).const_smul (physicalDrivenQ E ^ 2))
  have hd : ∀ᵐ s, s ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenGaugePartial γ E v 0 (N + 1))
        (a s + t s + physicalDrivenQ E ^ 2 * b s) s := by
    filter_upwards [roughGauge_regular_partial_zero_ae_hasDerivAt hK hγ hW p m α N]
      with s hs hmem
    convert hs hmem using 1
    · dsimp only [a, t, b, v]
      ring
  have hri : IntegrableOn (fun s => a s + t s + physicalDrivenQ E ^ 2 * b s)
      (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hr.integrable (by norm_num)
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (roughGauge_regular_partial_ac hK hγ hW p m α 0 (N + 1)) hri hd θ hθ
  rw [roughGauge_regular_partial_at_initial_vector p m α (N + 1)
    (roughVekuaRegularCorrection_zero hW p m α)] at he
  have hsub : uIcc 0 θ ⊆ Icc 0 (2 * Real.pi) := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have hai : IntervalIntegrable a volume 0 θ := by
    have hI : IntegrableOn a (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact ha.integrable (by norm_num)
    exact (hI.mono_set hsub).intervalIntegrable
  have hti : IntervalIntegrable t volume 0 θ := (ht.mono hsub).intervalIntegrable
  have hbi : IntervalIntegrable b volume 0 θ := (hb.mono hsub).intervalIntegrable
  rw [intervalIntegral.integral_add (hai.add hti) (hbi.const_mul _),
    intervalIntegral.integral_add hai hti, intervalIntegral.integral_const_mul] at he
  simpa only [a, t, b, v, add_assoc] using he

include hK hγ hW in
/-- The correction gauge is an actual primitive of the computed L2
derivative. The factorial tail and the shifted series are integrated
before taking their genuine limits. -/
theorem roughVekuaGauge_regular_primitive (p : BoundaryL2) (m α : ℂ)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0 θ =
      (Real.sqrt 2 : ℂ) * α +
        ∫ s in (0 : ℝ)..θ, roughVekuaGaugeRegularDerivative γ E W p m α s := by
  classical
  let v := roughVekuaRegularCorrection γ E W p m α
  let a : ℝ → ℂ := fun s => deriv γ s * physicalDrivenScaledRow E v 1 s - Complex.I * m -
    Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) * physicalDrivenPower γ 1 s * p s
  let b : ℝ → ℂ := fun s => conj (deriv γ s) * physicalDrivenShiftedGauge γ E v s
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have hp : Tendsto (fun N : ℕ => physicalDrivenGaugePartial γ E v 0 (N + 1) θ) atTop
      (𝓝 (physicalDrivenGauge γ E v 0 θ)) := by
    simpa [physicalDrivenGaugePartial, physicalDrivenGauge, Function.comp_def] using
      ((summable_norm_physicalDrivenGaugeTerm γ E v 0 θ).of_norm.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 2)
  have ht := ((physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ.continuous E v hv 1
    (deriv γ) hγ.continuous_deriv_one.continuousOn hθ).summable.tendsto_atTop_zero).comp (tendsto_add_atTop_nat 1)
  have hs := physicalDrivenShiftedGauge_weightedIntegral_hasSum_to γ hγ.continuous E v hv
    (fun s => conj (deriv γ s))
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn hθ
  have hsub : uIcc 0 θ ⊆ Icc 0 (2 * Real.pi) := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have he (N : ℕ) : (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s) =
      ∑ l ∈ Finset.range (N + 1), ∫ s in (0 : ℝ)..θ,
        conj (deriv γ s) * physicalDrivenShiftedGaugeTerm γ E v l s := by
    simp_rw [Finset.mul_sum]
    apply intervalIntegral.integral_finset_sum
    intro l _
    exact (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E v hv l)).mono hsub).intervalIntegrable
  have hb : Tendsto (fun N : ℕ => ∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s) atTop
      (𝓝 (∫ s in (0 : ℝ)..θ, b s)) := by
    have h := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact h.congr' (Eventually.of_forall fun N => (he N).symm)
  have hr : Tendsto (fun N : ℕ => (Real.sqrt 2 : ℂ) * α +
      (∫ s in (0 : ℝ)..θ, a s) +
      (∫ s in (0 : ℝ)..θ, deriv γ s * physicalDrivenGaugeTerm γ E v 1 (N + 1) s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s)) atTop
      (𝓝 ((Real.sqrt 2 : ℂ) * α + (∫ s in (0 : ℝ)..θ, a s) +
        physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, b s))) := by
    simpa only [add_zero, Function.comp_apply] using
      ((tendsto_const_nhds (x := (Real.sqrt 2 : ℂ) * α + ∫ s in (0 : ℝ)..θ, a s)).add ht).add
        (hb.const_mul (physicalDrivenQ E ^ 2))
  have hlim : physicalDrivenGauge γ E v 0 θ =
      (Real.sqrt 2 : ℂ) * α + (∫ s in (0 : ℝ)..θ, a s) +
        physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, b s) :=
    tendsto_nhds_unique hp (hr.congr' (Eventually.of_forall fun N =>
      (roughGauge_regular_partial_zero_primitive hK hγ hW p m α N hθ).symm))
  have ha : MemLp a 2 μB := by
    have hc : ContinuousOn (fun s => deriv γ s * physicalDrivenScaledRow E v 1 s)
        (Icc 0 (2 * Real.pi)) := hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn v hv 1))
    have hco : Continuous (fun s => Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) *
        physicalDrivenPower γ 1 s) := by
      have hp' : Continuous (physicalDrivenPower γ 1) := by
        unfold physicalDrivenPower physicalDrivenCentered
        exact ((hγ.continuous.sub continuous_const).neg.pow 1).div_const _
      exact ((continuous_const.mul (Complex.continuous_conj.comp hγ.continuous_deriv_one)).mul hp')
    exact ((roughGauge_continuous_memLp hc).sub (memLp_const (Complex.I * m))).sub
      (roughGauge_continuous_mul_memLp hco (Lp.memLp p))
  have hai : IntervalIntegrable a volume 0 θ := by
    have hI : IntegrableOn a (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact ha.integrable (by norm_num)
    exact (hI.mono_set hsub).intervalIntegrable
  have hbi : IntervalIntegrable b volume 0 θ :=
    (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGauge_continuousOn γ hγ.continuous E v hv)).mono hsub).intervalIntegrable
  rw [hlim, ← intervalIntegral.integral_const_mul, add_assoc,
    ← intervalIntegral.integral_add hai (hbi.const_mul _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [a, b, roughVekuaGaugeRegularDerivative, physicalDrivenGaugeZeroContinuousPart, v]
  ring

include hK hγ hW in
theorem roughVekuaGauge_regular_absolutelyContinuous (p : BoundaryL2) (m α : ℂ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0)
      0 (2 * Real.pi) := by
  have hi := intervalIntegrable_boundary_of_memLp _
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => (Real.sqrt 2 : ℂ) * α) 0 (2 * Real.pi) := by
    simpa only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ)) _ (𝓝 0))
  have hp := hconst.add (absolutelyContinuousOnInterval_intervalIntegral_banach hi
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩))
  apply roughGauge_ac_congr hp
  intro θ hθ
  exact (roughVekuaGauge_regular_primitive hK hγ hW p m α hθ).symm

include hK hγ hW in
theorem roughVekuaGauge_regular_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0)
        (roughVekuaGaugeRegularDerivative γ E W p m α θ) θ := by
  have hi := intervalIntegrable_boundary_of_memLp _
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α)
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hi]
    with θ hθ hmem
  refine ((hθ hmem).const_add ((Real.sqrt 2 : ℂ) * α)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with t ht
  exact roughVekuaGauge_regular_primitive hK hγ hW p m α (Ioo_subset_Icc_self ht)

private theorem roughGauge_regular_at_initial_vector (p : BoundaryL2) (m α : ℂ)
    {θ : ℝ} (hv : roughVekuaRegularCorrection γ E W p m α θ = α • basisVec 0) :
    physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0 θ =
      (Real.sqrt 2 : ℂ) * α := by
  have hs := (summable_norm_physicalDrivenGaugeTerm γ E
    (roughVekuaRegularCorrection γ E W p m α) 0 θ).of_norm
  rw [physicalDrivenGauge, hs.tsum_eq_zero_add]
  have ht : (fun l : ℕ => physicalDrivenGaugeTerm γ E
      (roughVekuaRegularCorrection γ E W p m α) 0 (l + 1) θ) = fun _ => (0 : ℂ) := by
    funext l
    simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow,
      hv, basisVec_coord]
  rw [ht, tsum_zero, add_zero]
  simp [physicalDrivenGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow,
    physicalDrivenRow, hv, basisVec_coord]

include hK hγ hW in
/-- The regular factorial gauge has true H1 Fourier coefficients. Both
endpoints are sqrt(2) α by the computed vector endpoints; no endpoint or
derivative of the rough primitive is assumed. -/
theorem roughVekuaGauge_regular_isSobolevSeq_one (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0)) := by
  exact isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (roughVekuaGauge_regular_absolutelyContinuous hK hγ hW p m α)
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α)
    (roughVekuaGauge_regular_ae_hasDerivAt hK hγ hW p m α)
    ((roughGauge_regular_at_initial_vector p m α (roughVekuaRegularCorrection_zero hW p m α)).trans (roughGauge_regular_at_initial_vector p m α hα).symm)

include hK hγ hW in
/-- Genuine observation-kernel data have an L2 zeroth gauge with all
physical moments zero and an H1 regular correction. The original
normalized mean and the full zero mode are retained. -/
theorem roughVekuaGauge_exists_regular_of_projObsDual_eq_zero
    (hE : 0 < E) (y : L2Z) (hy : projObsDual W y = 0) :
    ∃ α : ℂ,
      roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α (2 * Real.pi) = α • basisVec 0 ∧
      MemLp (physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W
        (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0) 2 μB ∧
      MemLp (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W
        (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0) 2 μB ∧
      IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos
        (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W
          (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0)) ∧
      (∀ θ, physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W
        (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0 θ =
          -Complex.I * roughNormalizedPrimitive y θ +
            physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W
              (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0 θ) ∧
      ∀ j k, physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W
        (roughNormalizedPrimitive y) (roughNormalizedMean y) α) j k = 0 := by
  obtain ⟨α, _, hα⟩ :=
    roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero hK hγ hW y hy
  refine ⟨α, hα, roughVekuaGauge_zero_memLp hK hγ hW _ _ α,
    roughVekuaGauge_regular_memLp hK hγ hW _ _ α 0,
    roughVekuaGauge_regular_isSobolevSeq_one hK hγ hW _ _ α hα,
    roughVekuaGauge_zero_split _ _ α, ?_⟩
  exact fun j k => roughVekuaGauge_physicalMoment_eq_zero hK hγ hW hE _ _ α hα j k

end GenuineGauge

end PolyaNeumann

end
