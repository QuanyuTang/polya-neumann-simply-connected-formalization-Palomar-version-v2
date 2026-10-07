module

public import RequestProject.SobolevMultiplier

/-!
# Sobolev gain from an actual coefficient estimate

An estimate `|a_n| ≤ C/(1+|n|)` gives every Fourier Sobolev order less
than one half. The operator version supplies a bounded weighted operator
and its exact factorization through the compact Sobolev embedding.

This module does not infer coefficient decay from compactness. Its decay
hypothesis must be proved for the physical operator to which it is applied.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open scoped Topology

theorem summable_sobWeight_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun n : ℤ => sobWeight n ^ p) := by
  have hi := Real.summable_abs_int_rpow (b := -p) (by linarith)
  simp only [neg_neg] at hi
  have hz : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [hn])
  apply Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (sobWeight_pos n).le p) _ (hi.add hz)
  intro n
  by_cases hn : n = 0
  · subst n
    have hp0 : p ≠ 0 := by linarith
    simp [sobWeight, Real.zero_rpow hp0]
  · simp only [hn, if_false, add_zero]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    apply Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hn') _ (by linarith)
    unfold sobWeight
    linarith

def coefficientGainConst (δ : ℝ) : ℝ :=
  ∑' n : ℤ, sobWeight n ^ (2 * δ - 2)

theorem coefficientGainConst_nonneg (δ : ℝ) : 0 ≤ coefficientGainConst δ :=
  tsum_nonneg (fun n => Real.rpow_nonneg (sobWeight_pos n).le _)

private lemma coefficient_gain_weight {δ C : ℝ}
    {a : ℤ → ℂ} (ha : ∀ n, ‖a n‖ ≤ C / sobWeight n) (n : ℤ) :
    (sobWeight n ^ δ * ‖a n‖) ^ 2 ≤ C ^ 2 * sobWeight n ^ (2 * δ - 2) := by
  have hp := sobWeight_pos n
  calc
    _ ≤ (sobWeight n ^ δ * (C / sobWeight n)) ^ 2 := by
      gcongr
      exact ha n
    _ = C ^ 2 * (sobWeight n ^ δ / sobWeight n) ^ 2 := by ring
    _ = _ := by
      rw [← Real.rpow_sub_one hp.ne' δ]
      have he : (sobWeight n ^ (δ - 1)) ^ 2 = sobWeight n ^ (2 * δ - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
        congr 1
        norm_num
        ring
      rw [he]

theorem isSobolevSeq_of_coefficient_decay {δ C : ℝ} (hδ : δ < 1 / 2)
    {a : ℤ → ℂ} (ha : ∀ n, ‖a n‖ ≤ C / sobWeight n) :
    IsSobolevSeq δ a ∧ sobNormSq δ a ≤ C ^ 2 * coefficientGainConst δ := by
  have hs := (summable_sobWeight_rpow (by linarith : 2 * δ - 2 < -1)).mul_left (C ^ 2)
  have hw := coefficient_gain_weight (δ := δ) ha
  have hseq : IsSobolevSeq δ a :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hw hs
  refine ⟨hseq, ?_⟩
  unfold sobNormSq coefficientGainConst
  rw [← tsum_mul_left]
  exact hseq.tsum_le_tsum hw hs

section Operator

variable (A : L2Z →L[ℂ] L2Z) {δ C : ℝ} (hδ : δ < 1 / 2) (hC : 0 ≤ C)
  (hA : ∀ (b : L2Z) (n : ℤ), ‖A b n‖ ≤ C * ‖b‖ / sobWeight n)

def coefficientGainLin : L2Z →ₗ[ℂ] L2Z where
  toFun b := ⟨fun n => ((sobWeight n ^ δ : ℝ) : ℂ) * A b n,
    memℓp_two_iff_summable.mpr (by
      have hs := (isSobolevSeq_of_coefficient_decay hδ (hA b)).1
      simpa only [norm_mul, Complex.norm_of_nonneg
        (Real.rpow_nonneg (sobWeight_pos _).le _)] using hs)⟩
  map_add' b c := by
    apply lp.ext
    funext n
    change ((sobWeight n ^ δ : ℝ) : ℂ) * A (b + c) n = _
    simp only [map_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c b := by
    apply lp.ext
    funext n
    change ((sobWeight n ^ δ : ℝ) : ℂ) * A (c • b) n =
      c * (((sobWeight n ^ δ : ℝ) : ℂ) * A b n)
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

include hC in
theorem norm_coefficientGainLin_le (b : L2Z) :
    ‖coefficientGainLin A hδ hA b‖ ≤
      (C * Real.sqrt (coefficientGainConst δ)) * ‖b‖ := by
  have hb := (isSobolevSeq_of_coefficient_decay hδ (hA b)).2
  have hsq : ‖coefficientGainLin A hδ hA b‖ ^ 2 ≤
      ((C * Real.sqrt (coefficientGainConst δ)) * ‖b‖) ^ 2 := by
    rw [norm_sq_L2Z]
    change (∑' n : ℤ, ‖((sobWeight n ^ δ : ℝ) : ℂ) * A b n‖ ^ 2) ≤ _
    simp only [norm_mul, Complex.norm_of_nonneg
      (Real.rpow_nonneg (sobWeight_pos _).le _)]
    calc
      _ ≤ (C * ‖b‖) ^ 2 * coefficientGainConst δ := hb
      _ = _ := by
        simp only [mul_pow, Real.sq_sqrt (coefficientGainConst_nonneg δ)]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

def coefficientGainOperator : L2Z →L[ℂ] L2Z :=
  (coefficientGainLin A hδ hA).mkContinuous
    (C * Real.sqrt (coefficientGainConst δ)) (norm_coefficientGainLin_le A hδ hC hA)

theorem coefficientGainOperator_factorization (hδ0 : 0 ≤ δ) :
    (sobolevSmoothing δ hδ0).comp (coefficientGainOperator A hδ hC hA) = A := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  change ((sobWeight n ^ (-δ) : ℝ) : ℂ) *
    (((sobWeight n ^ δ : ℝ) : ℂ) * A b n) = A b n
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n),
    neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]

include hδ hC hA in
theorem isCompactOperator_of_coefficient_decay (hδ0 : 0 < δ) : IsCompactOperator A := by
  rw [← coefficientGainOperator_factorization A hδ hC hA hδ0.le]
  exact (isCompactOperator_sobolevSmoothing hδ0).comp_clm
    (coefficientGainOperator A hδ hC hA)

end Operator

end PolyaNeumann

end
