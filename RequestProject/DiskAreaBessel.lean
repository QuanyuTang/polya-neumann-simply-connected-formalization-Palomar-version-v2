module

public import RequestProject.DiskAreaGram

/-!
# Bessel estimates for physical area moments on the disk

The holomorphic and antiholomorphic monomials form two separate
orthogonal families in the actual area L² space. Their normalization
gives the weighted mass-moment estimate used in the Neumann equation.
The two zero modes are not combined into one orthonormal family.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

def diskHolomorphicArea (m : ℕ) : L2 (ball (0 : ℂ) 1) :=
  ((diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)).memLp'
    2 (μ := volume.restrict (ball (0 : ℂ) 1))).toLp
      (diskHarmonicCutoff (diskHolomorphicMode m))

def diskAntiholomorphicArea (m : ℕ) : L2 (ball (0 : ℂ) 1) :=
  ((diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)).memLp'
    2 (μ := volume.restrict (ball (0 : ℂ) 1))).toLp
      (diskHarmonicCutoff (diskAntiholomorphicMode m))

theorem diskHolomorphicArea_ae (m : ℕ) :
    (diskHolomorphicArea m : ℂ → ℂ) =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      fun z => z ^ m := by
  filter_upwards [((diskHarmonicCutoff_testFunction
    (contDiff_diskHolomorphicMode m)).memLp'
      2 (μ := volume.restrict (ball (0 : ℂ) 1))).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskHolomorphicArea m) z = diskHarmonicCutoff (diskHolomorphicMode m) z at hz
  rw [hz, diskHarmonicCutoff_eq_closedDisk _ (ball_subset_closedBall hzD)]
  rfl

theorem diskAntiholomorphicArea_ae (m : ℕ) :
    (diskAntiholomorphicArea m : ℂ → ℂ) =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      fun z => conj z ^ m := by
  filter_upwards [((diskHarmonicCutoff_testFunction
    (contDiff_diskAntiholomorphicMode m)).memLp'
      2 (μ := volume.restrict (ball (0 : ℂ) 1))).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskAntiholomorphicArea m) z = diskHarmonicCutoff (diskAntiholomorphicMode m) z at hz
  rw [hz, diskHarmonicCutoff_eq_closedDisk _ (ball_subset_closedBall hzD)]
  rfl

theorem inner_diskHolomorphicArea (m n : ℕ) :
    ⟪diskHolomorphicArea m, diskHolomorphicArea n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z in ball (0 : ℂ) 1, z ^ n * conj z ^ m := by
      apply integral_congr_ae
      filter_upwards [diskHolomorphicArea_ae m, diskHolomorphicArea_ae n] with z hm hn
      simp only [RCLike.inner_apply', hm, hn, map_pow]
      ring
    _ = _ := by
      rw [integral_disk_area_monomials]
      by_cases hmn : m = n
      · subst n; simp
      · simp [hmn, Ne.symm hmn]

theorem inner_diskAntiholomorphicArea (m n : ℕ) :
    ⟪diskAntiholomorphicArea m, diskAntiholomorphicArea n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n := by
      apply integral_congr_ae
      filter_upwards [diskAntiholomorphicArea_ae m, diskAntiholomorphicArea_ae n]
        with z hm hn
      simp only [RCLike.inner_apply', hm, hn, map_pow, Complex.conj_conj]
    _ = _ := integral_disk_area_monomials m n

theorem inner_diskHolomorphicArea_eq_integral (m : ℕ) (v : L2 (ball (0 : ℂ) 1)) :
    ⟪diskHolomorphicArea m, v⟫_ℂ =
      ∫ z in ball (0 : ℂ) 1, (v : ℂ → ℂ) z * conj z ^ m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diskHolomorphicArea_ae m] with z hz
  simp only [RCLike.inner_apply', hz, map_pow]
  ring

theorem inner_diskAntiholomorphicArea_eq_integral (m : ℕ) (v : L2 (ball (0 : ℂ) 1)) :
    ⟪diskAntiholomorphicArea m, v⟫_ℂ =
      ∫ z in ball (0 : ℂ) 1, (v : ℂ → ℂ) z * z ^ m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diskAntiholomorphicArea_ae m] with z hz
  simp only [RCLike.inner_apply', hz, map_pow, Complex.conj_conj]
  ring

def diskAreaScale (m : ℕ) : ℂ := (Real.sqrt (((m + 1 : ℕ) : ℝ) / π) : ℝ)

private theorem diskAreaScale_normalizes (m : ℕ) :
    conj (diskAreaScale m) *
      (diskAreaScale m * ((π : ℂ) / ((m + 1 : ℕ) : ℂ))) = 1 := by
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt
    (show 0 ≤ ((m + 1 : ℕ) : ℝ) / π by positivity)
  have hr : Real.sqrt (((m + 1 : ℕ) : ℝ) / π) *
      (Real.sqrt (((m + 1 : ℕ) : ℝ) / π) * (π / ((m + 1 : ℕ) : ℝ))) = 1 := by
    calc
      _ = (Real.sqrt (((m + 1 : ℕ) : ℝ) / π) ^ 2 * π) /
          ((m + 1 : ℕ) : ℝ) := by ring
      _ = 1 := by rw [(eq_div_iff Real.pi_ne_zero).mp hsq, div_self hm]
  simp only [diskAreaScale, Complex.conj_ofReal]
  exact_mod_cast hr

def diskNormalizedHolomorphicArea (m : ℕ) : L2 (ball (0 : ℂ) 1) :=
  diskAreaScale m • diskHolomorphicArea m

def diskNormalizedAntiholomorphicArea (m : ℕ) : L2 (ball (0 : ℂ) 1) :=
  diskAreaScale m • diskAntiholomorphicArea m

private theorem orthonormal_of_diskAreaGram
    (v : ℕ → L2 (ball (0 : ℂ) 1))
    (hv : ∀ m n, ⟪v m, v n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0) :
    Orthonormal ℂ (fun m => diskAreaScale m • v m) := by
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst n
    simp only [inner_smul_left, inner_smul_right, hv, ite_true]
    calc
      _ = conj (diskAreaScale m) *
        (diskAreaScale m * ((π : ℂ) / ((m + 1 : ℕ) : ℂ))) := by ring
      _ = 1 := diskAreaScale_normalizes m
  · simp [inner_smul_left, inner_smul_right, hv, hmn]

theorem orthonormal_diskNormalizedHolomorphicArea :
    Orthonormal ℂ diskNormalizedHolomorphicArea :=
  orthonormal_of_diskAreaGram diskHolomorphicArea inner_diskHolomorphicArea

theorem orthonormal_diskNormalizedAntiholomorphicArea :
    Orthonormal ℂ diskNormalizedAntiholomorphicArea :=
  orthonormal_of_diskAreaGram diskAntiholomorphicArea inner_diskAntiholomorphicArea

private theorem norm_sq_diskArea_scaled_inner (m : ℕ)
    (v w : L2 (ball (0 : ℂ) 1)) :
    π * ‖⟪diskAreaScale m • v, w⟫_ℂ‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖⟪v, w⟫_ℂ‖ ^ 2 := by
  rw [inner_smul_left, norm_mul, Complex.norm_conj]
  simp only [diskAreaScale, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (show 0 ≤ ((m + 1 : ℕ) : ℝ) / π by positivity)]
  field_simp [Real.pi_ne_zero]

private theorem diskArea_bessel
    (v : ℕ → L2 (ball (0 : ℂ) 1))
    (hv : Orthonormal ℂ (fun m => diskAreaScale m • v m))
    (w : L2 (ball (0 : ℂ) 1)) :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) * ‖⟪v m, w⟫_ℂ‖ ^ 2) ∧
      (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * ‖⟪v m, w⟫_ℂ‖ ^ 2) ≤ π * ‖w‖ ^ 2 := by
  have hs := hv.inner_products_summable w
  have he (m : ℕ) := norm_sq_diskArea_scaled_inner m (v m) w
  refine ⟨(hs.mul_left π).congr he, ?_⟩
  calc
    _ = π * ∑' m : ℕ, ‖⟪diskAreaScale m • v m, w⟫_ℂ‖ ^ 2 := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun m => (he m).symm)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hv.tsum_inner_products_le w) Real.pi_pos.le

theorem disk_area_holomorphic_bessel (v : L2 (ball (0 : ℂ) 1)) :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in ball (0 : ℂ) 1, (v : ℂ → ℂ) z * conj z ^ m‖ ^ 2) ∧
    (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in ball (0 : ℂ) 1, (v : ℂ → ℂ) z * conj z ^ m‖ ^ 2) ≤ π * ‖v‖ ^ 2 := by
  simpa only [inner_diskHolomorphicArea_eq_integral] using
    diskArea_bessel diskHolomorphicArea orthonormal_diskNormalizedHolomorphicArea v

theorem disk_area_antiholomorphic_bessel (v : L2 (ball (0 : ℂ) 1)) :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in ball (0 : ℂ) 1, (v : ℂ → ℂ) z * z ^ m‖ ^ 2) ∧
    (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in ball (0 : ℂ) 1, (v : ℂ → ℂ) z * z ^ m‖ ^ 2) ≤ π * ‖v‖ ^ 2 := by
  simpa only [inner_diskAntiholomorphicArea_eq_integral] using
    diskArea_bessel diskAntiholomorphicArea orthonormal_diskNormalizedAntiholomorphicArea v

end PolyaNeumann

end
