module

public import RequestProject.ObservationHS

/-!
# Double Fourier coefficients of kernels with Lipschitz rows (toward Lemma 6.6)

Let `k(θ, t)` be a bounded kernel, measurable in `t`, which is `2π`-periodic and uniformly
`K`-Lipschitz in `θ` (for `t ∈ [0, 2π)`). Its rows `θ ↦ k(θ, ·)` are then a periodic Lipschitz
map into `L²(𝕋)`, and the estimate of `FourierLipschitz.lean`, applied to the Fourier basis of
`L²(𝕋)`, gives for the double Fourier coefficients
`k_{n m} = (θ ↦ (t ↦ k(θ, t))^(n))^(m)`

  `∑_{n, m} m² |k_{n m}|² < ∞`     (`summable_sq_mul_kernelCoeff`).

This is the form in which the regularity of the corrected Volterra kernel `r_E` of Lemma 6.6
enters the compactness of the normalized remainder in Lemma 6.7.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory
open scoped InnerProductSpace ComplexConjugate

local instance factTwoPiPosKR : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- `L²(𝕋)` with the normalized Haar measure on `ℝ / 2πℤ`. -/
abbrev L2Circ := Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _)

/-- The representative in `[0, 2π)` of a point of the circle. -/
def circRep (x : AddCircle (2 * π)) : ℝ := (AddCircle.measurableEquivIco (2 * π) 0 x : ℝ)

lemma circRep_mem (x : AddCircle (2 * π)) : circRep x ∈ Set.Ico 0 (2 * π) := by
  have := (AddCircle.measurableEquivIco (2 * π) 0 x).2
  simpa [circRep] using this

lemma liftIco_eq_comp (f : ℝ → ℂ) : AddCircle.liftIco (2 * π) 0 f = fun x => f (circRep x) := rfl

lemma measurable_liftIco_two_pi {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (AddCircle.liftIco (2 * π) 0 f) := by
  rw [liftIco_eq_comp]
  exact hf.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (2 * π) 0).measurable)

lemma memLp_liftIco_two_pi {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ} (hM : ∀ t, ‖f t‖ ≤ M) :
    MemLp (AddCircle.liftIco (2 * π) 0 f) 2 AddCircle.haarAddCircle :=
  MemLp.of_bound (measurable_liftIco_two_pi hf).aestronglyMeasurable M
    (ae_of_all _ fun x => by rw [liftIco_eq_comp]; exact hM _)

/-- Fourier coefficients of the lift of a function on `[0, 2π)` to the circle. -/
lemma fourierCoeff_liftIco_two_pi (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIco (2 * π) 0 f) n = fourierCoeffOn two_pi_pos f n := by
  rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, zero_add, sub_zero]

/-- Fourier coefficients of a complex conjugate. -/
lemma fourierCoeffOn_conj (g : ℝ → ℂ) (m : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => conj (g θ)) m =
      conj (fourierCoeffOn two_pi_pos g (-m)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [smul_eq_mul, map_mul, neg_neg]
  congr 1
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_conj]
  congr 1
  have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  simp [Complex.conj_ofReal, h2]

section Kernel

variable {k : ℝ → ℝ → ℂ} {M : ℝ} {K : NNReal}
  (hmeas : ∀ θ, Measurable (k θ)) (hbd : ∀ θ t, ‖k θ t‖ ≤ M)

/-- The row `θ ↦ k(θ, ·)` as an element of `L²(𝕋)`. -/
def kernelRow (θ : ℝ) : L2Circ :=
  (memLp_liftIco_two_pi (hmeas θ) (hbd θ)).toLp _

include hmeas hbd in
lemma inner_kernelRow_fourierBasis (θ : ℝ) (n : ℤ) :
    ⟪kernelRow hmeas hbd θ, fourierBasis n⟫_ℂ = conj (fourierCoeffOn two_pi_pos (k θ) n) := by
  rw [← inner_conj_symm, ← HilbertBasis.repr_apply_apply, fourierBasis_repr]
  congr 1
  rw [kernelRow, fourierCoeff_congr_ae (MemLp.coeFn_toLp (memLp_liftIco_two_pi (hmeas θ) (hbd θ))),
    fourierCoeff_liftIco_two_pi]

include hmeas hbd in
lemma norm_kernelRow_sub_le
    (hlip : ∀ θ θ' t, t ∈ Set.Ico 0 (2 * π) → ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|) (θ θ' : ℝ) :
    ‖kernelRow hmeas hbd θ - kernelRow hmeas hbd θ'‖ ≤ K * |θ - θ'| := by
  unfold kernelRow
  rw [← MemLp.toLp_sub]
  have h := Lp.norm_le_of_ae_bound (μ := (@AddCircle.haarAddCircle (2 * π) _)) (p := 2)
    (f := MemLp.toLp _ ((memLp_liftIco_two_pi (hmeas θ) (hbd θ)).sub
      (memLp_liftIco_two_pi (hmeas θ') (hbd θ')))) (C := K * |θ - θ'|) (by positivity) ?_
  · have h1 : measureUnivNNReal (@AddCircle.haarAddCircle (2 * π) _) = 1 := by
      simp [measureUnivNNReal]
    simpa [h1] using h
  · filter_upwards [MemLp.coeFn_toLp ((memLp_liftIco_two_pi (hmeas θ) (hbd θ)).sub
      (memLp_liftIco_two_pi (hmeas θ') (hbd θ')))] with x hx
    rw [hx, Pi.sub_apply, liftIco_eq_comp, liftIco_eq_comp]
    exact hlip θ θ' _ (circRep_mem x)

include hmeas hbd in
lemma kernelRow_periodic (hper : ∀ θ t, t ∈ Set.Ico 0 (2 * π) → k (θ + 2 * π) t = k θ t) :
    Function.Periodic (kernelRow hmeas hbd) (2 * π) := by
  intro θ
  unfold kernelRow
  refine MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_)
  rw [liftIco_eq_comp, liftIco_eq_comp]
  exact hper θ _ (circRep_mem x)

include hmeas hbd in
/-- **Kernels with Lipschitz rows.** If `k(θ, t)` is bounded, measurable in `t`, `2π`-periodic
and uniformly `K`-Lipschitz in `θ`, then its double Fourier coefficients
`k_{n m} = (θ ↦ k(θ, ·)^(n))^(m)` satisfy `∑_{n,m} m² |k_{n m}|² < ∞`. -/
theorem summable_sq_mul_kernelCoeff
    (hlip : ∀ θ θ' t, t ∈ Set.Ico 0 (2 * π) → ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|)
    (hper : ∀ θ t, t ∈ Set.Ico 0 (2 * π) → k (θ + 2 * π) t = k θ t) :
    Summable fun p : ℤ × ℤ => ((p.2 : ℝ)) ^ 2 *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2 := by
  have hL : LipschitzWith K (kernelRow hmeas hbd) := by
    refine LipschitzWith.of_dist_le_mul fun θ θ' => ?_
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_kernelRow_sub_le hmeas hbd hlip θ θ'
  have h := summable_sq_mul_fourierCoeff (fourierBasis (T := 2 * π)).orthonormal hL
    (kernelRow_periodic hmeas hbd hper)
  simp_rw [inner_kernelRow_fourierBasis, fourierCoeffOn_conj, Complex.norm_conj] at h
  have e : (fun p : ℤ × ℤ => ((p.2 : ℝ)) ^ 2 *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2) =
      (fun p : ℤ × ℤ => ((p.2 : ℝ)) ^ 2 *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) (-p.2)‖ ^ 2) ∘
        (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) := by
    funext p
    simp
  rw [e]
  exact (Equiv.summable_iff _).mpr h

end Kernel

end PolyaNeumann
