module

public import RequestProject.FractionalRows
public import RequestProject.KernelRows

/-!
# `H^{1+δ}` regularity of kernels in the first variable (Lemma 6.6, fractional part)

Let `k(θ, t)` be a bounded kernel, measurable in `t`, `2π`-periodic and uniformly Lipschitz in
`θ`. Suppose that its second differences in `θ` satisfy, uniformly in `t ∈ [0, 2π)`,

  `|k(θ+2h, t) - 2k(θ+h, t) + k(θ, t)| ≤ A h²`  for `θ ∈ [0, 2π - 2h]`,

(this holds when `θ ↦ k(θ, t)` has an `A`-Lipschitz derivative on `[0, 2π]`, the derivative being
allowed to jump at the cut). Then the double Fourier coefficients
`k_{n m} = (θ ↦ (t ↦ k(θ, t))^(n))^(m)` satisfy

  `∑_{n, m} |m|^{2+2δ} |k_{n m}|² < ∞`  for every `0 ≤ δ < 1/2`
  (`summable_kernelCoeff_three_halves`).

This is the fractional analogue of `summable_sq_mul_kernelCoeff`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory
open scoped InnerProductSpace ComplexConjugate

local instance factTwoPiPosFK : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

section Kernel

variable {k : ℝ → ℝ → ℂ} {M : ℝ} (hmeas : ∀ θ, Measurable (k θ)) (hbd : ∀ θ t, ‖k θ t‖ ≤ M)

include hmeas hbd in
/-- A pointwise bound on second differences of the kernel bounds the second difference of the
rows in `L²(𝕋)`. -/
lemma norm_secondDiff_kernelRow_le {h θ D : ℝ} (hD : 0 ≤ D)
    (hpt : ∀ t ∈ Set.Ico 0 (2 * π), ‖secondDiff (fun θ => k θ t) h θ‖ ≤ D) :
    ‖secondDiff (kernelRow hmeas hbd) h θ‖ ≤ D := by
  unfold secondDiff kernelRow
  rw [← MemLp.toLp_sub, ← MemLp.toLp_sub, ← MemLp.toLp_sub]
  set hm := fun θ => memLp_liftIco_two_pi (hmeas θ) (hbd θ)
  have h := Lp.norm_le_of_ae_bound (μ := (@AddCircle.haarAddCircle (2 * π) _)) (p := 2)
    (f := MemLp.toLp _ (((hm (θ + 2 * h)).sub (hm (θ + h))).sub ((hm (θ + h)).sub (hm θ))))
    (C := D) hD ?_
  · have h1 : measureUnivNNReal (@AddCircle.haarAddCircle (2 * π) _) = 1 := by
      simp [measureUnivNNReal]
    simpa [h1] using h
  · filter_upwards [MemLp.coeFn_toLp
      (((hm (θ + 2 * h)).sub (hm (θ + h))).sub ((hm (θ + h)).sub (hm θ)))] with x hx
    rw [hx]
    simp only [Pi.sub_apply, liftIco_eq_comp]
    exact hpt _ (circRep_mem x)

include hmeas hbd in
/-- **`H^{1+δ}` regularity of a kernel in the first variable.** Let `k(θ, t)` be bounded,
measurable in `t`, `2π`-periodic and uniformly `K`-Lipschitz in `θ` (for `t ∈ [0, 2π)`), and
suppose that for `0 < h ≤ π/2`, `θ ∈ [0, 2π - 2h]` and `t ∈ [0, 2π)`,
`|k(θ+2h, t) - 2k(θ+h, t) + k(θ, t)| ≤ A h²`. Then the double Fourier coefficients satisfy
`∑_{n,m} |m|^{2+2δ} |k_{n m}|² < ∞` for every `0 ≤ δ < 1/2`. -/
theorem summable_kernelCoeff_three_halves {K : NNReal} {A : ℝ} (hA : 0 ≤ A)
    (hlip : ∀ θ θ' t, t ∈ Set.Ico 0 (2 * π) → ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|)
    (hper : ∀ θ t, t ∈ Set.Ico 0 (2 * π) → k (θ + 2 * π) t = k θ t)
    (hsecond : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h),
      ∀ t ∈ Set.Ico 0 (2 * π), ‖secondDiff (fun θ => k θ t) h θ‖ ≤ A * h ^ 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    Summable fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2 := by
  have hL : LipschitzWith K (kernelRow hmeas hbd) := by
    refine LipschitzWith.of_dist_le_mul fun θ θ' => ?_
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_kernelRow_sub_le hmeas hbd hlip θ θ'
  have hbad : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ,
      ‖secondDiff (kernelRow hmeas hbd) h θ‖ ≤ (2 * K) * h := by
    intro h hh _ θ
    have e1 := norm_kernelRow_sub_le hmeas hbd hlip (θ + 2 * h) (θ + h)
    have e2 := norm_kernelRow_sub_le hmeas hbd hlip (θ + h) θ
    rw [show θ + 2 * h - (θ + h) = h by ring, abs_of_pos hh] at e1
    rw [show θ + h - θ = h by ring, abs_of_pos hh] at e2
    unfold secondDiff
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hgood : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h),
      ‖secondDiff (kernelRow hmeas hbd) h θ‖ ≤ A * h ^ 2 := fun h h0 h1 θ hθ =>
    norm_secondDiff_kernelRow_le hmeas hbd (by positivity) (hsecond h h0 h1 θ hθ)
  have h := summable_fourierCoeff_rows_three_halves (fourierBasis (T := 2 * π)).orthonormal
    hL.continuous (kernelRow_periodic hmeas hbd hper) hgood hbad hδ hδ'
  simp_rw [inner_kernelRow_fourierBasis, fourierCoeffOn_conj, Complex.norm_conj] at h
  have e : (fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2) =
      (fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) (-p.2)‖ ^ 2) ∘
        (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) := by
    funext p
    simp
  rw [e]
  exact (Equiv.summable_iff _).mpr h

end Kernel

end PolyaNeumann
