module

public import RequestProject.CorrectedKernelSymm
public import RequestProject.BoundaryRegularity

/-!
# Lemma 6.6 for the boundary parametrization of a smooth domain

For a smooth domain and its constant-speed boundary parametrization, `γ'` is Lipschitz on
`[0, L]` (`IsBoundaryParam.deriv_lipschitz`), so the fractional regularity of the corrected
kernel holds without any further assumption on the curve: for `0 ≤ δ < 1/2`,

* `∑_{n,m} (|m|^{2+2δ} + |n|^{2+2δ}) |r_{n m}|² < ∞` (`r_E ∈ H^{1+δ}` in both variables;
  `summable_correctedKernelCoeff_smoothDomain`);
* the normalized remainder `Λ^{1/2} R_E Λ^{1/2} : H^t → H^{t+δ}` (`0 ≤ t ≤ 1/2`) is a compact
  Hilbert–Schmidt operator (`isCompactOperator_correctedRemainder_smoothDomain`).
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

/-- **Lemma 6.6 (fractional regularity) on a smooth domain.** For the constant-speed boundary
parametrization of a smooth domain, a transport `W` at energy `E` with `c_E ≠ 0` and
`0 ≤ δ < 1/2`, the double Fourier coefficients `r_{n m}` of the corrected kernel (`n` the
frequency in `t`, `m` in `θ`) satisfy `∑ |m|^{2+2δ} |r_{n m}|² < ∞` and
`∑ |n|^{2+2δ} |r_{n m}|² < ∞`. -/
theorem summable_correctedKernelCoeff_smoothDomain (hS : IsSmoothDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    (Summable fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) * ‖fourierCoeffOn two_pi_pos
      (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) p.1) p.2‖ ^ 2) ∧
    (Summable fun p : ℤ × ℤ => |(p.1 : ℝ)| ^ (2 + 2 * δ) * ‖fourierCoeffOn two_pi_pos
      (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) p.1) p.2‖ ^ 2) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨K', hK'⟩ := hγ.deriv_lipschitz hS
  exact ⟨summable_rpow_mul_correctedKernelCoeff hK hK' hW hc hδ hδ',
    summable_rpow_mul_correctedKernelCoeff_snd hK hK' hW hc hδ hδ'⟩

/-- The normalized remainder matrix is square summable on a smooth domain. -/
theorem summable_correctedRemainderMatrix_smoothDomain (hS : IsSmoothDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {δ s : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Summable fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨K', hK'⟩ := hγ.deriv_lipschitz hS
  exact summable_correctedRemainderMatrix hK hK' hW hc hδ hδ' hs0 hs1

/-- **Lemma 6.7 (kernel part) on a smooth domain.** For `0 ≤ t ≤ 1/2` and `0 ≤ δ < 1/2`, the
normalized corrected-kernel remainder `Λ^{1/2} R_E Λ^{1/2} : H^t → H^{t+δ}`, written as the
operator on `ℓ²(ℤ)` with matrix `λ_m^{1/2+t+δ} λ_n^{1/2-t} r̂_E(m, n)`, is compact. -/
theorem isCompactOperator_correctedRemainder_smoothDomain (hS : IsSmoothDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {δ s : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    IsCompactOperator (hsMatrixOp (correctedRemainderMatrix W δ s)
      (summable_correctedRemainderMatrix_smoothDomain hS hγ hW hc hδ hδ' hs0 hs1)) :=
  isCompactOperator_hsMatrixOp _ _

end PolyaNeumann
