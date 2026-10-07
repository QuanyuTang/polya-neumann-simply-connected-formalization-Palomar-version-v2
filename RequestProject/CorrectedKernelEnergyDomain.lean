module

public import RequestProject.CorrectedKernelEnergy
public import RequestProject.CorrectedKernelDomain

/-!
# Continuity in the energy of Lemmas 6.6–6.7 on a smooth domain

For the constant-speed boundary parametrization of a smooth domain, `γ'` is Lipschitz on `[0, L]`
(`IsBoundaryParam.deriv_lipschitz`), so the continuity statements of `CorrectedKernelEnergy.lean`
hold with no further assumption on the curve:

* `tendsto_correctedKernelCoeff_energy_smoothDomain`: `r_E → r_{E₀}` in the `H^{1+δ}` seminorms
  in both variables;
* `tendsto_correctedRemainder_energy_smoothDomain`: the normalized remainder
  `Λ^{1/2} R_E Λ^{1/2} : H^t → H^{t+δ}` depends continuously on `E` in operator norm.

Both assume `c_{E₀} ≠ 0`, as the regularity statements of Lemma 6.6 do.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter Topology

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}

/-- **Lemma 6.6 (continuity in the energy) on a smooth domain.** For the constant-speed boundary
parametrization of a smooth domain, transports `W_E` with `c_{E₀} ≠ 0` and `0 ≤ δ < 1/2`, the
double Fourier coefficients of the corrected kernels satisfy
`∑_{n,m} |m|^{2+2δ} |r_{n m}(E) - r_{n m}(E₀)|² → 0` and
`∑_{n,m} |n|^{2+2δ} |r_{n m}(E) - r_{n m}(E₀)|² → 0` as `E → E₀`, the series converging for `E`
near `E₀`. -/
theorem tendsto_correctedKernelCoeff_energy_smoothDomain (hS : IsSmoothDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    ((∀ᶠ E in 𝓝 E₀, Summable fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2) ∧
    Tendsto (fun E => ∑' p : ℤ × ℤ, |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2)
      (𝓝 E₀) (𝓝 0)) ∧
    ((∀ᶠ E in 𝓝 E₀, Summable fun p : ℤ × ℤ => |(p.1 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2) ∧
    Tendsto (fun E => ∑' p : ℤ × ℤ, |(p.1 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2)
      (𝓝 E₀) (𝓝 0)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨K', hK'⟩ := hγ.deriv_lipschitz hS
  exact ⟨tendsto_correctedKernelCoeff_energy hK hK' hWs E₀ hc hδ hδ',
    tendsto_correctedKernelCoeff_energy_snd hK hK' hWs E₀ hc hδ hδ'⟩

/-- **Lemma 6.7 (kernel part, continuity in the energy) on a smooth domain.** For the
constant-speed boundary parametrization of a smooth domain, transports `W_E` with `c_{E₀} ≠ 0`,
`0 ≤ t ≤ 1/2` and `0 ≤ δ < 1/2`, the Hilbert–Schmidt operators `Λ^{1/2} R_E Λ^{1/2} : H^t → H^{t+δ}`
are defined for `E` near `E₀` and converge to the one at `E₀` in operator norm. -/
theorem tendsto_correctedRemainder_energy_smoothDomain (hS : IsSmoothDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) {δ s : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    (∀ᶠ E in 𝓝 E₀, Summable fun p => ‖correctedRemainderMatrix (Ws E) δ s p‖ ^ 2) ∧
    ∀ η, 0 < η → ∀ᶠ E in 𝓝 E₀,
      ∀ hE : Summable (fun p => ‖correctedRemainderMatrix (Ws E) δ s p‖ ^ 2),
        ‖hsMatrixOp (correctedRemainderMatrix (Ws E) δ s) hE -
          hsMatrixOp (correctedRemainderMatrix (Ws E₀) δ s)
            (summable_correctedRemainderMatrix_smoothDomain hS hγ (hWs E₀) hc hδ hδ' hs0 hs1)‖ <
          η := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨K', hK'⟩ := hγ.deriv_lipschitz hS
  exact tendsto_correctedRemainder_energy hK hK' hWs E₀ hc hδ hδ' hs0 hs1

end PolyaNeumann
