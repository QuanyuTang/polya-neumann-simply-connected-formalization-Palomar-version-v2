module

public import RequestProject.RellichCompact
public import RequestProject.LipschitzCover

/-!
# Rellich compactness and closedness of the weak gradient

* `rellich_compact`: the Rellich–Kondrachov compactness theorem for bounded Lipschitz domains
  (part of External theorem E2 of the paper), stated for sequences: a sequence bounded in
  `H¹(Ω)` has an `L²(Ω)`-convergent subsequence. It is proved from the cover of `Ω` by
  shiftable pieces (`lipschitz_cover`) and the Kolmogorov–Riesz argument `rellich_of_cover`.
* `isWeakGradient_of_tendsto`: weak gradients are closed under `L²` limits.
* `isWeakGradient_smul`: weak gradients are compatible with scalar multiplication.
* `tendsto_integral_mul`: `u ↦ ∫_Ω u ψ` is continuous on `L²(Ω)` for `ψ ∈ L²(Ω)`.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-- **External theorem E2 (Rellich–Kondrachov compactness)**: on a bounded Lipschitz domain,
every sequence bounded in `H¹(Ω)` has a subsequence converging in `L²(Ω)`. -/
theorem rellich_compact {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (u : ℕ → L2 Ω) (g : ℕ → Fin 2 → L2 Ω) (hg : ∀ n, IsWeakGradient Ω (u n) (g n)) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) (hgC : ∀ n i, ‖g n i‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : L2 Ω, Tendsto (u ∘ φ) atTop (𝓝 v) := by
  obtain ⟨m, W, hWo, hWΩ, hcov, hsh⟩ := lipschitz_cover hb hL
  exact rellich_of_cover hL.1.1 hb W hWo hWΩ hcov hsh u g hg C hu hgC

/-- Integration against a fixed function whose conjugate is in `L²(Ω)` is continuous on
`L²(Ω)`. -/
lemma tendsto_integral_mul {Ω : Set ℂ} {ψ : ℂ → ℂ}
    (hψ : MemLp (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω))
    {f : ℕ → L2 Ω} {F : L2 Ω} (hf : Tendsto f atTop (𝓝 F)) :
    Tendsto (fun n => ∫ w in Ω, f n w * ψ w) atTop (𝓝 (∫ w in Ω, F w * ψ w)) := by
  set Ψ : L2 Ω := hψ.toLp _
  have key : ∀ G : L2 Ω, ∫ w in Ω, G w * ψ w = inner ℂ Ψ G := by
    intro G
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with w hw
    simp only [Ψ, hw, RCLike.inner_apply, Complex.conj_conj]
  simp_rw [key]
  exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp hf

/-- Weak gradients pass to `L²` limits. -/
lemma isWeakGradient_of_tendsto {Ω : Set ℂ} {u : ℕ → L2 Ω} {g : ℕ → Fin 2 → L2 Ω}
    {U : L2 Ω} {G : Fin 2 → L2 Ω} (hg : ∀ n, IsWeakGradient Ω (u n) (g n))
    (hu : Tendsto u atTop (𝓝 U)) (hG : ∀ i, Tendsto (fun n => g n i) atTop (𝓝 (G i))) :
    IsWeakGradient Ω U G := by
  intro φ hφ i
  have hmem : ∀ ψ : ℂ → ℂ, Continuous ψ → HasCompactSupport ψ →
      MemLp (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω) := fun ψ hc hs =>
    ((Complex.continuous_conj.comp hc).memLp_of_hasCompactSupport
      (hs.comp_left (map_zero _))).restrict Ω
  have hd : Continuous fun w => fderiv ℝ φ w (coordDir i) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport fun w => fderiv ℝ φ w (coordDir i) :=
    (hφ.2.1.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T (coordDir i)) rfl
  have h1 := tendsto_integral_mul (hmem _ hd hds) hu
  have h2 := (tendsto_integral_mul (hmem _ hφ.1.continuous hφ.2.1) (hG i)).neg
  refine tendsto_nhds_unique h1 ?_
  exact h2.congr fun n => (hg n φ hφ i).symm

/-- Weak gradients scale: if `∇u = g` then `∇(c u) = c g`. -/
lemma isWeakGradient_smul {Ω : Set ℂ} {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) (c : ℂ) : IsWeakGradient Ω (c • u) (c • g) := by
  intro φ hφ i
  have h := hg φ hφ i
  have e1 : ∫ w in Ω, (c • u : L2 Ω) w * fderiv ℝ φ w (coordDir i) =
      c * ∫ w in Ω, u w * fderiv ℝ φ w (coordDir i) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c u] with w hw
    simp [hw, mul_assoc]
  have e2 : ∫ w in Ω, (c • g) i w * φ w = c * ∫ w in Ω, g i w * φ w := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c (g i)] with w hw
    simp [Pi.smul_apply, hw, mul_assoc]
  rw [e1, e2, h, mul_neg]

end PolyaNeumann

end
