module

public import RequestProject.Rellich
public import RequestProject.Finite

/-!
# Neumann eigenspaces

The Neumann eigenspace `ker(A_N - E)` of a domain `Ω` is the space of `u ∈ H¹(Ω)` satisfying the
weak Neumann eigenvalue equation `∫_Ω ∇v̄ · ∇u = E ∫_Ω v̄ u` for every `v ∈ H¹(Ω)`
(`neumannEigenspace`).

For a bounded Lipschitz domain it is finite-dimensional (`finiteDimensional_neumannEigenspace`,
the finiteness statement of Lemma 3.3): its elements satisfy `‖∇u‖² = E ‖u‖²`, so a bounded
sequence in it is bounded in `H¹(Ω)`, and Rellich compactness rules out the separated
sequences that an infinite-dimensional normed space contains (Riesz's lemma).
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-- The Neumann eigenspace `ker(A_N - E)`: the `u ∈ H¹(Ω)`, with weak gradient `g`, such that
`∑ᵢ ⟨hᵢ, gᵢ⟩ = E ⟨v, u⟩` for every `v ∈ H¹(Ω)` with weak gradient `h` (the weak form of
`-Δu = E u` with zero Neumann data). -/
def neumannEigenspace (Ω : Set ℂ) (E : ℝ) : Submodule ℂ (L2 Ω) where
  carrier := {u | ∃ g, IsWeakGradient Ω u g ∧ ∀ v h, IsWeakGradient Ω v h →
      ∑ i, inner ℂ (h i) (g i) = (E : ℂ) * inner ℂ v u}
  zero_mem' := ⟨0, isWeakGradient_zero, fun v h _ => by simp⟩
  add_mem' := by
    rintro u w ⟨g, hg, hu⟩ ⟨k, hk, hw⟩
    refine ⟨g + k, hg.add hk, fun v h hv => ?_⟩
    simp only [Pi.add_apply, inner_add_right, Finset.sum_add_distrib, hu v h hv, hw v h hv,
      mul_add]
  smul_mem' := by
    rintro c u ⟨g, hg, hu⟩
    refine ⟨c • g, hg.smul c, fun v h hv => ?_⟩
    simp only [Pi.smul_apply, inner_smul_right, ← Finset.mul_sum, hu v h hv]
    ring

/-- Eigenfunctions satisfy `‖∂ᵢ u‖ ≤ √|E| ‖u‖`. -/
lemma norm_grad_le_of_mem_neumannEigenspace {Ω : Set ℂ} {E : ℝ} {u : L2 Ω}
    {g : Fin 2 → L2 Ω} (hg : IsWeakGradient Ω u g)
    (hu : ∀ v h, IsWeakGradient Ω v h → ∑ i, inner ℂ (h i) (g i) = (E : ℂ) * inner ℂ v u)
    (i : Fin 2) : ‖g i‖ ≤ Real.sqrt |E| * ‖u‖ := by
  have h := hu u g hg
  simp only [inner_self_eq_norm_sq_to_K, Fin.sum_univ_two] at h
  have h' : ‖g 0‖ ^ 2 + ‖g 1‖ ^ 2 = E * ‖u‖ ^ 2 :=
    Complex.ofReal_injective (by push_cast; exact h)
  have hsq : ‖g i‖ ^ 2 ≤ (Real.sqrt |E| * ‖u‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg E)]
    have hE : E * ‖u‖ ^ 2 ≤ |E| * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self E) (by positivity)
    fin_cases i <;> simp <;> nlinarith [sq_nonneg ‖g 0‖, sq_nonneg ‖g 1‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- Lemma 3.3 (finite multiplicity): on a bounded Lipschitz domain every Neumann eigenspace is
finite-dimensional. -/
theorem finiteDimensional_neumannEigenspace {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (E : ℝ) : FiniteDimensional ℂ (neumannEigenspace Ω E) := by
  by_contra hfin
  obtain ⟨R, f, hR, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
  have hmem : ∀ n, ∃ g, IsWeakGradient Ω (f n : L2 Ω) g ∧ ∀ v h, IsWeakGradient Ω v h →
      ∑ i, inner ℂ (h i) (g i) = (E : ℂ) * inner ℂ v (f n : L2 Ω) := fun n => (f n).2
  choose g hg hgE using hmem
  have hu : ∀ n, ‖(f n : L2 Ω)‖ ≤ max R (Real.sqrt |E| * R) := fun n =>
    le_max_of_le_left (hfR n)
  have hgC : ∀ n i, ‖g n i‖ ≤ max R (Real.sqrt |E| * R) := fun n i =>
    le_max_of_le_right ((norm_grad_le_of_mem_neumannEigenspace (hg n) (hgE n) i).trans
      (mul_le_mul_of_nonneg_left (hfR n) (Real.sqrt_nonneg _)))
  obtain ⟨φ, hφ, v, hv⟩ := rellich_compact hb hL (fun n => (f n : L2 Ω)) g hg _ hu hgC
  have hcauchy := hv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy 1 one_pos
  have h1 := hN (N + 1) (by omega) N le_rfl
  have h2 := hsep (hφ.injective.ne (by omega : N + 1 ≠ N))
  rw [dist_eq_norm] at h1
  simp only [Function.comp] at h1
  have h1' : ‖f (φ (N + 1)) - f (φ N)‖ < 1 := h1
  linarith

end PolyaNeumann
