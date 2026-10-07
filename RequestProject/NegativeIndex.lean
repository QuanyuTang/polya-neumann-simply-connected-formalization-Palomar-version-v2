module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Tactic

/-!
# Negative index of a Hermitian form (Definition 1.6) and the index count of Lemma 8.6

Definition 1.6 of the paper: the negative index of a Hermitian form is the supremum of the
dimensions of subspaces on which the form is strictly negative. Here the form is
`g ↦ Re ⟨g, A g⟩` for a bounded operator `A` on a complex inner product space (for
self-adjoint `A` this is `⟨g, A g⟩`), and the supremum is taken in `ℕ∞` over
finite-dimensional subspaces (`negIndex`).

Lemma 8.6 of the paper (Negative index at small energy) ends with the following argument:
`𝒜_E = C^sc_E + a_E⁻¹ b_E ⟨b_E, ·⟩` with `C^sc_E ≥ 0` and `a_E = ⟨q_E, 𝒜_E q_E⟩ < 0`. Any
subspace of dimension at least two contains a nonzero vector orthogonal to `b_E`, on which the
form is nonnegative, so `ind₋ 𝒜_E ≤ 1`; and `q_E` spans a negative line, so `ind₋ 𝒜_E = 1`.
This is `negIndex_eq_one_of_schur` below; the nonnegativity `C^sc_E ≥ 0` (Lemmas 8.4–8.5) is a
hypothesis.

We also record the elementary operator identity used in Lemma 8.5 (A basis decomposition at
small energy): if `⟨φ₀, ζ - φ₀⟩ = 0` and `N = (ζ - φ₀) ⟨φ₀, ·⟩`, then `N² = 0` and
`(I + N)⁻¹ = I - N`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open InnerProductSpace ContinuousLinearMap Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `A` is strictly negative on the subspace `V`: `Re ⟨v, A v⟩ < 0` for all nonzero `v ∈ V`. -/
def IsNegativeOn (A : H →L[ℂ] H) (V : Submodule ℂ H) : Prop :=
  ∀ v ∈ V, v ≠ 0 → (⟪v, A v⟫_ℂ).re < 0

/-- **Definition 1.6 (negative index).** The supremum of the dimensions of (finite-dimensional)
subspaces on which the form `g ↦ Re ⟨g, A g⟩` is strictly negative. -/
noncomputable def negIndex (A : H →L[ℂ] H) : ℕ∞ :=
  ⨆ (V : Submodule ℂ H) (_ : FiniteDimensional ℂ V) (_ : IsNegativeOn A V),
    (Module.finrank ℂ V : ℕ∞)

/-- If the form of `A` is nonnegative on the orthogonal complement of a single vector `b`, then
`A` has negative index at most one. -/
theorem negIndex_le_one_of_nonneg_on_ker (A : H →L[ℂ] H) (b : H)
    (hA : ∀ g : H, ⟪b, g⟫_ℂ = 0 → 0 ≤ (⟪g, A g⟫_ℂ).re) : negIndex A ≤ 1 := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hneg => ?_
  norm_cast
  by_contra hlt
  push_neg at hlt
  let f : V →ₗ[ℂ] ℂ := (innerₛₗ ℂ b).comp V.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank ℂ (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hfv : ⟪b, (v : H)⟫_ℂ = 0 := by simpa [f] using hv
  have hv0' : (v : H) ≠ 0 := by simpa using hv0
  have := hneg v v.2 hv0'
  have := hA v hfv
  linarith

/-- A vector with `Re ⟨q, A q⟩ < 0` spans a negative line, so `ind₋ A ≥ 1`. -/
theorem one_le_negIndex_of_neg (A : H →L[ℂ] H) (q : H) (hq : (⟪q, A q⟫_ℂ).re < 0) :
    1 ≤ negIndex A := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hneg : IsNegativeOn A (ℂ ∙ q) := by
    intro v hv hv0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have hc : c ≠ 0 := by rintro rfl; simp at hv0
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul']
    have : (0:ℝ) < ‖c‖ ^ 2 := by positivity
    rw [show ((‖c‖ : ℂ) ^ 2) = ((‖c‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    nlinarith
  have h := le_iSup₂_of_le (f := fun (V : Submodule ℂ H) (_ : FiniteDimensional ℂ V) =>
    ⨆ (_ : IsNegativeOn A V), (Module.finrank ℂ V : ℕ∞)) (ℂ ∙ q) inferInstance
    (le_iSup_of_le hneg le_rfl)
  rw [finrank_span_singleton hq0] at h
  unfold negIndex
  exact_mod_cast h

/-- **Lemma 8.6 (negative index at small energy), index count.** Let `q` be a vector with
`a = ⟨q, A q⟩` real and negative, put `b = A q`, and suppose the Schur complement
`C^sc = A - a⁻¹ b ⟨b, ·⟩` is nonnegative: `Re ⟨g, A g⟩ - a⁻¹ |⟨b, g⟩|² ≥ 0` for all `g`. Then
`ind₋ A = 1`. -/
theorem negIndex_eq_one_of_schur (A : H →L[ℂ] H) (q : H) (a : ℝ) (ha : a < 0)
    (hqa : ⟪q, A q⟫_ℂ = a)
    (hC : ∀ g : H, 0 ≤ (⟪g, A g⟫_ℂ).re - a⁻¹ * ‖⟪A q, g⟫_ℂ‖ ^ 2) :
    negIndex A = 1 := by
  refine le_antisymm (negIndex_le_one_of_nonneg_on_ker A (A q) fun g hg => ?_)
    (one_le_negIndex_of_neg A q (by rw [hqa]; simpa using ha))
  simpa [hg] using hC g

/-- **Lemma 8.5, the limit operator.** If `⟨φ₀, ζ - φ₀⟩ = 0` and `N = (ζ - φ₀) ⟨φ₀, ·⟩`, then
`N² = 0` and `I + N` is invertible with inverse `I - N`. -/
theorem rankOne_sq_eq_zero_and_inverse (φ₀ ζ : H) (h : ⟪φ₀, ζ - φ₀⟫_ℂ = 0) :
    let N : H →L[ℂ] H := (innerSL ℂ φ₀).smulRight (ζ - φ₀)
    N ∘L N = 0 ∧ (1 + N) * (1 - N) = 1 ∧ (1 - N) * (1 + N) = 1 := by
  intro N
  have hN : N ∘L N = 0 := by
    ext x
    simp [N, h]
  have hN' : N * N = 0 := hN
  refine ⟨hN, ?_, ?_⟩
  · rw [add_mul, mul_sub, mul_sub, hN']; simp only [one_mul, mul_one]; abel
  · rw [sub_mul, mul_add, mul_add, hN']; simp only [one_mul, mul_one]; abel

end PolyaNeumann
