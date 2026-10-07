module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-!
# Abstract counting lemmas (Lemmas 3.4 and 3.5 of the paper)

These lemmas only use that the eigenvalue sequence `μ : ℕ → ℝ≥0∞` is nondecreasing,
together with `μ 0 = 0` and, for the reverse implication, `0 < μ j < ∞` for `j ≥ 1`.
-/

@[expose] public section

open scoped Real

namespace PolyaNeumann

variable (μ : ℕ → ENNReal)

/-- Lemma 3.4: `N(μ_j) ≤ j`. -/
lemma encard_lt_le_of_monotone (hμ : Monotone μ) (j : ℕ) :
    {i | μ i < μ j}.encard ≤ j := by
  have hsub : {i | μ i < μ j} ⊆ (Finset.range j : Set ℕ) := by
    intro i hi
    simp only [Set.mem_setOf_eq] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact absurd (hμ (not_lt.mp h)) (not_le.mpr hi)
  calc {i | μ i < μ j}.encard ≤ (Finset.range j : Set ℕ).encard := Set.encard_le_encard hsub
    _ = j := by rw [Set.encard_coe_eq_coe_finsetCard]; simp

/-- Lemma 3.4: if `m = N(E)` is finite then `E ≤ μ_m`. -/
lemma le_of_encard_eq (hμ : Monotone μ) (E : ENNReal) (m : ℕ)
    (hm : {i | μ i < E}.encard = m) : E ≤ μ m := by
  by_contra h
  push_neg at h
  have hsub : (Finset.range (m + 1) : Set ℕ) ⊆ {i | μ i < E} := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    exact lt_of_le_of_lt (hμ (by omega)) h
  have := Set.encard_le_encard hsub
  rw [Set.encard_coe_eq_coe_finsetCard, hm] at this
  simp at this
  exact absurd this (by norm_cast; omega)

/-- Lemma 3.5, first implication: the eigenvalue inequality implies the counting
inequality. -/
theorem count_of_eigen (V : ENNReal) (hV : V ≠ ⊤) (hμ : Monotone μ) (h0 : μ 0 = 0)
    (h : ∀ j : ℕ, 1 ≤ j → V * μ j < ENNReal.ofReal (4 * π * j)) (E : ℝ) (hE : 0 < E) :
    V * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (({i | μ i < ENNReal.ofReal E}.encard : ℕ∞) : ENNReal) := by
  have h4 : ENNReal.ofReal (4 * π) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have h4' : ENNReal.ofReal (4 * π) ≠ ⊤ := ENNReal.ofReal_ne_top
  by_cases htop : {i | μ i < ENNReal.ofReal E}.encard = ⊤
  · rw [htop, ENat.toENNReal_top]
    exact ENNReal.div_lt_top (ENNReal.mul_ne_top hV ENNReal.ofReal_ne_top) h4
  · obtain ⟨m, hc⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hc]
    have hm := le_of_encard_eq μ hμ _ m hc.symm
    have hm1 : 1 ≤ m := by
      by_contra hm0
      have : m = 0 := by omega
      subst this
      rw [h0] at hm
      exact absurd hm (not_le.mpr (ENNReal.ofReal_pos.mpr hE))
    have key := lt_of_le_of_lt (mul_le_mul_right hm V) (h m hm1)
    rw [ENNReal.div_lt_iff (Or.inl h4) (Or.inl h4')]
    simp only [ENat.toENNReal_coe]
    calc V * ENNReal.ofReal E < ENNReal.ofReal (4 * π * m) := key
      _ = (m : ENNReal) * ENNReal.ofReal (4 * π) := by
        rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

/-- Lemma 3.5, second implication: the counting inequality implies the eigenvalue
inequality (given `0 < μ_j < ∞` for `j ≥ 1`). -/
theorem eigen_of_count (V : ENNReal) (hμ : Monotone μ)
    (hpos : ∀ j : ℕ, 1 ≤ j → 0 < μ j) (hfin : ∀ j : ℕ, 1 ≤ j → μ j ≠ ⊤)
    (h : ∀ E : ℝ, 0 < E → V * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (({i | μ i < ENNReal.ofReal E}.encard : ℕ∞) : ENNReal))
    (j : ℕ) (hj : 1 ≤ j) : V * μ j < ENNReal.ofReal (4 * π * j) := by
  have h4 : ENNReal.ofReal (4 * π) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hE : 0 < (μ j).toReal := ENNReal.toReal_pos (hpos j hj).ne' (hfin j hj)
  have hh := h _ hE
  rw [ENNReal.ofReal_toReal (hfin j hj)] at hh
  have hc := encard_lt_le_of_monotone μ hμ j
  have hc' : (({i | μ i < μ j}.encard : ℕ∞) : ENNReal) ≤ (j : ENNReal) := by
    have := ENat.toENNReal_le.mpr hc
    simpa using this
  have := lt_of_lt_of_le hh hc'
  rw [ENNReal.div_lt_iff (Or.inl h4) (Or.inl ENNReal.ofReal_ne_top)] at this
  calc V * μ j < (j : ENNReal) * ENNReal.ofReal (4 * π) := this
    _ = ENNReal.ofReal (4 * π * j) := by
      rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

end PolyaNeumann

end
