module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic

/-!
# Compact perturbation coercivity (Lemma 7.6)

Let `Z`, `Y` be complex Hilbert spaces, `H = α I + C` a bounded operator on `Z` with `α > 0` and
`C` compact, and `S : Z → Y` a bounded injective operator. Lemma 7.6 of the paper states that
there are `A > 0`, `ε > 0` with

`Re ⟨z, H z⟩ + A ‖S z‖² ≥ ε ‖z‖²` for all `z ∈ Z`,

and that the same `A` and the bound `ε / 2` work for small operator-norm perturbations of `H`
and `S`.

The paper assumes `H` self-adjoint, so that `⟨z, H z⟩` is real; stated with the real part,
self-adjointness is not needed. The paper's proof extracts a weakly convergent subsequence; the
proof here avoids weak compactness: a bounded sequence with `S z_n → 0` is weakly null because
`ran S^*` is dense (`S` is injective), and a compact operator maps a weakly null bounded
sequence to a norm-null one.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open InnerProductSpace ContinuousLinearMap Filter Topology
open scoped InnerProductSpace

variable {Z Y : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

omit [CompleteSpace Z] in
/-- A bounded sequence whose inner products with every vector of a dense set tend to zero
is weakly null. -/
lemma tendsto_inner_of_dense {u : ℕ → Z} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) {D : Set Z}
    (hD : Dense D) (h : ∀ y ∈ D, Tendsto (fun n => ⟪y, u n⟫_ℂ) atTop (𝓝 0)) (y : Z) :
    Tendsto (fun n => ⟪y, u n⟫_ℂ) atTop (𝓝 0) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans (hu 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.1 hD y (ε / (2 * (R + 1))) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h d hdD) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [dist_zero_right] at h1 ⊢
  rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hd
  have h2 : ‖⟪y - d, u n⟫_ℂ‖ ≤ ‖y - d‖ * R :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg _))
  have h3 : ‖y - d‖ * R ≤ ε / (2 * (R + 1)) * R := mul_le_mul_of_nonneg_right hd.le hR
  have h4 : ε / (2 * (R + 1)) * R ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : ⟪y, u n⟫_ℂ = ⟪y - d, u n⟫_ℂ + ⟪d, u n⟫_ℂ := by rw [inner_sub_left]; ring
  rw [this]
  calc _ ≤ ‖⟪y - d, u n⟫_ℂ‖ + ‖⟪d, u n⟫_ℂ‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- A compact operator maps a bounded weakly null sequence to a norm-null sequence. -/
lemma IsCompactOperator.tendsto_of_weak {C : Z →L[ℂ] Y} (hC : IsCompactOperator C)
    {u : ℕ → Z} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R)
    (h : ∀ y, Tendsto (fun n => ⟪y, u n⟫_ℂ) atTop (𝓝 0)) :
    Tendsto (fun n => C (u n)) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hK := hC.isCompact_closure_image_closedBall R
  obtain ⟨a, -, φ, hφ, ha⟩ := hK.tendsto_subseq (x := fun n => C (u (ns n)))
    (fun n => subset_closure ⟨u (ns n), by simpa using hu (ns n), rfl⟩)
  have hsub : Tendsto (ns ∘ φ) atTop atTop := hns.comp hφ.tendsto_atTop
  have ha0 : a = 0 := by
    have hy : ∀ y, ⟪y, a⟫_ℂ = 0 := by
      intro y
      have h1 := (((innerSL ℂ y).continuous.tendsto a).comp ha)
      have h2 := (h (adjoint C y)).comp hsub
      refine tendsto_nhds_unique h1 ?_
      convert h2 using 1
      ext n
      simp [adjoint_inner_left]
    simpa using hy a
  exact ⟨φ, ha0 ▸ ha⟩

/-- For an injective `S`, a bounded sequence with `S u_n → 0` is weakly null: `ran S^*` is
dense since its orthogonal complement is `ker S = 0`. -/
lemma tendsto_inner_of_injective {S : Z →L[ℂ] Y} (hS : Function.Injective S)
    {u : ℕ → Z} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) (h : Tendsto (fun n => S (u n)) atTop (𝓝 0))
    (y : Z) : Tendsto (fun n => ⟪y, u n⟫_ℂ) atTop (𝓝 0) := by
  apply tendsto_inner_of_dense hu (D := LinearMap.range (adjoint S).toLinearMap)
  · have : (LinearMap.range (adjoint S).toLinearMap).topologicalClosure = ⊤ := by
      rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
      intro v hv
      have h0 := (Submodule.mem_orthogonal _ _).1 hv (adjoint S (S v)) ⟨S v, rfl⟩
      rw [adjoint_inner_left, inner_self_eq_zero] at h0
      exact hS (by rw [h0, map_zero])
    exact Submodule.dense_iff_topologicalClosure_eq_top.2 this
  · rintro _ ⟨x, rfl⟩
    simp only [ContinuousLinearMap.coe_coe, adjoint_inner_left]
    have := ((innerSL ℂ x).continuous.tendsto 0).comp h
    simpa [Function.comp_def] using this

/-- The coercivity inequality of Lemma 7.6 (without the perturbation statement). -/
lemma exists_coercive (α : ℝ) (hα : 0 < α) (C : Z →L[ℂ] Z) (hC : IsCompactOperator C)
    (S : Z →L[ℂ] Y) (hS : Function.Injective S) :
    ∃ A > 0, ∃ ε > 0, ∀ z : Z,
      ε * ‖z‖ ^ 2 ≤ (⟪z, ((α : ℂ) • ContinuousLinearMap.id ℂ Z + C) z⟫_ℂ).re + A * ‖S z‖ ^ 2 := by
  set H := (α : ℂ) • ContinuousLinearMap.id ℂ Z + C with hHdef
  by_contra hcon
  push_neg at hcon
  choose z hz using fun n : ℕ => hcon (n + 1) (by positivity) (1 / (n + 1)) (by positivity)
  have hz0 : ∀ n, z n ≠ 0 := by
    intro n h0
    have := hz n
    simp [h0] at this
  have hscale : ∀ (t : ℝ) (v : Z), (⟪(t : ℂ) • v, H ((t : ℂ) • v)⟫_ℂ).re = t ^ 2 * (⟪v, H v⟫_ℂ).re ∧
      ‖S ((t : ℂ) • v)‖ ^ 2 = t ^ 2 * ‖S v‖ ^ 2 := by
    intro t v
    constructor
    · rw [map_smul, inner_smul_left, inner_smul_right]
      simp [Complex.conj_ofReal]
      ring
    · rw [map_smul, norm_smul, mul_pow]
      simp
  set w : ℕ → Z := fun n => ((‖z n‖⁻¹ : ℝ) : ℂ) • z n with hw_def
  have hwn : ∀ n, ‖w n‖ = 1 := by
    intro n
    simp [hw_def, norm_smul, hz0 n]
  have hw : ∀ n, (⟪w n, H (w n)⟫_ℂ).re + (n + 1) * ‖S (w n)‖ ^ 2 < 1 / (n + 1) := by
    intro n
    obtain ⟨h1, h2⟩ := hscale (‖z n‖⁻¹) (z n)
    simp only [hw_def]
    rw [h1, h2]
    have hpos : 0 < ‖z n‖⁻¹ ^ 2 := by have := norm_pos_iff.2 (hz0 n); positivity
    have := mul_lt_mul_of_pos_left (hz n) hpos
    have e : ‖z n‖⁻¹ ^ 2 * (1 / (n + 1) * ‖z n‖ ^ 2) = 1 / (n + 1) := by
      have := norm_pos_iff.2 (hz0 n); field_simp
    nlinarith
  have hHb : ∀ n, -‖H‖ ≤ (⟪w n, H (w n)⟫_ℂ).re := by
    intro n
    have h1 : |(⟪w n, H (w n)⟫_ℂ).re| ≤ ‖H‖ :=
      calc |(⟪w n, H (w n)⟫_ℂ).re| ≤ ‖⟪w n, H (w n)⟫_ℂ‖ := Complex.abs_re_le_norm _
        _ ≤ ‖w n‖ * ‖H (w n)‖ := norm_inner_le_norm _ _
        _ ≤ ‖w n‖ * (‖H‖ * ‖w n‖) := by gcongr; exact H.le_opNorm _
        _ = ‖H‖ := by rw [hwn]; ring
    linarith [neg_abs_le (⟪w n, H (w n)⟫_ℂ).re]
  have h1n : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hSw : Tendsto (fun n => S (w n)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n => ‖S (w n)‖ ^ 2) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => by positivity)
        (g := fun n : ℕ => (1 + ‖H‖) * (1 / ((n : ℝ) + 1)))
      · intro n
        have := hw n
        have := hHb n
        have hn : 0 < (n : ℝ) + 1 := by positivity
        have : 1 / ((n:ℝ) + 1) ≤ 1 := by rw [div_le_one hn]; linarith
        rw [mul_one_div, le_div_iff₀ hn]
        nlinarith
      · simpa using h1n.const_mul (1 + ‖H‖)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  have hweak := tendsto_inner_of_injective hS (fun n => (hwn n).le) hSw
  have hCw := IsCompactOperator.tendsto_of_weak hC (fun n => (hwn n).le) hweak
  have hre : Tendsto (fun n => (⟪w n, C (w n)⟫_ℂ).re) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hCw ⊢
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hCw
    calc ‖(⟪w n, C (w n)⟫_ℂ).re‖ ≤ ‖⟪w n, C (w n)⟫_ℂ‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ ≤ ‖w n‖ * ‖C (w n)‖ := norm_inner_le_norm _ _
      _ = ‖C (w n)‖ := by rw [hwn, one_mul]
  have hHw : ∀ n, (⟪w n, H (w n)⟫_ℂ).re = α + (⟪w n, C (w n)⟫_ℂ).re := by
    intro n
    simp only [hHdef, add_apply, smul_apply, id_apply, inner_add_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hwn, Complex.add_re]
    simp
  have hle : α + 0 ≤ 0 := by
    refine le_of_tendsto_of_tendsto' (tendsto_const_nhds.add hre) h1n (fun n => ?_)
    rw [← hHw n]
    have := hw n
    have : 0 ≤ ((n : ℝ) + 1) * ‖S (w n)‖ ^ 2 := by positivity
    linarith
  linarith

omit [CompleteSpace Z] in
lemma re_inner_ge_neg (T : Z →L[ℂ] Z) (z : Z) : -(‖T‖ * ‖z‖ ^ 2) ≤ (⟪z, T z⟫_ℂ).re := by
  have h1 : |(⟪z, T z⟫_ℂ).re| ≤ ‖T‖ * ‖z‖ ^ 2 :=
    calc |(⟪z, T z⟫_ℂ).re| ≤ ‖⟪z, T z⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖z‖ * ‖T z‖ := norm_inner_le_norm _ _
      _ ≤ ‖z‖ * (‖T‖ * ‖z‖) := by gcongr; exact T.le_opNorm _
      _ = ‖T‖ * ‖z‖ ^ 2 := by ring
  linarith [neg_abs_le (⟪z, T z⟫_ℂ).re]

lemma norm_sq_eq_re_inner_adjoint (S : Z →L[ℂ] Y) (z : Z) :
    ‖S z‖ ^ 2 = (⟪z, (adjoint S ∘L S) z⟫_ℂ).re := by
  rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Lemma 7.6 (compact perturbation coercivity).** Let `H = α I + C` with `α > 0` and `C`
compact, and let `S` be bounded and injective. Then there are `A > 0` and `ε > 0` with
`Re ⟨z, H z⟩ + A ‖S z‖² ≥ ε ‖z‖²`, and the same `A` with the lower bound `ε / 2` works for every
`H'`, `S'` with `‖H' - H‖ + A ‖S'^* S' - S^* S‖ < ε / 2`. -/
theorem compact_perturbation_coercive (α : ℝ) (hα : 0 < α) (C : Z →L[ℂ] Z)
    (hC : IsCompactOperator C) (S : Z →L[ℂ] Y) (hS : Function.Injective S) :
    ∃ A > 0, ∃ ε > 0,
      (∀ z : Z, ε * ‖z‖ ^ 2 ≤
        (⟪z, ((α : ℂ) • ContinuousLinearMap.id ℂ Z + C) z⟫_ℂ).re + A * ‖S z‖ ^ 2) ∧
      ∀ (H' : Z →L[ℂ] Z) (S' : Z →L[ℂ] Y),
        ‖H' - ((α : ℂ) • ContinuousLinearMap.id ℂ Z + C)‖ +
            A * ‖adjoint S' ∘L S' - adjoint S ∘L S‖ < ε / 2 →
        ∀ z : Z, ε / 2 * ‖z‖ ^ 2 ≤ (⟪z, H' z⟫_ℂ).re + A * ‖S' z‖ ^ 2 := by
  obtain ⟨A, hA, ε, hε, h⟩ := exists_coercive α hα C hC S hS
  refine ⟨A, hA, ε, hε, h, fun H' S' hsmall z => ?_⟩
  set H := (α : ℂ) • ContinuousLinearMap.id ℂ Z + C
  have e1 : (⟪z, H' z⟫_ℂ).re = (⟪z, H z⟫_ℂ).re + (⟪z, (H' - H) z⟫_ℂ).re := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    ring
  have e2 : ‖S' z‖ ^ 2 = ‖S z‖ ^ 2 + (⟪z, (adjoint S' ∘L S' - adjoint S ∘L S) z⟫_ℂ).re := by
    rw [norm_sq_eq_re_inner_adjoint S', norm_sq_eq_re_inner_adjoint S]
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    ring
  have b1 := re_inner_ge_neg (H' - H) z
  have b2 := re_inner_ge_neg (adjoint S' ∘L S' - adjoint S ∘L S) z
  have hz := h z
  have hz2 : 0 ≤ ‖z‖ ^ 2 := by positivity
  rw [e1, e2]
  have : (‖H' - H‖ + A * ‖adjoint S' ∘L S' - adjoint S ∘L S‖) * ‖z‖ ^ 2 ≤ ε / 2 * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hsmall.le hz2
  nlinarith

/-- **Lemma 7.6, perturbation form.** With `H`, `S` as in `compact_perturbation_coercive`,
there are `A > 0`, `ε > 0` and `δ > 0` such that `Re ⟨z, H' z⟩ + A ‖S' z‖² ≥ ε ‖z‖² / 2`
whenever `‖H' - H‖ < δ` and `‖S' - S‖ < δ`. -/
theorem compact_perturbation_coercive_nhds (α : ℝ) (hα : 0 < α) (C : Z →L[ℂ] Z)
    (hC : IsCompactOperator C) (S : Z →L[ℂ] Y) (hS : Function.Injective S) :
    ∃ A > 0, ∃ ε > 0, ∃ δ > 0, ∀ (H' : Z →L[ℂ] Z) (S' : Z →L[ℂ] Y),
      ‖H' - ((α : ℂ) • ContinuousLinearMap.id ℂ Z + C)‖ < δ → ‖S' - S‖ < δ →
        ∀ z : Z, ε / 2 * ‖z‖ ^ 2 ≤ (⟪z, H' z⟫_ℂ).re + A * ‖S' z‖ ^ 2 := by
  obtain ⟨A, hA, ε, hε, -, h⟩ := compact_perturbation_coercive α hα C hC S hS
  set K := 1 + A * (2 * ‖S‖ + 1)
  have hK : 0 < K := by positivity
  refine ⟨A, hA, ε, hε, min 1 (ε / (4 * K)), by positivity, fun H' S' hH hS' => h H' S' ?_⟩
  have hδ1 : min 1 (ε / (4 * K)) ≤ 1 := min_le_left _ _
  have hδ2 : min 1 (ε / (4 * K)) ≤ ε / (4 * K) := min_le_right _ _
  set δ := min 1 (ε / (4 * K))
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hS'.le
  have hadj : ‖adjoint S' ∘L S' - adjoint S ∘L S‖ ≤ (2 * ‖S‖ + 1) * δ := by
    have e : adjoint S' ∘L S' - adjoint S ∘L S =
        adjoint S' ∘L (S' - S) + (adjoint (S' - S)) ∘L S := by
      rw [map_sub]; simp [comp_sub, sub_comp]
    rw [e]
    have hS'n : ‖S'‖ ≤ ‖S‖ + δ := by
      have := norm_sub_norm_le S' S; linarith
    calc _ ≤ ‖adjoint S' ∘L (S' - S)‖ + ‖(adjoint (S' - S)) ∘L S‖ := norm_add_le _ _
      _ ≤ ‖adjoint S'‖ * ‖S' - S‖ + ‖adjoint (S' - S)‖ * ‖S‖ :=
          add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
      _ = ‖S'‖ * ‖S' - S‖ + ‖S' - S‖ * ‖S‖ := by simp only [LinearIsometryEquiv.norm_map]
      _ ≤ (‖S‖ + δ) * δ + δ * ‖S‖ := by gcongr
      _ ≤ (2 * ‖S‖ + 1) * δ := by nlinarith [norm_nonneg S]
  have : ‖H' - ((α : ℂ) • ContinuousLinearMap.id ℂ Z + C)‖ +
      A * ‖adjoint S' ∘L S' - adjoint S ∘L S‖ < δ + A * ((2 * ‖S‖ + 1) * δ) := by
    have := mul_le_mul_of_nonneg_left hadj hA.le
    linarith
  have h2 : δ + A * ((2 * ‖S‖ + 1) * δ) = K * δ := by ring
  have h3 : K * δ ≤ ε / 4 := by
    calc K * δ ≤ K * (ε / (4 * K)) := by gcongr
      _ = ε / 4 := by field_simp
  linarith

end PolyaNeumann
