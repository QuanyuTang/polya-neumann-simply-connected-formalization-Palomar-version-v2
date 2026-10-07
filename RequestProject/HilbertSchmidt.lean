module

public import RequestProject.FiniteRankCompletion

/-!
# Hilbert–Schmidt operators are compact

Generic Hilbert-space facts used for the regularizing remainders of Section 6 (Lemmas 6.3 and
6.7): if `T : H → K` is bounded and `∑ᵢ ‖T bᵢ‖² < ∞` for a Hilbert basis `(bᵢ)` of `H`, then
`‖T‖ ≤ (∑ᵢ ‖T bᵢ‖²)^{1/2}` (`norm_le_sqrt_tsum_norm_sq`) and `T` is compact
(`isCompactOperator_of_summable_norm_sq`), being the operator-norm limit of the finite-rank
truncations `x ↦ ∑_{i ∈ F} ⟨bᵢ, x⟩ T bᵢ`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- Expansion of `T x` along a Hilbert basis. -/
lemma hasSum_apply_hilbertBasis (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) (x : H) :
    HasSum (fun i => ⟪b i, x⟫_𝕜 • T (b i)) (T x) := by
  have := (b.hasSum_repr x).mapL T
  simpa [b.repr_apply_apply] using this

/-- Cauchy–Schwarz bound for the part of the expansion of `T x` over a set `s` of indices. -/
lemma norm_tsum_subtype_le (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) (s : Set ι)
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) (x : H) :
    ‖∑' i : s, ⟪b i, x⟫_𝕜 • T (b i)‖ ≤ Real.sqrt (∑' i : s, ‖T (b i)‖ ^ 2) * ‖x‖ := by
  set f : s → ℝ := fun i => ‖⟪b i, x⟫_𝕜‖
  set g : s → ℝ := fun i => ‖T (b i)‖
  have hbessel : Summable fun i : ι => ‖⟪b i, x⟫_𝕜‖ ^ 2 :=
    b.orthonormal.inner_products_summable x
  have hf2 : Summable fun i : s => f i ^ (2 : ℝ) := by
    simpa [f, Real.rpow_two, Function.comp_def] using hbessel.subtype (· ∈ s)
  have hg2 : Summable fun i : s => g i ^ (2 : ℝ) := by
    simpa [g, Real.rpow_two, Function.comp_def] using hT.subtype (· ∈ s)
  have hfg := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg _) (fun i => norm_nonneg _) hf2 hg2
  have hle := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg _) (fun i => norm_nonneg _) hf2 hg2
  have hsumf : ∑' i : s, f i ^ (2 : ℝ) ≤ ‖x‖ ^ 2 := by
    have h1 : ∑' i : s, f i ^ (2 : ℝ) ≤ ∑' i : ι, ‖⟪b i, x⟫_𝕜‖ ^ 2 := by
      simp only [f, Real.rpow_two]
      exact hbessel.tsum_subtype_le _ s (fun i => by positivity)
    exact h1.trans (b.orthonormal.tsum_inner_products_le x)
  have hnorm : Summable fun i : s => ‖⟪b i, x⟫_𝕜 • T (b i)‖ := by
    simpa [norm_smul, f, g] using hfg
  calc ‖∑' i : s, ⟪b i, x⟫_𝕜 • T (b i)‖ ≤ ∑' i : s, ‖⟪b i, x⟫_𝕜 • T (b i)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ = ∑' i : s, f i * g i := by simp [norm_smul, f, g]
    _ ≤ (∑' i : s, f i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑' i : s, g i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        hle
    _ ≤ (‖x‖ ^ 2) ^ (1 / (2 : ℝ)) * (∑' i : s, g i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = Real.sqrt (∑' i : s, ‖T (b i)‖ ^ 2) * ‖x‖ := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg x), mul_comm]
        simp [g]

/-- **Hilbert–Schmidt bound.** `‖T‖ ≤ (∑ᵢ ‖T bᵢ‖²)^{1/2}` for a Hilbert basis `(bᵢ)`. -/
theorem norm_le_sqrt_tsum_norm_sq (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K)
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) :
    ‖T‖ ≤ Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) fun x => ?_
  have h := norm_tsum_subtype_le b T Set.univ hT x
  have e1 : ∑' i : (Set.univ : Set ι), ⟪b i, x⟫_𝕜 • T (b i) = T x := by
    rw [tsum_univ (f := fun i => ⟪b i, x⟫_𝕜 • T (b i))]
    exact (hasSum_apply_hilbertBasis b T x).tsum_eq
  have e2 : ∑' i : (Set.univ : Set ι), ‖T (b i)‖ ^ 2 = ∑' i, ‖T (b i)‖ ^ 2 :=
    tsum_univ (f := fun i => ‖T (b i)‖ ^ 2)
  rwa [e1, e2] at h

/-- The finite-rank truncation `x ↦ ∑_{i ∈ F} ⟨bᵢ, x⟩ T bᵢ`. -/
def hsTrunc (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) (F : Finset ι) : H →L[𝕜] K :=
  ∑ i ∈ F, (innerSL 𝕜 (b i)).smulRight (T (b i))

lemma hsTrunc_apply (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) (F : Finset ι) (x : H) :
    hsTrunc b T F x = ∑ i ∈ F, ⟪b i, x⟫_𝕜 • T (b i) := by
  simp [hsTrunc, ContinuousLinearMap.sum_apply]

lemma isCompactOperator_hsTrunc (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) (F : Finset ι) :
    IsCompactOperator (hsTrunc b T F) := by
  classical
  unfold hsTrunc
  induction F using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → K))
  | insert j F hj ih =>
    rw [Finset.sum_insert hj]
    refine IsCompactOperator.add (f := ⇑((innerSL 𝕜 (b j)).smulRight (T (b j)))) ?_ ih
    have hle : LinearMap.range (((innerSL 𝕜 (b j)).smulRight (T (b j)) : H →L[𝕜] K) :
        H →ₗ[𝕜] K) ≤ 𝕜 ∙ T (b j) := by
      rintro _ ⟨x, rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
    haveI : FiniteDimensional 𝕜 (LinearMap.range (((innerSL 𝕜 (b j)).smulRight (T (b j)) :
        H →L[𝕜] K) : H →ₗ[𝕜] K)) := Submodule.finiteDimensional_of_le hle
    exact isCompactOperator_of_finiteDimensional_range _

lemma norm_sub_hsTrunc_le (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K)
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) (F : Finset ι) :
    ‖T - hsTrunc b T F‖ ≤ Real.sqrt (∑' i : {i // i ∉ F}, ‖T (b i)‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hs := hasSum_apply_hilbertBasis b T x
  have hsplit := hs.summable.sum_add_tsum_compl (s := F)
  rw [hs.tsum_eq] at hsplit
  have : (T - hsTrunc b T F) x = ∑' i : {i // i ∉ F}, ⟪b i, x⟫_𝕜 • T (b i) := by
    rw [ContinuousLinearMap.sub_apply, hsTrunc_apply, ← hsplit]
    simp only [add_sub_cancel_left]
    rfl
  rw [this]
  exact norm_tsum_subtype_le b T {i | i ∉ F} hT x

/-- **Hilbert–Schmidt operators are compact.** If `∑ᵢ ‖T bᵢ‖² < ∞` for a Hilbert basis
`(bᵢ)` of `H`, then `T` is a compact operator. -/
theorem isCompactOperator_of_summable_norm_sq [CompleteSpace K] (b : HilbertBasis ι 𝕜 H)
    (T : H →L[𝕜] K) (hT : Summable fun i => ‖T (b i)‖ ^ 2) : IsCompactOperator T := by
  have hlim : Tendsto (fun F : Finset ι => hsTrunc b T F) atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 := tendsto_tsum_compl_atTop_zero (fun i => ‖T (b i)‖ ^ 2)
    have h1 : Tendsto (fun F : Finset ι => Real.sqrt (∑' i : {i // i ∉ F}, ‖T (b i)‖ ^ 2))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h0
    refine squeeze_zero (fun F => norm_nonneg _) (fun F => ?_) h1
    rw [norm_sub_rev]
    exact norm_sub_hsTrunc_le b T hT F
  have hmem : ∀ F, hsTrunc b T F ∈ {f : H →L[𝕜] K | IsCompactOperator f} :=
    fun F => isCompactOperator_hsTrunc b T F
  exact isClosed_setOf_isCompactOperator.mem_of_tendsto hlim (Eventually.of_forall hmem)

end PolyaNeumann
