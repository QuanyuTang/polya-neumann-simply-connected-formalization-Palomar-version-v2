module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Tactic

/-!
# Fredholm alternative, finite-rank completion (Lemma 7.2) and the fixed complement (Lemma 7.3)

The paper invokes the Fredholm alternative for operators of the form identity plus compact
(External theorem on compact operators). Mathlib does not contain it, so it is proved here from
the Riesz lemma, for an operator `I + C` with `C` compact on a Banach space over `ℝ` or `ℂ`:

* `finiteDimensional_ker_one_add`: `ker (I + C)` is finite-dimensional;
* `injective_iff_surjective_one_add`: `I + C` is injective iff it is surjective
  (both directions via the Riesz chain argument on `ran (I+C)^n` and `ker (I+C)^n`);
* `exists_complement_range_one_add`: there is a subspace of dimension `dim ker (I + C)` meeting
  `ran (I + C)` only in `0` (the half of "index zero" used in the paper).

With these:

* `finite_rank_completion` / `finite_rank_completion_isUnit` (**Lemma 7.2**): on a Hilbert space
  `H = H₀ ⊕ H₀ᗮ`, if `A = I + C` is injective on `H₀`, there is a finite-rank `F : H₀ᗮ → H` with
  `A + F Π₁` invertible;
* `finite_rank_completion_basis` (**Lemma 7.2**, second sentence): given Hilbert bases of `H` and
  `H₀ᗮ`, `F` can be taken as `∑_r ⟪u_r, ·⟫ v_r` with finite basis combinations `u_r`, `v_r`;
* `exists_fixed_complement` (**Lemma 7.3**, abstract form): for a norm-continuous family
  `Ĵ_E : H₀ → H` with `Ĵ_{E₀}` injective and `Ĵ_{E₀} Π₀ + Π₁ − I` compact, there is a fixed
  `R = inclusion + finite rank` such that `𝔅_E = Ĵ_E Π₀ + R Π₁` is invertible near `E₀`, with
  norm-continuous inverse; `exists_fixed_complement_basis` gives `R` with finite basis input and
  output vectors.

In the paper `H₀ = 𝓗_{≤0}`, `H₀ᗮ = 𝓗_+` and `Ĵ_E` is the normalized conormal transmutation; its
compactness property (Lemma 6.13) is a hypothesis here.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology

section Banach

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A compact operator maps a bounded sequence to one with a convergent subsequence. -/
lemma IsCompactOperator.exists_subseq_tendsto {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    {u : ℕ → X} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ y : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => C (u (φ n))) atTop (𝓝 y) := by
  have hK := hC.isCompact_closure_image_closedBall R
  have hmem : ∀ n, C (u n) ∈ closure (C '' Metric.closedBall 0 R) := fun n =>
    subset_closure ⟨u n, by simpa using hu n, rfl⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact ⟨y, φ, hφ, hlim⟩

/-- A compact operator cannot map a norm-bounded sequence to a sequence with pairwise distances
at least `1/2`. -/
lemma IsCompactOperator.not_separated {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    {u : ℕ → X} (hu : ∀ n, ‖u n‖ ≤ 1) (hsep : ∀ m n, m < n → 1 / 2 ≤ ‖C (u n) - C (u m)‖) :
    False := by
  obtain ⟨y, φ, hφ, hlim⟩ := IsCompactOperator.exists_subseq_tendsto hC hu
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N, hN⟩ := hc (1 / 2) (by norm_num)
  have h1 := hN (N + 1) (by omega)
  rw [dist_eq_norm] at h1
  have := hsep (φ N) (φ (N + 1)) (hφ (by omega))
  linarith

/-- Riesz chain argument, decreasing version. -/
lemma not_strictAnti_chain {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (R : ℕ → Submodule 𝕜 X) (hcl : ∀ n, IsClosed (R n : Set X))
    (hlt : ∀ n, R (n + 1) < R n) (hmap : ∀ n, ∀ x ∈ R n, x + C x ∈ R (n + 1)) : False := by
  have hanti : Antitone R := antitone_nat_of_succ_le fun n => (hlt n).le
  have hx : ∀ n, ∃ x ∈ R n, ‖x‖ = 1 ∧ ∀ y ∈ R (n + 1), 1 / 2 ≤ ‖x - y‖ := by
    intro n
    obtain ⟨z, hzn, hz⟩ := SetLike.exists_of_lt (hlt n)
    -- Riesz lemma inside the subspace `R n`
    let F : Submodule 𝕜 (R n) := (R (n + 1)).comap (R n).subtype
    have hFc : IsClosed (F : Set (R n)) := (hcl (n + 1)).preimage continuous_subtype_val
    obtain ⟨x, -, hx1, hxF⟩ := riesz_lemma_of_lt_one hFc ⟨⟨z, hzn⟩, hz⟩ (r := 1 / 2) (by norm_num)
    refine ⟨x, x.2, by simpa using hx1, fun y hy => ?_⟩
    have := hxF ⟨y, (hlt n).le hy⟩ hy
    simpa using this
  choose u huR hu1 husep using hx
  refine IsCompactOperator.not_separated hC (u := u) (fun n => (hu1 n).le) fun m n hmn => ?_
  have hmem : (u m + C (u m)) - (u n + C (u n)) + u n ∈ R (m + 1) := by
    refine add_mem (sub_mem (hmap m _ (huR m)) (hanti (show m + 1 ≤ n + 1 by omega)
      (hmap n _ (huR n)))) (hanti (show m + 1 ≤ n by omega) (huR n))
  have := husep m _ hmem
  convert this using 2
  abel

/-- Riesz chain argument, increasing version. -/
lemma not_strictMono_chain {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (N : ℕ → Submodule 𝕜 X) (hcl : ∀ n, IsClosed (N n : Set X))
    (hlt : ∀ n, N n < N (n + 1)) (hmap : ∀ n, ∀ x ∈ N (n + 1), x + C x ∈ N n) : False := by
  have hmono : Monotone N := monotone_nat_of_le_succ fun n => (hlt n).le
  have hx : ∀ n, ∃ x ∈ N (n + 1), ‖x‖ = 1 ∧ ∀ y ∈ N n, 1 / 2 ≤ ‖x - y‖ := by
    intro n
    obtain ⟨z, hzn, hz⟩ := SetLike.exists_of_lt (hlt n)
    let F : Submodule 𝕜 (N (n + 1)) := (N n).comap (N (n + 1)).subtype
    have hFc : IsClosed (F : Set (N (n + 1))) := (hcl n).preimage continuous_subtype_val
    obtain ⟨x, -, hx1, hxF⟩ := riesz_lemma_of_lt_one hFc ⟨⟨z, hzn⟩, hz⟩ (r := 1 / 2) (by norm_num)
    refine ⟨x, x.2, by simpa using hx1, fun y hy => ?_⟩
    have := hxF ⟨y, (hlt n).le hy⟩ hy
    simpa using this
  choose u huN hu1 husep using hx
  refine IsCompactOperator.not_separated hC (u := u) (fun n => (hu1 n).le) fun m n hmn => ?_
  have hmem : (u n + C (u n)) - (u m + C (u m)) + u m ∈ N n := by
    refine add_mem (sub_mem (hmap n _ (huN n)) (hmono (show m ≤ n by omega)
      (hmap m _ (huN m)))) (hmono (show m + 1 ≤ n by omega) (huN m))
  have := husep n _ hmem
  rw [norm_sub_rev]
  convert this using 2
  abel


section Fredholm

variable [CompleteSpace X]

omit [CompleteSpace X] in
/-- If `I + C` is injective with `C` compact, then `I + C` is bounded below. -/
lemma exists_bound_of_injective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (hinj : Function.Injective ⇑((1 : X →L[𝕜] X) + C)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖(1 + C) x‖ := by
  by_contra hne
  push_neg at hne
  have hx : ∀ n : ℕ, ∃ u : X, ‖u‖ = 1 ∧ ‖(1 + C) u‖ < 1 / (n + 1) := by
    intro n
    obtain ⟨x, hx⟩ := hne (1 / (n + 1)) (by positivity)
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    refine ⟨(‖x‖⁻¹ : 𝕜) • x, norm_smul_inv_norm hx0, ?_⟩
    rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    rw [inv_mul_lt_iff₀ hpos]
    linarith
  choose u hu1 hu using hx
  obtain ⟨y, φ, hφ, hlim⟩ := IsCompactOperator.exists_subseq_tendsto hC (fun n => (hu1 n).le)
  have hT : Tendsto (fun n => (1 + C) (u (φ n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hu (φ n)).le) ?_
    have : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact this
  have hu_lim : Tendsto (fun n => u (φ n)) atTop (𝓝 (-y)) := by
    have := hT.sub hlim
    simp only [zero_sub] at this
    refine this.congr fun n => ?_
    simp
  have hTy : (1 + C) (-y) = 0 :=
    tendsto_nhds_unique (((1 + C).continuous.tendsto _).comp hu_lim) hT
  have hy0 : -y = 0 := hinj (by rw [hTy, map_zero])
  have hnorm : Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖-y‖) := hu_lim.norm
  simp only [hu1, hy0, norm_zero] at hnorm
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hnorm)

/-- **Fredholm alternative**, injective implies surjective: if `C` is compact and `I + C` is
injective, then `I + C` is surjective. -/
theorem surjective_of_injective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (hinj : Function.Injective ⇑((1 : X →L[𝕜] X) + C)) :
    Function.Surjective ⇑((1 : X →L[𝕜] X) + C) := by
  obtain ⟨c, hc, hbound⟩ := exists_bound_of_injective_one_add hC hinj
  set T : X →L[𝕜] X := 1 + C with hTdef
  by_contra hs
  obtain ⟨y, hy⟩ : ∃ y, y ∉ Set.range T := by
    simpa [Function.Surjective, Set.mem_range] using hs
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T := by
    refine T.antilipschitz_of_bound fun x => ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    have := hbound x
    rw [le_inv_mul_iff₀ hc]
    linarith
  have hantin : ∀ n : ℕ, AntilipschitzWith (Real.toNNReal c⁻¹ ^ n) (T ^ n : X →L[𝕜] X) := by
    intro n
    induction n with
    | zero => simpa using AntilipschitzWith.id
    | succ n ih =>
      rw [pow_succ' (Real.toNNReal c⁻¹), pow_succ T, FunLike.coe_mul_eq_comp]
      exact ih.comp hanti
  have hinjn : ∀ n : ℕ, Function.Injective (T ^ n : X →L[𝕜] X) := fun n => (hantin n).injective
  refine not_strictAnti_chain hC (fun n => LinearMap.range ((T ^ n : X →L[𝕜] X) : X →ₗ[𝕜] X))
    (fun n => ?_) (fun n => ?_) (fun n => ?_)
  · rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    exact (hantin n).isClosed_range (T ^ n).uniformContinuous
  · refine lt_of_le_of_ne ?_ ?_
    · rintro x ⟨z, rfl⟩
      exact ⟨T z, by rw [pow_succ]; rfl⟩
    · intro heq
      have hmem : (T ^ n) y ∈ LinearMap.range ((T ^ n : X →L[𝕜] X) : X →ₗ[𝕜] X) := ⟨y, rfl⟩
      rw [← heq] at hmem
      obtain ⟨z, hz⟩ := hmem
      apply hy
      refine ⟨z, hinjn n ?_⟩
      rw [← hz, pow_succ]
      rfl
  · rintro x ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [pow_succ']
    rfl

omit [CompleteSpace X] in
/-- **Fredholm alternative**, surjective implies injective: if `C` is compact and `I + C` is
surjective, then `I + C` is injective. -/
theorem injective_of_surjective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (hsurj : Function.Surjective ⇑((1 : X →L[𝕜] X) + C)) :
    Function.Injective ⇑((1 : X →L[𝕜] X) + C) := by
  set T : X →L[𝕜] X := 1 + C with hTdef
  rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨x₁, hx₁, hx₁0⟩ := hne
  have hsurjn : ∀ n : ℕ, Function.Surjective (T ^ n : X →L[𝕜] X) := fun n => by
    rw [FunLike.coe_pow_eq_iterate]
    exact hsurj.iterate n
  refine not_strictMono_chain hC (fun n => LinearMap.ker ((T ^ n : X →L[𝕜] X) : X →ₗ[𝕜] X))
    (fun n => (T ^ n).isClosed_ker) (fun n => ?_) (fun n => ?_)
  · refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      rw [pow_succ', ContinuousLinearMap.mul_apply, hx, map_zero]
    · intro heq
      obtain ⟨z, hz⟩ := hsurjn n x₁
      have hmem : z ∈ LinearMap.ker ((T ^ (n + 1) : X →L[𝕜] X) : X →ₗ[𝕜] X) := by
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        rw [pow_succ', ContinuousLinearMap.mul_apply, hz, hx₁]
      rw [← heq] at hmem
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hmem
      exact hx₁0 (hz ▸ hmem)
  · intro x hx
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
    rw [pow_succ, ContinuousLinearMap.mul_apply] at hx
    simpa [hTdef] using hx

/-- **Fredholm alternative**: for compact `C`, `I + C` is injective iff it is surjective. -/
theorem injective_iff_surjective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C) :
    Function.Injective ⇑((1 : X →L[𝕜] X) + C) ↔ Function.Surjective ⇑((1 : X →L[𝕜] X) + C) :=
  ⟨surjective_of_injective_one_add hC, injective_of_surjective_one_add hC⟩

omit [CompleteSpace X] in
/-- The kernel of `I + C` is finite-dimensional when `C` is compact. -/
theorem finiteDimensional_ker_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C) :
    FiniteDimensional 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  by_contra hfin
  obtain ⟨R, f, -, hfR, hf⟩ := exists_seq_norm_le_one_le_norm_sub hfin
  have hCf : ∀ n, C (f n : X) = -(f n : X) := by
    intro n
    have := (f n).2
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply] at this
    exact eq_neg_of_add_eq_zero_right this
  obtain ⟨y, φ, hφ, hlim⟩ :=
    IsCompactOperator.exists_subseq_tendsto hC (u := fun n => (f n : X)) (R := R)
      (fun n => hfR n)
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N, hN⟩ := hc 1 one_pos
  have h1 := hN (N + 1) (by omega)
  rw [dist_eq_norm, hCf, hCf, neg_sub_neg, norm_sub_rev] at h1
  have h2 := hf (hφ.injective.ne (show N + 1 ≠ N by omega))
  rw [← Submodule.coe_sub, ← Submodule.coe_norm] at h1
  linarith

end Fredholm

section FiniteRank

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A bounded operator with finite-dimensional range is compact. -/
theorem isCompactOperator_of_finiteDimensional_range (F : X →L[𝕜] Y)
    [FiniteDimensional 𝕜 (LinearMap.range (F : X →ₗ[𝕜] Y))] : IsCompactOperator F := by
  set V := LinearMap.range (F : X →ₗ[𝕜] Y)
  let F' : X →L[𝕜] V := F.codRestrict V (fun x => LinearMap.mem_range_self _ x)
  refine ⟨V.subtype '' Metric.closedBall 0 ‖F'‖, (isCompact_closedBall _ _).image
    continuous_subtype_val, ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun x hx => ?_
  refine ⟨F' x, ?_, rfl⟩
  rw [mem_closedBall_zero_iff]
  rw [mem_ball_zero_iff] at hx
  calc ‖F' x‖ ≤ ‖F'‖ * ‖x‖ := F'.le_opNorm x
    _ ≤ ‖F'‖ * 1 := mul_le_mul_of_nonneg_left hx.le F'.opNorm_nonneg
    _ = ‖F'‖ := mul_one _

end FiniteRank

section Codim

variable [CompleteSpace X]

/-- A surjective linear map from a larger finite-dimensional space. -/
lemma exists_surjective_of_finrank_le {K Q : Type*} [AddCommGroup K] [Module 𝕜 K]
    [AddCommGroup Q] [Module 𝕜 Q] [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 Q]
    (h : Module.finrank 𝕜 Q ≤ Module.finrank 𝕜 K) :
    ∃ L : K →ₗ[𝕜] Q, Function.Surjective L := by
  let eK : K ≃ₗ[𝕜] (Fin (Module.finrank 𝕜 K) → 𝕜) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let eQ : Q ≃ₗ[𝕜] (Fin (Module.finrank 𝕜 Q) → 𝕜) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  refine ⟨eQ.symm.toLinearMap ∘ₗ LinearMap.funLeft 𝕜 𝕜 (Fin.castLE h) ∘ₗ eK.toLinearMap, ?_⟩
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact eQ.symm.surjective.comp ((LinearMap.funLeft_surjective_of_injective _ _ _
    (Fin.castLE_injective h)).comp eK.surjective)

omit [CompleteSpace X] in
/-- If the range of `I + C` together with a finite-dimensional `Q` spans everything, then
`dim Q ≥ dim ker (I + C)`. -/
lemma finrank_ker_le_of_sup_eq_top {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (Q : Submodule 𝕜 X) [FiniteDimensional 𝕜 Q]
    (htop : LinearMap.range (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X) ⊔ Q = ⊤) :
    haveI := finiteDimensional_ker_one_add hC
    Module.finrank 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) ≤
      Module.finrank 𝕜 Q := by
  haveI := finiteDimensional_ker_one_add hC
  set A : X →L[𝕜] X := (1 : X →L[𝕜] X) + C with hAdef
  set K := LinearMap.ker (A : X →ₗ[𝕜] X)
  by_contra hlt
  push_neg at hlt
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional K
  obtain ⟨L, hL⟩ := exists_surjective_of_finrank_le (K := K) (Q := Q) hlt.le
  -- a nonzero element of the kernel of `L`
  obtain ⟨k₁, hk₁L, hk₁0⟩ : ∃ k₁ ∈ LinearMap.ker L, k₁ ≠ 0 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker L
    have hr : Module.finrank 𝕜 (LinearMap.range L) ≤ Module.finrank 𝕜 Q :=
      Submodule.finrank_le _
    have hpos : 0 < Module.finrank 𝕜 (LinearMap.ker L) := by omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.1 hpos)
  let Lc : K →L[𝕜] Q := LinearMap.toContinuousLinearMap L
  let F : X →L[𝕜] X := Q.subtypeL ∘L Lc ∘L P
  have hFrange : FiniteDimensional 𝕜 (LinearMap.range (F : X →ₗ[𝕜] X)) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    exact (Lc (P x)).2
  have hFc : IsCompactOperator (C + F) :=
    hC.add (isCompactOperator_of_finiteDimensional_range F)
  have hKA : ∀ k ∈ K, A k = 0 := fun k hk => hk
  have hsurj : Function.Surjective ((1 : X →L[𝕜] X) + (C + F)) := by
    intro h
    have hh : h ∈ LinearMap.range (A : X →ₗ[𝕜] X) ⊔ Q := htop ▸ Submodule.mem_top
    obtain ⟨_, ⟨x, rfl⟩, q, hq, rfl⟩ := Submodule.mem_sup.1 hh
    obtain ⟨k₀, hk₀⟩ := hL ⟨q, hq⟩
    refine ⟨x - (P x : X) + (k₀ : X), ?_⟩
    have h1 : (1 : X →L[𝕜] X) + (C + F) = A + F := by rw [hAdef, add_assoc]
    rw [h1, ContinuousLinearMap.add_apply]
    have hA : A (x - (P x : X) + (k₀ : X)) = A x := by
      rw [map_add, map_sub, hKA _ (P x).2, hKA _ k₀.2, sub_zero, add_zero]
    have hF : F (x - (P x : X) + (k₀ : X)) = q := by
      simp only [F, ContinuousLinearMap.comp_apply, map_add, map_sub]
      have hPx : P (P x : X) = P x := hP (P x)
      have hPk : P (k₀ : X) = k₀ := hP k₀
      rw [hPx, hPk, sub_self, zero_add]
      simp [Lc, hk₀]
    rw [hA, hF]
    rfl
  have hinj := injective_of_surjective_one_add hFc hsurj
  apply hk₁0
  have : ((1 : X →L[𝕜] X) + (C + F)) (k₁ : X) = ((1 : X →L[𝕜] X) + (C + F)) 0 := by
    have h1 : (1 : X →L[𝕜] X) + (C + F) = A + F := by rw [hAdef, add_assoc]
    rw [h1, map_zero, ContinuousLinearMap.add_apply, hKA _ k₁.2, zero_add]
    simp only [F, ContinuousLinearMap.comp_apply, hP k₁]
    simp [Lc, LinearMap.mem_ker.1 hk₁L]
  exact Subtype.ext (hinj this)

omit [CompleteSpace X] in
/-- The range of `I + C` has codimension at least `dim ker (I + C)`: there is a subspace `Q`
of dimension `dim ker (I + C)` meeting the range only in `0`. -/
theorem exists_complement_range_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C) :
    haveI := finiteDimensional_ker_one_add hC
    ∃ Q : Submodule 𝕜 X, FiniteDimensional 𝕜 Q ∧
      Module.finrank 𝕜 Q =
        Module.finrank 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) ∧
      Disjoint Q (LinearMap.range (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  haveI := finiteDimensional_ker_one_add hC
  set k := Module.finrank 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X))
  set Rg := LinearMap.range (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)
  suffices h : ∀ n ≤ k, ∃ Q : Submodule 𝕜 X, FiniteDimensional 𝕜 Q ∧
      Module.finrank 𝕜 Q = n ∧ Disjoint Q Rg from h k le_rfl
  intro n
  induction n with
  | zero => exact fun _ => ⟨⊥, inferInstance, finrank_bot _ _, disjoint_bot_left⟩
  | succ n ih =>
    intro hn
    obtain ⟨Q, hQf, hQn, hQd⟩ := ih (by omega)
    by_cases htop : Rg ⊔ Q = ⊤
    · have := finrank_ker_le_of_sup_eq_top hC Q htop
      omega
    · obtain ⟨y, hy⟩ : ∃ y, y ∉ Rg ⊔ Q := by
        by_contra hall
        push_neg at hall
        exact htop (eq_top_iff.2 fun y _ => hall y)
      have hyQ : y ∉ Q := fun h => hy (Submodule.mem_sup_right h)
      refine ⟨Q ⊔ Submodule.span 𝕜 {y}, inferInstance, ?_, ?_⟩
      · have hy0 : y ≠ 0 := fun h => hyQ (h ▸ Q.zero_mem)
        have hinf : Q ⊓ Submodule.span 𝕜 {y} = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          obtain ⟨hzQ, hzy⟩ := Submodule.mem_inf.1 hz
          obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hzy
          by_cases ht : t = 0
          · simp [ht]
          · exact absurd ((Submodule.smul_mem_iff Q ht).1 hzQ) hyQ
        have := Submodule.finrank_sup_add_finrank_inf_eq Q (Submodule.span 𝕜 {y})
        rw [hinf, finrank_bot, add_zero, finrank_span_singleton hy0, hQn] at this
        exact this
      · rw [Submodule.disjoint_def]
        intro z hz hzR
        obtain ⟨q, hq, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hw
        by_cases ht : t = 0
        · subst ht
          simp only [zero_smul, add_zero] at hzR ⊢
          exact Submodule.disjoint_def.1 hQd q hq hzR
        · exfalso
          apply hy
          have : y = t⁻¹ • (q + t • y) - t⁻¹ • q := by
            rw [smul_add, inv_smul_smul₀ ht]; abel
          rw [this]
          exact sub_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_left hzR))
            (Submodule.smul_mem _ _ (Submodule.mem_sup_right hq))

end Codim

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Lemma 7.2 (finite-rank completion).** Let `H = H₀ ⊕ H₀ᗮ` be a Hilbert space and
`A = I + C` with `C` compact. If `A` is injective on `H₀`, there is a finite-rank bounded
`F : H₀ᗮ → H` such that `A + F Π₁` is bijective, where `Π₁` is the orthogonal projection onto
`H₀ᗮ`. -/
theorem finite_rank_completion {C : H →L[𝕜] H} (hC : IsCompactOperator C)
    (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (hinj : ∀ x ∈ H₀, x + C x = 0 → x = 0) :
    ∃ F : H₀ᗮ →L[𝕜] H, FiniteDimensional 𝕜 (LinearMap.range (F : H₀ᗮ →ₗ[𝕜] H)) ∧
      Function.Bijective ⇑((1 : H →L[𝕜] H) + C + F ∘L H₀ᗮ.orthogonalProjection) := by
  haveI := finiteDimensional_ker_one_add hC
  set A : H →L[𝕜] H := (1 : H →L[𝕜] H) + C with hAdef
  set K := LinearMap.ker (A : H →ₗ[𝕜] H) with hKdef
  obtain ⟨Q, hQf, hQk, hQd⟩ := exists_complement_range_one_add hC
  set P₁ : H →L[𝕜] H₀ᗮ := H₀ᗮ.orthogonalProjection
  have hKA : ∀ k ∈ K, k + C k = 0 := fun k hk => by
    simpa [hAdef] using (LinearMap.mem_ker.1 hk)
  -- `Π₁` is injective on the kernel
  have hP₁inj : Function.Injective ((P₁ : H →ₗ[𝕜] H₀ᗮ) ∘ₗ K.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro k hk
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hk
    have h0 : (k : H) ∈ H₀ := by
      have := (Submodule.orthogonalProjection_eq_zero_iff (K := H₀ᗮ)).1 hk
      rwa [Submodule.orthogonal_orthogonal] at this
    have := hinj _ h0 (hKA _ k.2)
    simp [Subtype.ext_iff, this]
  set M : Submodule 𝕜 H₀ᗮ := LinearMap.range ((P₁ : H →ₗ[𝕜] H₀ᗮ) ∘ₗ K.subtype) with hMdef
  have hMk : Module.finrank 𝕜 M = Module.finrank 𝕜 K := LinearMap.finrank_range_of_inj hP₁inj
  let e : M ≃ₗ[𝕜] Q := LinearEquiv.ofFinrankEq _ _ (by rw [hMk, hQk])
  let Lc : M →L[𝕜] Q := LinearMap.toContinuousLinearMap (e : M →ₗ[𝕜] Q)
  let F : H₀ᗮ →L[𝕜] H := Q.subtypeL ∘L Lc ∘L M.orthogonalProjection
  have hFQ : ∀ y, F y ∈ Q := fun y => (Lc _).2
  have hFrange : FiniteDimensional 𝕜 (LinearMap.range (F : H₀ᗮ →ₗ[𝕜] H)) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    exact hFQ x
  refine ⟨F, hFrange, ?_⟩
  have hFP : FiniteDimensional 𝕜 (LinearMap.range ((F ∘L P₁ : H →L[𝕜] H) : H →ₗ[𝕜] H)) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    exact hFQ _
  have hcpt : IsCompactOperator (C + F ∘L P₁) :=
    hC.add (isCompactOperator_of_finiteDimensional_range _)
  have heq : (1 : H →L[𝕜] H) + C + F ∘L P₁ = (1 : H →L[𝕜] H) + (C + F ∘L P₁) := add_assoc _ _ _
  have hinj' : Function.Injective ⇑((1 : H →L[𝕜] H) + C + F ∘L P₁) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply] at hx
    have hAx : A x = -F (P₁ x) := eq_neg_of_add_eq_zero_left hx
    have hAx0 : A x = 0 := by
      refine Submodule.disjoint_def.1 hQd (A x) ?_ ⟨x, rfl⟩
      rw [hAx]
      exact Q.neg_mem (hFQ _)
    have hxK : x ∈ K := hAx0
    have hF0 : F (P₁ x) = 0 := by rw [← neg_eq_zero, ← hAx, hAx0]
    have hPM : P₁ x ∈ M := ⟨⟨x, hxK⟩, rfl⟩
    have hPx : M.orthogonalProjection (P₁ x) = ⟨P₁ x, hPM⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (K := M) ⟨P₁ x, hPM⟩
    have hP0 : P₁ x = 0 := by
      have h1 : (e ⟨P₁ x, hPM⟩ : H) = 0 := by
        simpa [F, Lc, hPx] using hF0
      have h2 : e ⟨P₁ x, hPM⟩ = 0 := Subtype.ext h1
      have h3 : (⟨P₁ x, hPM⟩ : M) = 0 := by simpa using h2
      simpa using congrArg Subtype.val h3
    have h0 : x ∈ H₀ := by
      have := (Submodule.orthogonalProjection_eq_zero_iff (K := H₀ᗮ)).1 hP0
      rwa [Submodule.orthogonal_orthogonal] at this
    exact hinj x h0 (hKA x hxK)
  refine ⟨hinj', ?_⟩
  rw [heq] at hinj' ⊢
  exact surjective_of_injective_one_add hcpt hinj'

/-- A bijective bounded operator on a Banach space is a unit of the operator algebra. -/
lemma isUnit_of_bijective (f : H →L[𝕜] H) (hf : Function.Bijective f) : IsUnit f := by
  let e := ContinuousLinearEquiv.ofBijective f (LinearMap.ker_eq_bot.2 hf.1)
    (LinearMap.range_eq_top.2 hf.2)
  exact ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 H).symm e, by ext x; rfl⟩

/-- **Lemma 7.2**, stated with invertibility in the operator algebra: `A + F Π₁` is a unit. -/
theorem finite_rank_completion_isUnit {C : H →L[𝕜] H} (hC : IsCompactOperator C)
    (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (hinj : ∀ x ∈ H₀, x + C x = 0 → x = 0) :
    ∃ F : H₀ᗮ →L[𝕜] H, FiniteDimensional 𝕜 (LinearMap.range (F : H₀ᗮ →ₗ[𝕜] H)) ∧
      IsUnit ((1 : H →L[𝕜] H) + C + F ∘L H₀ᗮ.orthogonalProjection) := by
  obtain ⟨F, hF, hbij⟩ := finite_rank_completion hC H₀ hinj
  exact ⟨F, hF, isUnit_of_bijective _ hbij⟩

/-- Invertibility at `E₀` of `Ĵ_E Π₀ + R Π₁` propagates to a neighbourhood of `E₀`, with
norm-continuous inverse. -/
lemma isUnit_nhds_of_isUnit (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    {J : ℝ → (H₀ →L[𝕜] H)} (hJ : Continuous J) {E₀ : ℝ} (R : H₀ᗮ →L[𝕜] H)
    (hunit : IsUnit (J E₀ ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) :
    ∃ U ∈ 𝓝 E₀,
      (∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) ∧
      ContinuousOn (fun E => Ring.inverse
        (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) U := by
  set B : ℝ → (H →L[𝕜] H) :=
    fun E => J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection with hBdef
  have hB : Continuous B := by
    refine Continuous.add ?_ continuous_const
    exact (ContinuousLinearMap.compL 𝕜 H H₀ H).flip H₀.orthogonalProjection |>.continuous.comp hJ
  refine ⟨B ⁻¹' {x | IsUnit x}, (Units.isOpen.preimage hB).mem_nhds hunit, fun E hE => hE, ?_⟩
  intro E hE
  obtain ⟨u, hu⟩ := hE
  have := NormedRing.inverse_continuousAt u
  rw [hu] at this
  exact (this.comp hB.continuousAt).continuousWithinAt

omit [CompleteSpace H] in
/-- In the setting of Lemma 7.3, write `Ĵ_{E₀} Π₀ + Π₁ = I + C`. Then `I + C` is injective on
`H₀` and `Ĵ_{E₀} Π₀ + (ι + F) Π₁ = I + C + F Π₁` for every `F`. -/
lemma fixed_complement_aux (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (J₀ : H₀ →L[𝕜] H) (hinj : Function.Injective J₀) :
    (∀ x ∈ H₀, x + (J₀ ∘L H₀.orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)) x = 0 → x = 0) ∧
    ∀ F : H₀ᗮ →L[𝕜] H, J₀ ∘L H₀.orthogonalProjection +
        (Submodule.subtypeL H₀ᗮ + F) ∘L H₀ᗮ.orthogonalProjection =
      (1 : H →L[𝕜] H) + (J₀ ∘L H₀.orthogonalProjection +
        Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)) +
        F ∘L H₀ᗮ.orthogonalProjection := by
  refine ⟨fun x hx h0 => ?_, fun F => ?_⟩
  · have hP₁ : H₀ᗮ.orthogonalProjection x = 0 :=
      (Submodule.orthogonalProjection_eq_zero_iff (K := H₀ᗮ)).2
        (Submodule.le_orthogonal_orthogonal H₀ hx)
    have hP₀ : H₀.orthogonalProjection x = ⟨x, hx⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (K := H₀) ⟨x, hx⟩
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, hP₁, hP₀, map_zero, add_zero,
      ContinuousLinearMap.one_apply, add_sub_cancel] at h0
    have := hinj (h0.trans (map_zero J₀).symm)
    simpa using congrArg Subtype.val this
  · simp only [ContinuousLinearMap.add_comp]
    abel

/-- **Lemma 7.3 (fixed complement to the transmuted range)**, abstract form.
Let `H = H₀ ⊕ H₀ᗮ` and let `E ↦ Ĵ_E : H₀ → H` be norm-continuous. Suppose `Ĵ_{E₀}` is injective
and `Ĵ_{E₀} Π₀ + Π₁` is the identity plus a compact operator. Then there is a fixed
`R : H₀ᗮ → H`, equal to the inclusion plus a finite-rank operator, such that on a neighbourhood of
`E₀` the operator `𝔅_E = Ĵ_E Π₀ + R Π₁` (that is, `(a, z) ↦ Ĵ_E a + R z`) is invertible, with
inverse depending continuously on `E` in operator norm. -/
theorem exists_fixed_complement (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    {J : ℝ → (H₀ →L[𝕜] H)} (hJ : Continuous J) {E₀ : ℝ}
    (hcpt : IsCompactOperator (J E₀ ∘L H₀.orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)))
    (hinj : Function.Injective (J E₀)) :
    ∃ R : H₀ᗮ →L[𝕜] H,
      FiniteDimensional 𝕜
        (LinearMap.range ((R - Submodule.subtypeL H₀ᗮ : H₀ᗮ →L[𝕜] H) : H₀ᗮ →ₗ[𝕜] H)) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E => Ring.inverse
          (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) U := by
  obtain ⟨hinj', heq⟩ := fixed_complement_aux H₀ (J E₀) hinj
  obtain ⟨F, hF, hunit⟩ := finite_rank_completion_isUnit hcpt H₀ hinj'
  refine ⟨Submodule.subtypeL H₀ᗮ + F, by rwa [add_sub_cancel_left], ?_⟩
  exact isUnit_nhds_of_isUnit H₀ hJ _ (by rw [heq]; exact hunit)

/-- A finite-rank bounded operator between Hilbert spaces is a finite sum of rank-one operators
`z ↦ ⟪u_r, z⟫ v_r`. -/
lemma exists_eq_sum_rankOne {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [CompleteSpace Y] (F : Y →L[𝕜] H) [FiniteDimensional 𝕜 (LinearMap.range (F : Y →ₗ[𝕜] H))] :
    ∃ (d : ℕ) (u : Fin d → Y) (v : Fin d → H),
      F = ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r) := by
  set V := LinearMap.range (F : Y →ₗ[𝕜] H)
  let e := stdOrthonormalBasis 𝕜 V
  refine ⟨_, fun r => ContinuousLinearMap.adjoint F (e r), fun r => (e r : H), ?_⟩
  ext z
  have hz := e.sum_repr' (⟨F z, LinearMap.mem_range_self _ z⟩ : V)
  have := congrArg Subtype.val hz
  simp only [Submodule.coe_sum, Submodule.coe_smul] at this
  rw [ContinuousLinearMap.sum_apply]
  simp only [InnerProductSpace.rankOne_apply, ContinuousLinearMap.adjoint_inner_left]
  conv_lhs => rw [← this]
  rfl

omit [CompleteSpace H] in
/-- Joint continuity of the rank-one operator `(x, y) ↦ ⟪y, ·⟫ x`. -/
lemma continuous_rankOne {Y Z : Type*} [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [TopologicalSpace Z] {f : Z → H} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z => InnerProductSpace.rankOne 𝕜 (f z) (g z) := by
  simp only [InnerProductSpace.rankOne_def']
  refine Continuous.clm_comp ?_ ((innerSL 𝕜 (E := Y)).continuous.comp hg)
  exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := H)).continuous.comp hf

variable {ι ι₁ : Type*}

/-- **Lemma 7.2, basis refinement.** If `H` and `H₀ᗮ` carry Hilbert bases `b`, `b₁`, the
finite-rank correction can be taken of the form `F z = ∑_r ⟪u_r, z⟫ v_r` with every `u_r` a finite
linear combination of the `b₁ i` and every `v_r` a finite linear combination of the `b i`. -/
theorem finite_rank_completion_basis {C : H →L[𝕜] H} (hC : IsCompactOperator C)
    (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (hinj : ∀ x ∈ H₀, x + C x = 0 → x = 0)
    (b : HilbertBasis ι 𝕜 H) (b₁ : HilbertBasis ι₁ 𝕜 H₀ᗮ) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → H),
      (∀ r, u r ∈ Submodule.span 𝕜 (Set.range b₁)) ∧
      (∀ r, v r ∈ Submodule.span 𝕜 (Set.range b)) ∧
      IsUnit ((1 : H →L[𝕜] H) + C +
        (∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L H₀ᗮ.orthogonalProjection) := by
  obtain ⟨F, hF, hunit⟩ := finite_rank_completion_isUnit hC H₀ hinj
  obtain ⟨d, u, v, rfl⟩ := exists_eq_sum_rankOne F
  set P₁ : H →L[𝕜] H₀ᗮ := H₀ᗮ.orthogonalProjection
  let Φ : (Fin d → H₀ᗮ) × (Fin d → H) → (H →L[𝕜] H) := fun p =>
    (1 : H →L[𝕜] H) + C + (∑ r, InnerProductSpace.rankOne 𝕜 (p.2 r) (p.1 r)) ∘L P₁
  have hΦ : Continuous Φ := by
    refine continuous_const.add ?_
    refine ((ContinuousLinearMap.compL 𝕜 H H₀ᗮ H).flip P₁).continuous.comp ?_
    refine continuous_finset_sum _ fun r _ => ?_
    exact continuous_rankOne ((continuous_apply r).comp continuous_snd)
      ((continuous_apply r).comp continuous_fst)
  have hO : IsOpen (Φ ⁻¹' {x | IsUnit x}) := Units.isOpen.preimage hΦ
  have hdense : Dense ((Set.univ.pi fun _ : Fin d => (Submodule.span 𝕜 (Set.range b₁) : Set H₀ᗮ))
      ×ˢ (Set.univ.pi fun _ : Fin d => (Submodule.span 𝕜 (Set.range b) : Set H))) := by
    refine Dense.prod (dense_pi _ fun _ _ => ?_) (dense_pi _ fun _ _ => ?_)
    · exact (Submodule.dense_iff_topologicalClosure_eq_top).2 b₁.dense_span
    · exact (Submodule.dense_iff_topologicalClosure_eq_top).2 b.dense_span
  obtain ⟨⟨u', v'⟩, hmem, hD⟩ := hdense.inter_open_nonempty _ hO ⟨(u, v), hunit⟩
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, SetLike.mem_coe] at hD
  exact ⟨d, u', v', hD.1, hD.2, hmem⟩

/-- **Lemma 7.3**, with finite basis input and output vectors: given Hilbert bases `b` of `H`
and `b₁` of `H₀ᗮ`, the fixed map can be taken as `R z = z + ∑_r ⟪u_r, z⟫ v_r` with finite basis
combinations `u_r`, `v_r`. -/
theorem exists_fixed_complement_basis (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    {J : ℝ → (H₀ →L[𝕜] H)} (hJ : Continuous J) {E₀ : ℝ}
    (hcpt : IsCompactOperator (J E₀ ∘L H₀.orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)))
    (hinj : Function.Injective (J E₀))
    (b : HilbertBasis ι 𝕜 H) (b₁ : HilbertBasis ι₁ 𝕜 H₀ᗮ) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → H),
      (∀ r, u r ∈ Submodule.span 𝕜 (Set.range b₁)) ∧
      (∀ r, v r ∈ Submodule.span 𝕜 (Set.range b)) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E => Ring.inverse (J E ∘L H₀.orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) U := by
  obtain ⟨hinj', heq⟩ := fixed_complement_aux H₀ (J E₀) hinj
  obtain ⟨d, u, v, hu, hv, hunit⟩ := finite_rank_completion_basis hcpt H₀ hinj' b b₁
  exact ⟨d, u, v, hu, hv, isUnit_nhds_of_isUnit H₀ hJ _ (by rw [heq]; exact hunit)⟩

end Hilbert

end Banach

end PolyaNeumann
