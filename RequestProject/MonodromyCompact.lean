module

public import RequestProject.Area
public import RequestProject.NormAttained

/-!
# Lemma 4.7: `V_E - I` and `U_E - I` are compact

The paper proves that `V_E - I` is trace class by integrating the curvature formula
`∂_E V_E = -i V_E Q_E` from `E = 0`, where `Q_E = (1/4) ∫ b W_E^* D_N W_E dθ` is an integral
of operators of finite rank. We prove the (weaker) compactness statement along the same lines:
compact operators form a closed subspace, it contains `Q_E` and the derivative `∂_E V_E`, hence
the increments `V_E - V_δ`, and letting `δ → 0` gives `V_E - I`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

namespace PolyaNeumann

section ClosedSubspace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- An interval integral of a function with values in a closed subspace lies in the
subspace. -/
theorem intervalIntegral_mem_of_isClosed (K : Submodule ℂ X) (hK : IsClosed (K : Set X))
    {f : ℝ → X} (hf : ∀ t, f t ∈ K) (a b : ℝ) : ∫ t in a..b, f t ∈ K := by
  haveI : IsClosed (K : Set X) := hK
  let p : X →L[ℂ] X ⧸ K := { toLinearMap := K.mkQ, cont := continuous_quot_mk }
  have hp : ∀ x, p x = 0 ↔ x ∈ K := fun x => Submodule.Quotient.mk_eq_zero K
  by_cases hi : IntervalIntegrable f volume a b
  · have h := p.intervalIntegral_comp_comm hi
    have h0 : ∀ t, p (f t) = 0 := fun t => (hp _).mpr (hf t)
    simp only [h0, intervalIntegral.integral_zero] at h
    exact (hp _).mp h.symm
  · rw [intervalIntegral.integral_undef hi]; exact K.zero_mem

omit [CompleteSpace X] in
/-- If the derivative of `f` takes values in a closed subspace on `[a, b]`, then
`f b - f a` lies in the subspace. -/
theorem sub_mem_of_hasDerivAt (K : Submodule ℂ X) (hK : IsClosed (K : Set X)) {f f' : ℝ → X}
    {a b : ℝ} (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc a b, f' t ∈ K) : f b - f a ∈ K := by
  haveI : IsClosed (K : Set X) := hK
  let p : X →L[ℂ] X ⧸ K := { toLinearMap := K.mkQ, cont := continuous_quot_mk }
  have hp : ∀ x, p x = 0 ↔ x ∈ K := fun x => Submodule.Quotient.mk_eq_zero K
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => p (f t)) (p (f' t)) (Icc a b) t :=
    fun t ht => ((p.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hf t ht)).hasDerivWithinAt
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun t ht => by rw [(hp _).mpr (hf' t (Ico_subset_Icc_self ht)), norm_zero]) b ⟨hab, le_rfl⟩
  rw [zero_mul, norm_le_zero_iff, ← map_sub] at hb
  exact (hp _).mp hb

end ClosedSubspace

/-- The subspace of compact operators on `ℓ²(ℕ₀)`. -/
abbrev compactOps : Submodule ℂ (Ell2 →L[ℂ] Ell2) := compactOperator (RingHom.id ℂ) Ell2 Ell2

lemma isClosed_compactOps : IsClosed (compactOps : Set (Ell2 →L[ℂ] Ell2)) :=
  isClosed_setOf_isCompactOperator

lemma mem_compactOps {T : Ell2 →L[ℂ] Ell2} : T ∈ compactOps ↔ IsCompactOperator T := Iff.rfl

/-- `D_N` has finite rank, hence is compact. -/
theorem isCompactOperator_diagN : IsCompactOperator diagN := by
  have h : ∀ v : Ell2, IsCompactOperator
      ((ContinuousLinearMap.toSpanSingleton ℂ v).comp (innerSL ℂ v)) := fun v =>
    (isCompactOperator_of_finiteDimensional_range (ContinuousLinearMap.toSpanSingleton ℂ v)).comp_clm
      (innerSL ℂ v)
  exact ((h _).smul (2 : ℂ)).sub (h _)

/-- The curvature operator `Q_E = (1/4) ∫ b W^* D_N W dθ` is compact. -/
theorem isCompactOperator_curvatureOp (γ : ℝ → ℂ) (W : ℝ → Ell2 →L[ℂ] Ell2) :
    IsCompactOperator (curvatureOp γ W) := by
  rw [← mem_compactOps, curvatureOp]
  refine compactOps.smul_of_tower_mem _ ?_
  refine intervalIntegral_mem_of_isClosed _ isClosed_compactOps (fun θ => ?_) _ _
  refine compactOps.smul_of_tower_mem _ ?_
  rw [mem_compactOps]
  exact (isCompactOperator_diagN.clm_comp (star (W θ))).comp_clm (W θ)

/-- At energy `0` the transport is the identity. -/
theorem transport_zero_energy {γ : ℝ → ℂ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ 0 W) :
    W (2 * π) = 1 := by
  have h := hW.2 (2 * π) ⟨by positivity, le_rfl⟩
  have h0 : ∀ s, transportCoeff γ 0 s = 0 := fun s => by simp [transportCoeff]
  simpa [h0] using h

/-- **Lemma 4.7 (compactness of `V_E - I`).** For a closed Lipschitz curve and `E ≥ 0`, the
endpoint `V_E = W_E(L)` of the transport satisfies: `V_E - I` is compact. -/
theorem isCompactOperator_transport_sub_one {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) : IsCompactOperator ⇑(W (2 * π) - 1) := by
  rw [← mem_compactOps]
  have h2π : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  choose Ws hWs using fun E' : ℝ => transport_exists_of_lipschitz γ hK E'
  have hWE : W (2 * π) = Ws E (2 * π) := transport_unique_of_lipschitz γ hK E hW (hWs E) h2π
  rw [hWE]
  rcases eq_or_lt_of_le hE with rfl | hEpos
  · rw [transport_zero_energy (hWs 0), sub_self]; exact compactOps.zero_mem
  -- increments `V_E - V_δ` are compact for `0 < δ ≤ E`
  have hinc : ∀ δ ∈ Ioc 0 E, Ws E (2 * π) - Ws δ (2 * π) ∈ compactOps := by
    intro δ hδ
    refine sub_mem_of_hasDerivAt compactOps isClosed_compactOps hδ.2
      (fun t ht => hasDerivAt_transport_energy hK hclosed hWs (hδ.1.trans_le ht.1)) ?_
    intro t _
    refine compactOps.neg_mem (compactOps.smul_mem _ ?_)
    rw [mem_compactOps]
    exact (isCompactOperator_curvatureOp γ (Ws t)).clm_comp (Ws t (2 * π))
  -- let `δ → 0⁺`
  have hlim : Tendsto (fun δ => Ws E (2 * π) - Ws δ (2 * π)) (𝓝[>] 0)
      (𝓝 (Ws E (2 * π) - 1)) := by
    have h := tendsto_transport_energy hK hWs 0 h2π
    rw [transport_zero_energy (hWs 0)] at h
    exact (tendsto_const_nhds.sub h).mono_left nhdsWithin_le_nhds
  refine isClosed_compactOps.mem_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hEpos] with δ hδ
  exact hinc δ ⟨hδ.1, hδ.2.le⟩

/-- **Lemma 4.7 (compactness of `U_E - I`).** For a closed Lipschitz curve and `E ≥ 0`, the
monodromy `U_E = V_E^*` satisfies: `U_E - I` is compact. -/
theorem isCompactOperator_monodromy_sub_one {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) : IsCompactOperator ⇑(monodromy W - 1) := by
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have hVV : star (W (2 * π)) * W (2 * π) = 1 := (Unitary.mem_iff.mp hU).1
  have heq : monodromy W - 1 = -(star (W (2 * π)) * (W (2 * π) - 1)) := by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint, mul_sub, hVV, mul_one, neg_sub]
  rw [heq]
  exact ((isCompactOperator_transport_sub_one hK hclosed hE hW).clm_comp _).neg

end PolyaNeumann

end
