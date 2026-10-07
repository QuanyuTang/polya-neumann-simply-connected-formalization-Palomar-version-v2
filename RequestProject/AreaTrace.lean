module

public import RequestProject.Area

/-!
# Trace of the curvature operator (Lemma 4.7, `tr L_E = |Ω|/2`)

For a continuous unitary family `U` and a bounded measurable weight `b`, the operator
`∫₀^L b U^* D_N U dθ` has diagonal sum `∫₀^L b dθ` in the standard basis (`tr D_N = 1` and the
trace is invariant under unitary conjugation). Applied to `Q_E = (1/4) ∫ b W^* D_N W` and to
`L_E = V_E Q_E V_E^*`, this gives `tr Q_E = tr L_E = (1/4) ∫₀^L b`, where `b` is the signed area
density; Green's formula `∫₀^L b = 2|Ω|` (not formalized here) turns this into the paper's
`tr L_E = |Ω|/2`.

Mathlib has no trace-class operators, so the trace is written as the sum of the diagonal
entries in the standard basis `(eₙ)` of `ℓ²(ℕ₀)`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- `⟨y, D_N y⟩ = 2 |y₀|² - |y₁|²`. -/
lemma inner_diagN_self (y : Ell2) :
    inner ℂ y (diagN y) =
      ((2 * ‖inner ℂ (basisVec 0) y‖ ^ 2 - ‖inner ℂ (basisVec 1) y‖ ^ 2 : ℝ) : ℂ) := by
  simp only [diagN, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
    inner_sub_right, inner_smul_right, basisVec]
  rw [← inner_conj_symm y, ← inner_conj_symm y, Complex.mul_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Parseval for a row of an operator: `∑ₙ |⟨e_k, X eₙ⟩|² = ‖X^* e_k‖²`. -/
lemma hasSum_norm_inner_basisVec_sq_row (X : Ell2 →L[ℂ] Ell2) (k : ℕ) :
    HasSum (fun n => ‖inner ℂ (basisVec k) (X (basisVec n))‖ ^ 2)
      (‖ContinuousLinearMap.adjoint X (basisVec k)‖ ^ 2) := by
  set g := ContinuousLinearMap.adjoint X (basisVec k)
  have h : ∀ n, ‖inner ℂ (basisVec k) (X (basisVec n))‖ ^ 2 = ‖(g : ℕ → ℂ) n‖ ^ 2 := by
    intro n
    rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, basisVec, inner_single,
      RCLike.norm_conj]
  simp_rw [h]
  rw [← tsum_sq_eq_norm_sq]
  exact (summable_sq g).hasSum

lemma norm_adjoint_unitary_basisVec {U : Ell2 →L[ℂ] Ell2}
    (hU : U ∈ unitary (Ell2 →L[ℂ] Ell2)) (k : ℕ) :
    ‖ContinuousLinearMap.adjoint U (basisVec k)‖ = 1 := by
  have h1 : U * ContinuousLinearMap.adjoint U = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact (Unitary.mem_iff.mp hU).2
  have h2 : ‖ContinuousLinearMap.adjoint U (basisVec k)‖ ^ 2 = ‖basisVec k‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.mul_apply, h1,
      ContinuousLinearMap.one_apply]
  have h3 : ‖basisVec k‖ = 1 := by
    rw [basisVec, lp.norm_single (by norm_num)]; simp
  rw [h3, one_pow] at h2
  have := norm_nonneg (ContinuousLinearMap.adjoint U (basisVec k))
  nlinarith

/-- The diagonal sum of `∫₀^L b U^* D_N U dθ` is `∫₀^L b dθ`, for a continuous unitary family
`U` on `[0, L]` and a bounded measurable weight `b`. -/
theorem hasSum_trace_integral_conj_diagN {U : ℝ → Ell2 →L[ℂ] Ell2}
    (hU : ContinuousOn U (Icc 0 (2 * π)))
    (hunit : ∀ θ ∈ Icc 0 (2 * π), U θ ∈ unitary (Ell2 →L[ℂ] Ell2))
    {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) :
    HasSum (fun n => inner ℂ (basisVec n)
        ((∫ θ in (0 : ℝ)..(2 * π), b θ • (star (U θ) * diagN * U θ)) (basisVec n)))
      ((∫ θ in (0 : ℝ)..(2 * π), b θ : ℝ) : ℂ) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have hsub : uIoc 0 (2 * π) ⊆ Icc 0 (2 * π) := by
    rw [uIoc_of_le hπ]; exact Ioc_subset_Icc_self
  have hint := intervalIntegrable_conj_diagN hU hunit hb hbB
  set a : ℕ → ℕ → ℝ → ℝ := fun k n θ => ‖inner ℂ (basisVec k) (U θ (basisVec n))‖ ^ 2 with ha
  set F : ℕ → ℝ → ℝ := fun n θ => b θ * (2 * a 0 n θ - a 1 n θ) with hF
  have hpt : ∀ n θ, inner ℂ (basisVec n) ((b θ • (star (U θ) * diagN * U θ)) (basisVec n)) =
      ((F n θ : ℝ) : ℂ) := by
    intro n θ
    rw [ContinuousLinearMap.smul_apply, real_smul_eq_coe_smul_ell2, inner_smul_right, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_diagN_self]
    simp only [hF, ha]
    push_cast
    ring
  have h1 : ∀ n, inner ℂ (basisVec n)
      ((∫ θ in (0 : ℝ)..(2 * π), b θ • (star (U θ) * diagN * U θ)) (basisVec n)) =
      ((∫ θ in (0 : ℝ)..(2 * π), F n θ : ℝ) : ℂ) := by
    intro n
    set L : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
      (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 (basisVec n))
    have hL : ∀ X, L X = inner ℂ (basisVec n) (X (basisVec n)) := fun X => rfl
    rw [← hL, ← L.intervalIntegral_comp_comm hint, ← intervalIntegral.integral_ofReal]
    congr 1
    funext θ
    rw [hL, hpt]
  simp_rw [h1]
  refine Complex.hasSum_ofReal.mpr ?_
  have hsum : ∀ k θ, θ ∈ Icc 0 (2 * π) → HasSum (fun n => a k n θ) 1 := by
    intro k θ hθ
    have := hasSum_norm_inner_basisVec_sq_row (U θ) k
    rwa [norm_adjoint_unitary_basisVec (hunit θ hθ), one_pow] at this
  have hac : ∀ k n, ContinuousOn (a k n) (Icc 0 (2 * π)) := fun k n =>
    ((continuousOn_const.inner (hU.clm_apply continuousOn_const)).norm).pow 2
  have hbound : ∀ n θ, ‖F n θ‖ ≤ |b θ| * (2 * a 0 n θ + a 1 n θ) := by
    intro n θ
    have h0 : 0 ≤ a 0 n θ := by positivity
    have h1' : 0 ≤ a 1 n θ := by positivity
    rw [Real.norm_eq_abs, abs_mul]
    gcongr
    rw [abs_le]
    constructor <;> linarith
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n θ => |b θ| * (2 * a 0 n θ + a 1 n θ)) (fun n => ?_)
    (fun n => Eventually.of_forall fun θ _ => hbound n θ)
    (Eventually.of_forall fun θ hθ =>
      (((hsum 0 θ (hsub hθ)).mul_left 2).add (hsum 1 θ (hsub hθ))).mul_left |b θ| |>.summable)
    ?_ (Eventually.of_forall fun θ hθ => ?_)
  · exact hb.restrict.mul ((((hac 0 n).mono hsub).aestronglyMeasurable measurableSet_uIoc).const_mul
      2 |>.sub (((hac 1 n).mono hsub).aestronglyMeasurable measurableSet_uIoc))
  · have hbi : IntervalIntegrable (fun θ => |b θ| * 3) volume 0 (2 * π) := by
      refine (IntervalIntegrable.mono_fun' (g := fun _ => B) intervalIntegrable_const
        hb.norm.restrict ?_).mul_const 3
      rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      exact Eventually.of_forall fun θ hθ => by rw [norm_norm]; exact hbB θ (hsub hθ)
    refine hbi.congr fun θ hθ => ?_
    have := ((((hsum 0 θ (hsub hθ)).mul_left 2).add (hsum 1 θ (hsub hθ))).mul_left |b θ|).tsum_eq
    rw [this]
    ring
  · have := (((hsum 0 θ (hsub hθ)).mul_left 2).sub (hsum 1 θ (hsub hθ))).mul_left (b θ)
    convert this using 1
    ring

/-- Lemma 4.7: `tr Q_E = (1/4) ∫₀^L b`, with `b` the signed area density (the trace being the
diagonal sum in the standard basis). -/
theorem hasSum_trace_curvatureOp {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    HasSum (fun n => inner ℂ (basisVec n) (curvatureOp γ W (basisVec n)))
      (((1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ : ℝ) : ℂ) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  have h := (hasSum_trace_integral_conj_diagN hW.1 (fun θ hθ => transport_mem_unitary hK hW hθ)
    (areaDensity_aestronglyMeasurable hK.continuous)
    (fun θ hθ => abs_areaDensity_le hK hR hθ)).mul_left ((1 / 4 : ℝ) : ℂ)
  push_cast at h ⊢
  convert h using 2 with n
  rw [curvatureOp, ContinuousLinearMap.smul_apply, real_smul_eq_coe_smul_ell2, inner_smul_right]
  push_cast
  ring

/-- **Lemma 4.7 (trace formula).** For a closed Lipschitz curve and `E > 0`, the operator
`L_E = -i U_E^* ∂_E U_E` has trace `(1/4) ∫₀^L b`, where `b = Im(conj(γ - γ(0)) γ')` is the
signed area density (by Green's formula, `∫₀^L b = 2|Ω|` for a positively oriented boundary
parametrization, which gives the paper's `tr L_E = |Ω|/2`; Green's formula itself is not
formalized here). The trace is the diagonal sum in the standard basis. -/
theorem hasSum_trace_monodromy_logDeriv_energy {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) :
    HasSum (fun n => inner ℂ (basisVec n)
        ((-(Complex.I • (star (monodromy (Ws E)) * deriv (fun E => monodromy (Ws E)) E)))
          (basisVec n)))
      (((1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ : ℝ) : ℂ) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  rw [monodromy_logDeriv_energy hK hclosed hWs hE]
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  set W := Ws E
  set V := W (2 * π)
  have hV : V ∈ unitary (Ell2 →L[ℂ] Ell2) := transport_mem_unitary hK (hWs E) ⟨hπ, le_rfl⟩
  set U : ℝ → Ell2 →L[ℂ] Ell2 := fun θ => W θ * star V
  have hU : ContinuousOn U (Icc 0 (2 * π)) := (hWs E).1.mul continuousOn_const
  have hUu : ∀ θ ∈ Icc 0 (2 * π), U θ ∈ unitary (Ell2 →L[ℂ] Ell2) := fun θ hθ =>
    Submonoid.mul_mem _ (transport_mem_unitary hK (hWs E) hθ) (Unitary.star_mem hV)
  have hint := intervalIntegrable_conj_diagN (hWs E).1
    (fun θ hθ => transport_mem_unitary hK (hWs E) hθ)
    (areaDensity_aestronglyMeasurable hK.continuous) (fun θ hθ => abs_areaDensity_le hK hR hθ)
  set L : (Ell2 →L[ℂ] Ell2) →L[ℝ] (Ell2 →L[ℂ] Ell2) :=
    (ContinuousLinearMap.mul ℝ (Ell2 →L[ℂ] Ell2) V).comp
      ((ContinuousLinearMap.mul ℝ (Ell2 →L[ℂ] Ell2)).flip (star V))
  have hL : ∀ X, L X = V * (X * star V) := fun X => rfl
  have hconj : V * curvatureOp γ W * star V = (1 / 4 : ℝ) •
      ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ • (star (U θ) * diagN * U θ) := by
    rw [curvatureOp, mul_smul_comm, smul_mul_assoc, mul_assoc, ← hL,
      ← L.intervalIntegral_comp_comm hint]
    congr 1
    congr 1
    funext θ
    rw [hL, smul_mul_assoc, mul_smul_comm]
    congr 1
    simp only [U, W, star_mul, star_star, mul_assoc]
  rw [hconj]
  have h := (hasSum_trace_integral_conj_diagN hU hUu
    (areaDensity_aestronglyMeasurable hK.continuous)
    (fun θ hθ => abs_areaDensity_le hK hR hθ)).mul_left ((1 / 4 : ℝ) : ℂ)
  push_cast at h ⊢
  convert h using 2 with n
  rw [Pi.smul_apply, real_smul_eq_coe_smul_ell2, inner_smul_right]
  push_cast
  ring

end PolyaNeumann

end
