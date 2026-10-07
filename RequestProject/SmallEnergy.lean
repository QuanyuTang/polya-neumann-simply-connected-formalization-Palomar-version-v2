module

public import RequestProject.CutPhase

/-!
# Small energies: the principal phase sum (abstract part of Lemmas 8.7–8.8)

* The trace-norm bound of Lemma 4.7 is linear in the energy:
  `‖U_E - I‖_{𝒮₁} ≤ C E` for a closed Lipschitz curve (`exists_linear_traceBound_monodromyAt`).
* For a unitary `U` with `U - I` compact and trace-norm bound `C`, the principal phases
  (the cut phase sum with the cut through `-1`) satisfy `∑ mult(z) |arg z| ≤ (π/2) C`
  (`cutPhaseSum_pi_bound`), and if `C < 2` then `-1` is not an eigenvalue
  (`not_eigen_neg_one_of_traceBound`).
-/

@[expose] public section

noncomputable section

open scoped Real
open MeasureTheory Filter Topology Set

namespace PolyaNeumann

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The principal argument is bounded by `(π/2) |z - 1|` on the unit circle. -/
lemma abs_arg_le_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    |Complex.arg z| ≤ π / 2 * ‖z - 1‖ := by
  set t := Complex.arg z with ht
  have hexp : z = Complex.exp (Complex.I * t) := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, Complex.ofReal_one, one_mul, mul_comm] at this
    exact this.symm
  have hlo := Complex.neg_pi_lt_arg z
  have hhi := Complex.arg_le_pi z
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have hu0 : 0 ≤ |t| / 2 := by positivity
  have hu1 : |t| / 2 ≤ π / 2 := by
    have : |t| ≤ π := abs_le.mpr ⟨by linarith, hhi⟩
    linarith
  have hs := Real.mul_le_sin hu0 hu1
  have hsin : |Real.sin (t / 2)| = Real.sin (|t| / 2) := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    · rw [abs_of_nonpos h, neg_div, Real.sin_neg, abs_of_nonpos]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -(t / 2)) (by linarith) (by linarith)
      rw [Real.sin_neg] at this; linarith
  rw [hsin]
  have hpi := Real.pi_pos
  have h2 : 2 / π * (|t| / 2) * π = |t| := by field_simp
  nlinarith

/-- With the cut through `-1`, the cut argument is the principal argument up to sign. -/
lemma abs_argCut_pi (z : ℂ) : |argCut π z| = |Complex.arg z| := by
  have hlo := Complex.neg_pi_lt_arg z
  have hhi := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  unfold argCut argNeg
  by_cases ha : Complex.arg z < 0
  · rw [if_pos ha, if_neg (by linarith)]
  · rw [if_neg ha]
    rcases hhi.lt_or_eq with h | h
    · rw [if_pos (by linarith)]; ring_nf
    · rw [if_neg (by linarith), h, abs_of_neg (by linarith), abs_of_pos hpi]; ring

/-- Finite partial sums of `∑_{z ≠ 1} mult(z) |z - 1|` are bounded by a trace-norm bound. -/
lemma sum_eigenMult_mul_norm_le {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {C : ℝ} (hT : TraceBound (U - 1) C)
    (s : Finset {z : ℂ // z ≠ 1}) :
    ∑ z ∈ s, (eigenMult U z : ℝ) * ‖(z : ℂ) - 1‖ ≤ C := by
  classical
  obtain ⟨e, he, heig⟩ := exists_orthonormal_eigen_family hU hC s
  have key := hT.sum_norm_le _ e e he he
  have hterm : ∀ p : (Σ z : s, Fin (eigenMult U z)),
      ‖inner ℂ (e p) ((U - 1) (e p))‖ = ‖((p.1 : {z : ℂ // z ≠ 1}) : ℂ) - 1‖ := by
    intro p
    have hs : ∀ (c : ℂ) (v : H), c • v - v = (c - 1) • v := fun c v => by
      rw [sub_smul, one_smul]
    rw [ContinuousLinearMap.sub_apply, heig, ContinuousLinearMap.one_apply, hs,
      inner_smul_right, inner_self_eq_norm_sq_to_K, he.1 p]
    simp
  simp only [hterm] at key
  refine le_trans (le_of_eq ?_) key
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_coe_sort s]

/-- **Lemma 8.7 (summability of the principal phases, abstract form).** For a unitary `U` with
`U - I` compact and trace-norm bound `C`, the principal phases (cut through `-1`) are absolutely
summable, with `|∑ mult(z) arg z| ≤ (π/2) C`. -/
lemma cutPhaseSum_pi_bound {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {C : ℝ} (hT : TraceBound (U - 1) C) :
    Summable (cutPhaseTerm π U) ∧ |cutPhaseSum π U| ≤ π / 2 * C := by
  set g : {z : ℂ // z ≠ 1} → ℝ := fun z => (eigenMult U z : ℝ) * ‖(z : ℂ) - 1‖ with hg
  have hgnn : ∀ z, 0 ≤ g z := fun z => by positivity
  have hgs : Summable g := summable_of_sum_le hgnn (sum_eigenMult_mul_norm_le hU hC hT)
  have hgt : ∑' z, g z ≤ C := Real.tsum_le_of_sum_le hgnn (sum_eigenMult_mul_norm_le hU hC hT)
  have hb : ∀ z, ‖cutPhaseTerm π U z‖ ≤ π / 2 * g z := by
    intro z
    rw [cutPhaseTerm, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
    by_cases hm : eigenMult U z = 0
    · rw [hm, Nat.cast_zero, zero_mul]; exact mul_nonneg (by positivity) (hgnn z)
    have hm' : 0 < Module.finrank ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
      Nat.pos_of_ne_zero hm
    haveI := Module.finite_of_finrank_pos hm'
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hm'
    have hv0' : v ≠ 0 := fun h => hv0 (by simp [h])
    have hz1 : ‖(z : ℂ)‖ = 1 :=
      norm_eq_one_of_eigen hU hv0' (Module.End.mem_eigenspace_iff.mp hv)
    rw [abs_argCut_pi]
    calc (eigenMult U z : ℝ) * |Complex.arg z|
        ≤ (eigenMult U z : ℝ) * (π / 2 * ‖(z : ℂ) - 1‖) :=
          mul_le_mul_of_nonneg_left (abs_arg_le_of_norm_eq_one hz1) (Nat.cast_nonneg _)
      _ = π / 2 * g z := by rw [hg]; ring
  have hs : Summable (cutPhaseTerm π U) := Summable.of_norm_bounded (hgs.mul_left (π / 2)) hb
  refine ⟨hs, ?_⟩
  calc |cutPhaseSum π U| = ‖∑' z, cutPhaseTerm π U z‖ := by rw [cutPhaseSum, Real.norm_eq_abs]
    _ ≤ ∑' z, ‖cutPhaseTerm π U z‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' z, π / 2 * g z := Summable.tsum_le_tsum hb hs.norm (hgs.mul_left _)
    _ = π / 2 * ∑' z, g z := tsum_mul_left
    _ ≤ π / 2 * C := mul_le_mul_of_nonneg_left hgt (by positivity)

/-- If `U` is unitary, `U - I` is compact and has trace-norm bound `C < 2`, then `-1` is not an
eigenvalue of `U`. -/
lemma not_eigen_neg_one_of_traceBound {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {C : ℝ} (hT : TraceBound (U - 1) C) (hC2 : C < 2)
    {v : H} (hv : v ≠ 0) : U v ≠ (-1 : ℂ) • v := by
  intro hUv
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  haveI := finiteDimensional_eigenspace hC hne
  have hpos : 0 < eigenMult U (-1) := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hUv⟩, fun h => hv (by simpa using h)⟩
  have h := sum_eigenMult_mul_norm_le hU hC hT {⟨-1, hne⟩}
  rw [Finset.sum_singleton] at h
  have h2 : ‖(-1 : ℂ) - 1‖ = 2 := by norm_num
  simp only at h
  rw [h2] at h
  have : (1 : ℝ) ≤ eigenMult U (-1) := by exact_mod_cast hpos
  linarith

end General

/-- **Lemma 4.7 (trace-norm bound, linear in the energy).** For a closed Lipschitz curve there
is `C ≥ 0` such that, for every `E ≥ 0`, the transport endpoint satisfies the trace-norm bound
`‖V_E - I‖_{𝒮₁} ≤ C E`. -/
theorem exists_linear_traceBound_transport {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E, 0 ≤ E → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      TraceBound (W (2 * π) - 1) (C * E) := by
  have h2π : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  set Cq : ℝ := 1 / 4 * ((R * K * 3) * (2 * π)) with hCq
  choose Ws hWs using fun E' : ℝ => transport_exists_of_lipschitz γ hK E'
  have hCq0 : 0 ≤ Cq := (traceBound_curvatureOp hK hR (hWs 0)).nonneg
  refine ⟨Cq, hCq0, fun E hE W hW => ?_⟩
  have hWE : W (2 * π) = Ws E (2 * π) := transport_unique_of_lipschitz γ hK E hW (hWs E) h2π
  rw [hWE]
  rcases eq_or_lt_of_le hE with rfl | hEpos
  · rw [transport_zero_energy (hWs 0), sub_self, mul_zero]; exact TraceBound.zero
  have hinc : ∀ δ ∈ Ioc 0 E, TraceBound (Ws E (2 * π) - Ws δ (2 * π)) (Cq * (E - δ)) := by
    intro δ hδ
    refine TraceBound.sub_of_hasDerivAt (g := fun E' => Ws E' (2 * π))
      (g' := fun t => -(Complex.I • (Ws t (2 * π) * curvatureOp γ (Ws t)))) hδ.2
      (fun t ht => hasDerivAt_transport_energy hK hclosed hWs (hδ.1.trans_le ht.1)) ?_
    intro t _
    have h := ((traceBound_curvatureOp hK hR (hWs t)).unitary_mul
      (transport_mem_unitary hK (hWs t) h2π)).smul Complex.I
    rw [Complex.norm_I, one_mul] at h
    exact h.neg
  have hlim : Tendsto (fun δ => Ws E (2 * π) - Ws δ (2 * π)) (𝓝[>] 0)
      (𝓝 (Ws E (2 * π) - 1)) := by
    have h := tendsto_transport_energy hK hWs 0 h2π
    rw [transport_zero_energy (hWs 0)] at h
    exact (tendsto_const_nhds.sub h).mono_left nhdsWithin_le_nhds
  refine TraceBound.of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hEpos] with δ hδ
  exact (hinc δ ⟨hδ.1, hδ.2.le⟩).mono (mul_le_mul_of_nonneg_left (by linarith [hδ.1]) hCq0)

/-- **Lemma 4.7 (trace-norm bound for `U_E - I`, linear in the energy).** For a closed
Lipschitz curve there is `C ≥ 0` with `‖U_E - I‖_{𝒮₁} ≤ C E` for every `E ≥ 0`. -/
theorem exists_linear_traceBound_monodromyAt {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E, 0 ≤ E → TraceBound (monodromyAt γ E - 1) (C * E) := by
  obtain ⟨C, hC0, hC⟩ := exists_linear_traceBound_transport hK hclosed
  refine ⟨C, hC0, fun E hE => ?_⟩
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have hVV : star (W (2 * π)) * W (2 * π) = 1 := (Unitary.mem_iff.mp hU).1
  have heq : monodromy W - 1 = -(star (W (2 * π)) * (W (2 * π) - 1)) := by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint, mul_sub, hVV, mul_one, neg_sub]
  rw [monodromyAt_eq hK hW, heq]
  exact ((hC E hE W hW).unitary_mul (Unitary.star_mem hU)).neg

end PolyaNeumann
