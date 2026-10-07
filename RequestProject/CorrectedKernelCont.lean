module

public import RequestProject.KernelIdentity

/-!
# Continuity of the corrected kernel in the energy (Lemma 6.6, continuity part)

For a family of transports `W_E` of a Lipschitz curve and an energy `E₀` with
`c_{E₀} = (V_{E₀}^* - I) e₀ ≠ 0`, the correction `B_E` depends continuously on `E` near `E₀`
(`tendsto_cutBE_energy`), and the corrected kernel `r_E` of `CorrectedKernel.lean` converges to
`r_{E₀}` uniformly on the square `[0, L]²` as `E → E₀` (`tendsto_correctedKernel_energy`).
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

/-- Continuity of `(d, c) ↦ rankOne d c`. -/
lemma tendsto_rankOne {α : Type*} {l : Filter α} {d c : α → Ell2} {d₀ c₀ : Ell2}
    (hd : Tendsto d l (𝓝 d₀)) (hc : Tendsto c l (𝓝 c₀)) :
    Tendsto (fun x => InnerProductSpace.rankOne ℂ (d x) (c x)) l
      (𝓝 (InnerProductSpace.rankOne ℂ d₀ c₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ x, InnerProductSpace.rankOne ℂ (d x) (c x) - InnerProductSpace.rankOne ℂ d₀ c₀ =
      InnerProductSpace.rankOne ℂ (d x - d₀) (c x) +
        InnerProductSpace.rankOne ℂ d₀ (c x - c₀) := fun x => by
    rw [map_sub, map_sub, ContinuousLinearMap.sub_apply]
    abel
  have hb : ∀ x, ‖InnerProductSpace.rankOne ℂ (d x) (c x) - InnerProductSpace.rankOne ℂ d₀ c₀‖ ≤
      ‖d x - d₀‖ * ‖c x‖ + ‖d₀‖ * ‖c x - c₀‖ := fun x => by
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne]
  have h1 : Tendsto (fun x => ‖d x - d₀‖ * ‖c x‖ + ‖d₀‖ * ‖c x - c₀‖) l (𝓝 0) := by
    have hd' := (tendsto_iff_norm_sub_tendsto_zero.mp hd)
    have hc' := (tendsto_iff_norm_sub_tendsto_zero.mp hc)
    have := (hd'.mul hc.norm).add (hc'.const_mul ‖d₀‖)
    simpa using this
  exact squeeze_zero (fun _ => norm_nonneg _) hb h1

/-- Continuity of the correction `cutB c d` at a point with `c ≠ 0`. -/
lemma tendsto_cutB {α : Type*} {l : Filter α} {c d : α → Ell2} {c₀ d₀ : Ell2}
    (hc : Tendsto c l (𝓝 c₀)) (hd : Tendsto d l (𝓝 d₀)) (hc₀ : c₀ ≠ 0) :
    Tendsto (fun x => cutB (c x) (d x)) l (𝓝 (cutB c₀ d₀)) := by
  have hn2 : Tendsto (fun x => ((‖c x‖ ^ 2 : ℝ) : ℂ)) l (𝓝 ((‖c₀‖ ^ 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (hc.norm.pow 2)
  have hn4 : Tendsto (fun x => ((‖c x‖ ^ 4 : ℝ) : ℂ)) l (𝓝 ((‖c₀‖ ^ 4 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (hc.norm.pow 4)
  have h2 : ((‖c₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
    exact_mod_cast (by positivity : (0 : ℝ) < ‖c₀‖ ^ 2).ne'
  have h4 : ((‖c₀‖ ^ 4 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
    exact_mod_cast (by positivity : (0 : ℝ) < ‖c₀‖ ^ 4).ne'
  unfold cutB
  refine ((hn2.inv₀ h2).smul ((tendsto_rankOne hd hc).add (tendsto_rankOne hc hd))).sub
    (((hc.inner hd).div hn4 h4).smul (tendsto_rankOne hc hc))

variable {γ : ℝ → ℂ} {K : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}

/-- Continuity of `B_E` in the energy at `E₀` when `c_{E₀} ≠ 0`. -/
theorem tendsto_cutBE_energy (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E))
    (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    Tendsto (fun E => cutBE (Ws E)) (𝓝 E₀) (𝓝 (cutBE (Ws E₀))) := by
  have h2π : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hV := tendsto_transport_energy hK hWs E₀ h2π
  have hVa : Tendsto (fun E => ContinuousLinearMap.adjoint (Ws E (2 * π)) (basisVec 0)) (𝓝 E₀)
      (𝓝 (ContinuousLinearMap.adjoint (Ws E₀ (2 * π)) (basisVec 0))) :=
    ((continuous_eval_const (basisVec 0)).tendsto _).comp
      (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.tendsto _).comp
        hV)
  have hC : Tendsto (fun E => cutC (Ws E (2 * π)) (basisVec 0)) (𝓝 E₀)
      (𝓝 (cutC (Ws E₀ (2 * π)) (basisVec 0))) := by
    unfold cutC; exact hVa.sub tendsto_const_nhds
  have hS : Tendsto (fun E => Complex.I • cutS (Ws E (2 * π)) (basisVec 0)) (𝓝 E₀)
      (𝓝 (Complex.I • cutS (Ws E₀ (2 * π)) (basisVec 0))) := by
    unfold cutS; exact (tendsto_const_nhds.add hVa).const_smul _
  exact tendsto_cutB hC hS hc

/-- Perturbation bound for the kernels `⟨e₀, P X Q^* e₀⟩` with contractions `P, Q, P', Q'`. -/
lemma norm_inner_sandwich_sub_le {P Q P' Q' X X' : Ell2 →L[ℂ] Ell2}
    (hP' : ‖P'‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖⟪basisVec 0, P (X (ContinuousLinearMap.adjoint Q (basisVec 0)))⟫_ℂ -
        ⟪basisVec 0, P' (X' (ContinuousLinearMap.adjoint Q' (basisVec 0)))⟫_ℂ‖ ≤
      ‖P - P'‖ * ‖X‖ + ‖X - X'‖ + ‖X'‖ * ‖Q - Q'‖ := by
  set u := ContinuousLinearMap.adjoint Q (basisVec 0)
  set u' := ContinuousLinearMap.adjoint Q' (basisVec 0)
  have hu : ‖u‖ ≤ 1 := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map, norm_basisVec_zero, mul_one]; exact hQ
  have huu : ‖u - u'‖ ≤ ‖Q - Q'‖ := by
    simp only [u, u', ← ContinuousLinearMap.sub_apply, ← map_sub]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map, norm_basisVec_zero, mul_one]
  rw [← inner_sub_right]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [norm_basisVec_zero, one_mul]
  have e : P (X u) - P' (X' u') = (P - P') (X u) + P' ((X - X') u) + P' (X' (u - u')) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
  rw [e]
  refine (norm_add₃_le).trans ?_
  have t1 : ‖(P - P') (X u)‖ ≤ ‖P - P'‖ * ‖X‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖P - P'‖ * ‖X u‖ ≤ ‖P - P'‖ * (‖X‖ * 1) := by
          gcongr; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
      _ = _ := by ring
  have t2 : ‖P' ((X - X') u)‖ ≤ ‖X - X'‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖P'‖ * ‖(X - X') u‖ ≤ 1 * (‖X - X'‖ * 1) := by
          gcongr; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
      _ = _ := by ring
  have t3 : ‖P' (X' (u - u'))‖ ≤ ‖X'‖ * ‖Q - Q'‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖P'‖ * ‖X' (u - u')‖ ≤ 1 * (‖X'‖ * ‖Q - Q'‖) := by
          gcongr; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
      _ = _ := by ring
  linarith

/-- Pointwise perturbation bound for the corrected kernel between two transports. -/
lemma norm_correctedKernel_sub_correctedKernel_le {W W' : ℝ → Ell2 →L[ℂ] Ell2} {θ t : ℝ}
    (hWθ : ‖W θ‖ ≤ 1) (hW't : ‖W' t‖ ≤ 1) :
    ‖correctedKernel W' θ t - correctedKernel W θ t‖ ≤
      (‖W' θ - W θ‖ + ‖W' t - W t‖) * (1 + ‖cutBE W'‖ + ‖cutBE W‖) +
        ‖cutBE W' - cutBE W‖ := by
  have k1 := norm_inner_sandwich_sub_le (X := 1) (X' := 1) (P := W' θ) (Q := W' t)
    (P' := W θ) (Q' := W t) hWθ hW't
  have k2 := norm_inner_sandwich_sub_le (X := cutBE W') (X' := cutBE W) (P := W' θ) (Q := W' t)
    (P' := W θ) (Q' := W t) hWθ hW't
  simp only [ContinuousLinearMap.one_apply, sub_self, norm_zero, add_zero] at k1
  have hone : ‖(1 : Ell2 →L[ℂ] Ell2)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  have e : correctedKernel W' θ t - correctedKernel W θ t =
      Complex.I * Real.sign (θ - t) * (volterraKernel W' θ t - volterraKernel W θ t) +
      (⟪basisVec 0, W' θ (cutBE W' (ContinuousLinearMap.adjoint (W' t) (basisVec 0)))⟫_ℂ -
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W t) (basisVec 0)))⟫_ℂ) := by
    simp only [correctedKernel]; ring
  have hs : ‖Complex.I * (Real.sign (θ - t) : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_real_sign_le _
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hk : ‖Complex.I * Real.sign (θ - t) * (volterraKernel W' θ t - volterraKernel W θ t)‖ ≤
      ‖W' θ - W θ‖ * 1 + 1 * ‖W' t - W t‖ := by
    rw [norm_mul]
    calc _ ≤ 1 * ‖volterraKernel W' θ t - volterraKernel W θ t‖ := by gcongr
      _ ≤ ‖W' θ - W θ‖ * ‖(1 : Ell2 →L[ℂ] Ell2)‖ + ‖(1 : Ell2 →L[ℂ] Ell2)‖ * ‖W' t - W t‖ := by
          rw [one_mul]; unfold volterraKernel; exact k1
      _ ≤ _ := by gcongr
  have hB := norm_nonneg (cutBE W')
  have hB' := norm_nonneg (cutBE W)
  have h1 := norm_nonneg (W' θ - W θ)
  have h2 := norm_nonneg (W' t - W t)
  nlinarith

/-- The uniform transport perturbation bound of `Area.lean`, as a function of the energy. -/
def transportDist (K : NNReal) (R E₀ E : ℝ) : ℝ :=
  |Real.sqrt E₀ - Real.sqrt E| * shiftConst * R *
    (1 + 2 * π * ((Real.sqrt E + Real.sqrt E₀) * shiftConst * K))

lemma tendsto_transportDist (K : NNReal) (R E₀ : ℝ) :
    Tendsto (transportDist K R E₀) (𝓝 E₀) (𝓝 0) := by
  have hc : Continuous (transportDist K R E₀) := by unfold transportDist; fun_prop
  have := hc.tendsto E₀
  simpa [transportDist] using this

/-- **Lemma 6.6 (continuity in the energy).** If `c_{E₀} ≠ 0`, the corrected kernel `r_E`
converges to `r_{E₀}` uniformly on `[0, L]²` as `E → E₀`. -/
theorem tendsto_correctedKernel_energy (hK : LipschitzWith K γ)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ E in 𝓝 E₀, ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π),
      ‖correctedKernel (Ws E) θ t - correctedKernel (Ws E₀) θ t‖ < ε := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  have hB := tendsto_cutBE_energy hK hWs E₀ hc
  have hBn : Tendsto (fun E => ‖cutBE (Ws E) - cutBE (Ws E₀)‖) (𝓝 E₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hB
  have hD := tendsto_transportDist K R E₀
  have hlim : Tendsto (fun E => (transportDist K R E₀ E + transportDist K R E₀ E) *
      (1 + ‖cutBE (Ws E)‖ + ‖cutBE (Ws E₀)‖) + ‖cutBE (Ws E) - cutBE (Ws E₀)‖)
      (𝓝 E₀) (𝓝 0) := by
    have := ((hD.add hD).mul (((tendsto_const_nhds (x := (1 : ℝ))).add hB.norm).add
      (tendsto_const_nhds (x := ‖cutBE (Ws E₀)‖)))).add hBn
    simpa only [add_zero, zero_mul] using this
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with E hE θ hθ t ht
  refine lt_of_le_of_lt ?_ hE
  refine (norm_correctedKernel_sub_correctedKernel_le (norm_transport_le_one hK (hWs E₀) hθ)
    (norm_transport_le_one hK (hWs E) ht)).trans ?_
  have d1 : ‖Ws E θ - Ws E₀ θ‖ ≤ transportDist K R E₀ E :=
    norm_transport_sub_le hK hR (hWs E₀) (hWs E) hθ
  have d2 : ‖Ws E t - Ws E₀ t‖ ≤ transportDist K R E₀ E :=
    norm_transport_sub_le hK hR (hWs E₀) (hWs E) ht
  have hpos : 0 ≤ 1 + ‖cutBE (Ws E)‖ + ‖cutBE (Ws E₀)‖ := by positivity
  gcongr

end PolyaNeumann
