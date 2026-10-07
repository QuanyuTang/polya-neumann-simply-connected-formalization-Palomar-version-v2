module

public import RequestProject.SmallKernel

/-!
# Lemma 8.6 (negative index at small energy): the reduction to a Schur complement

For a bounded operator `U` on `ℓ²` put

  `F(w) = -4 Im ⟨w, U w⟩`,   `B(x, w) = 2i ⟨x, (U - U^*) w⟩`,

so that `B` is a Hermitian form with `B(w, w) = F(w)`; on Herglotz data `F` is the Herglotz form
(`herglotzForm_eq_im`). If `F(x) < 0`, the Schur complement

  `C(w) = F(w) - |B(x, w)|² / F(x)`

is invariant under `w ↦ w + t x` (`imSchur_add_smul`), and `C ≥ 0` on a dense set forces
`F ≥ 0` on the closed hyperplane `{B(x, ·) = 0}` (`nonneg_of_imSchur_nonneg`): this is the
index count `ind₋ 𝒜_E ≤ 1` of Lemma 8.6.

The analytic input (Lemmas 8.2–8.5, proved in `SmallEnergyCore.lean`) is `small_energy_schur_core`: for small `E > 0`,
`F(e₀) < 0`, and every finitely supported `w` can be shifted along `e₀` to a vector on which
`C ≥ 0`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The form `F(w) = -4 Im ⟨w, U w⟩`. -/
def imForm (U : Ell2 →L[ℂ] Ell2) (w : Ell2) : ℝ := -4 * (⟪w, U w⟫_ℂ).im

/-- The Hermitian form `B(x, w) = 2i ⟨x, (U - U^*) w⟩`. -/
def imPair (U : Ell2 →L[ℂ] Ell2) (x w : Ell2) : ℂ :=
  2 * Complex.I * ⟪x, (U - ContinuousLinearMap.adjoint U) w⟫_ℂ

/-- The Schur complement `C(w) = F(w) - |B(x, w)|² / F(x)`. -/
def imSchur (U : Ell2 →L[ℂ] Ell2) (x w : Ell2) : ℝ :=
  imForm U w - ‖imPair U x w‖ ^ 2 / imForm U x

lemma imPair_self (U : Ell2 →L[ℂ] Ell2) (w : Ell2) : imPair U w w = imForm U w := by
  unfold imPair imForm
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  have hz : ⟪U w, w⟫_ℂ = conj ⟪w, U w⟫_ℂ := (inner_conj_symm _ _).symm
  rw [hz]
  generalize ⟪w, U w⟫_ℂ = z
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

lemma imPair_conj (U : Ell2 →L[ℂ] Ell2) (x w : Ell2) : imPair U w x = conj (imPair U x w) := by
  unfold imPair
  have h : ⟪w, (U - ContinuousLinearMap.adjoint U) x⟫_ℂ =
      -conj ⟪x, (U - ContinuousLinearMap.adjoint U) w⟫_ℂ := by
    rw [inner_conj_symm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    ring
  rw [h, map_mul, map_mul, Complex.conj_I, map_ofNat]
  ring

lemma imPair_add_right (U : Ell2 →L[ℂ] Ell2) (x v w : Ell2) :
    imPair U x (v + w) = imPair U x v + imPair U x w := by
  unfold imPair; rw [map_add, inner_add_right]; ring

lemma imPair_smul_right (U : Ell2 →L[ℂ] Ell2) (x w : Ell2) (t : ℂ) :
    imPair U x (t • w) = t * imPair U x w := by
  unfold imPair; rw [map_smul, inner_smul_right]; ring

lemma imPair_add_left (U : Ell2 →L[ℂ] Ell2) (x v w : Ell2) :
    imPair U (v + w) x = imPair U v x + imPair U w x := by
  unfold imPair; rw [inner_add_left]; ring

lemma imPair_smul_left (U : Ell2 →L[ℂ] Ell2) (x w : Ell2) (t : ℂ) :
    imPair U (t • w) x = conj t * imPair U w x := by
  unfold imPair; rw [inner_smul_left]; ring

/-- The Schur complement is invariant under `w ↦ w + t x`. -/
lemma imSchur_add_smul (U : Ell2 →L[ℂ] Ell2) {x : Ell2} (hx : imForm U x ≠ 0) (w : Ell2)
    (t : ℂ) : imSchur U x (w + t • x) = imSchur U x w := by
  set a := imForm U x with ha
  set b := imPair U x w with hb
  have hxx : imPair U x x = a := imPair_self U x
  have hF : ((imForm U (w + t • x) : ℝ) : ℂ) =
      (imForm U w : ℂ) + conj t * b + t * conj b + t * conj t * a := by
    rw [← imPair_self, ← imPair_self, imPair_add_left, imPair_add_right, imPair_add_right,
      imPair_smul_left, imPair_smul_right, imPair_smul_left, imPair_smul_right, hxx,
      imPair_conj U x w]
    ring
  have hB : imPair U x (w + t • x) = b + t * a := by
    rw [imPair_add_right, imPair_smul_right, hxx]
  unfold imSchur
  rw [← ha, hB]
  have hFr : imForm U (w + t • x) =
      imForm U w + 2 * (conj t * b).re + Complex.normSq t * a := by
    have := congrArg Complex.re hF
    simp only [Complex.ofReal_re, Complex.add_re] at this
    rw [this]
    have e1 : (t * conj b).re = (conj t * b).re := by
      rw [← Complex.conj_conj (t * conj b)]; simp [map_mul, mul_comm]
    have e2 : (t * conj t * (a : ℂ)).re = Complex.normSq t * a := by
      rw [Complex.mul_conj]; simp
    rw [e1, e2]; ring
  have hN : ‖b + t * a‖ ^ 2 = ‖b‖ ^ 2 + 2 * a * (conj t * b).re + Complex.normSq t * a ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp only [Complex.normSq_ofReal, map_mul, Complex.conj_ofReal]
    have : (b * (conj t * (a : ℂ))).re = a * (conj t * b).re := by
      simp [Complex.mul_re]; ring
    rw [this]; ring
  rw [hFr, hN]
  field_simp
  ring

/-- Continuity of `F` and of `B(x, ·)`. -/
lemma continuous_imForm (U : Ell2 →L[ℂ] Ell2) : Continuous (imForm U) := by
  unfold imForm
  exact continuous_const.mul (Complex.continuous_im.comp
    (continuous_id.inner (U.continuous)))

lemma continuous_imPair (U : Ell2 →L[ℂ] Ell2) (x : Ell2) : Continuous (imPair U x) := by
  unfold imPair
  exact continuous_const.mul (continuous_const.inner
    (U - ContinuousLinearMap.adjoint U).continuous)

/-- **Index count.** If the Schur complement is nonnegative on a dense set, then `F ≥ 0` on the closed hyperplane `{B(x, ·) = 0}`. -/
theorem nonneg_of_imSchur_nonneg (U : Ell2 →L[ℂ] Ell2) {x : Ell2}
    {S : Set Ell2} (hS : Dense S) (hC : ∀ w ∈ S, 0 ≤ imSchur U x w) (w : Ell2)
    (hw : imPair U x w = 0) : 0 ≤ imForm U w := by
  have hcont : Continuous (imSchur U x) := by
    unfold imSchur
    exact (continuous_imForm U).sub (((continuous_imPair U x).norm.pow 2).div_const _)
  have hall : ∀ v, 0 ≤ imSchur U x v := by
    intro v
    have hclosed : IsClosed {v | 0 ≤ imSchur U x v} := isClosed_le continuous_const hcont
    exact hclosed.closure_subset_iff.mpr (fun v hv => hC v hv) (hS v)
  have := hall w
  unfold imSchur at this
  rwa [hw, norm_zero, zero_pow two_ne_zero, zero_div, sub_zero] at this

/-- Finitely supported vectors are dense in `ℓ²`. -/
lemma dense_finSupp : Dense {v : Ell2 | ∃ N : ℕ, ∀ n, N ≤ n → (v : ℕ → ℂ) n = 0} := by
  intro v
  have hs := lp.hasSum_single (p := 2) (by norm_num) v
  refine mem_closure_of_tendsto hs.tendsto_sum_nat ?_
  refine Eventually.of_forall fun N => ⟨N, fun n hn => ?_⟩
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have : n ≠ i := by
    have := Finset.mem_range.mp hi; omega
  simp [this]

/-! ### Linear dependence of the Herglotz vector on the density -/

lemma herglotzVec_congr {a b : ℝ → ℂ} (hab : a = b) (ha : IsDirDensity a) (hb : IsDirDensity b)
    (k : ℝ) (z : ℂ) : herglotzVec ha k z = herglotzVec hb k z := by
  subst hab; rfl

lemma herglotzVec_add {a b : ℝ → ℂ} (ha : IsDirDensity a) (hb : IsDirDensity b) (k : ℝ)
    (z : ℂ) : herglotzVec (ha.add hb) k z = herglotzVec ha k z + herglotzVec hb k z := by
  have hf : (∑ i, (![1, 1] : Fin 2 → ℂ) i • (![a, b] : Fin 2 → ℝ → ℂ) i) = a + b := by
    simp [Fin.sum_univ_two]
  have hs : IsDirDensity (∑ i, (![1, 1] : Fin 2 → ℂ) i • (![a, b] : Fin 2 → ℝ → ℂ) i) := by
    rw [hf]; exact ha.add hb
  have hi : ∀ i, IsDirDensity ((![a, b] : Fin 2 → ℝ → ℂ) i) := by
    intro i; fin_cases i
    · exact ha
    · exact hb
  rw [← herglotzVec_congr hf hs (ha.add hb), herglotzVec_sum _ _ hi hs, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]

lemma herglotzVec_smul {a : ℝ → ℂ} (ha : IsDirDensity a) (c : ℂ) (k : ℝ) (z : ℂ) :
    herglotzVec (ha.const_smul c) k z = c • herglotzVec ha k z := by
  have hf : (∑ i, (![c] : Fin 1 → ℂ) i • (![a] : Fin 1 → ℝ → ℂ) i) = c • a := by
    simp
  have hs : IsDirDensity (∑ i, (![c] : Fin 1 → ℂ) i • (![a] : Fin 1 → ℝ → ℂ) i) := by
    rw [hf]; exact ha.const_smul c
  have hi : ∀ i, IsDirDensity ((![a] : Fin 1 → ℝ → ℂ) i) := by
    intro i; fin_cases i; exact ha
  rw [← herglotzVec_congr hf hs (ha.const_smul c), herglotzVec_sum _ _ hi hs]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Matrix.cons_val_zero]

/-- The `L²` direction densities, as a submodule of all functions. -/
def dirDensities : Submodule ℂ (ℝ → ℂ) where
  carrier := {a | IsDirDensity a}
  add_mem' ha hb := MemLp.add ha hb
  zero_mem' := MemLp.zero
  smul_mem' c _ ha := MemLp.const_smul ha c

/-- `a ↦ y_a(z)` as a linear map on direction densities. -/
def herglotzVecLin (k : ℝ) (z : ℂ) : dirDensities →ₗ[ℂ] Ell2 where
  toFun a := herglotzVec (a.2 : IsDirDensity a.1) k z
  map_add' a b := herglotzVec_add a.2 b.2 k z
  map_smul' c a := herglotzVec_smul a.2 c k z

/-- For a closed Lipschitz curve, the signed area integral does not depend on the base point:
`∫ Im(conj(γ - γ(0)) γ') = ∫ Im(conj γ · γ')`. -/
lemma integral_areaDensity_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) :
    ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ = ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ θ := by
  have hloc : LocallyIntegrable (deriv γ) volume := locallyIntegrable_of_bounded
      (measurable_deriv γ).aestronglyMeasurable (norm_deriv_le_of_lipschitzWith hK)
  have hint : IntervalIntegrable (deriv γ) volume 0 (2 * π) :=
    (hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hint1 : IntervalIntegrable (fun θ => conj (γ 0) * deriv γ θ) volume 0 (2 * π) :=
    hint.const_mul _
  have hint2 : IntervalIntegrable (fun θ => Complex.imCLM (conj (γ 0) * deriv γ θ)) volume 0
      (2 * π) := ⟨Complex.imCLM.integrable_comp hint1.1, Complex.imCLM.integrable_comp hint1.2⟩
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  have hA : IntervalIntegrable (areaDensity γ) volume 0 (2 * π) := by
    refine (intervalIntegrable_const (c := R * K)).mono_fun'
      (areaDensity_aestronglyMeasurable hK.continuous).restrict ?_
    rw [Set.uIoc_of_le (by positivity)]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun θ hθ => ?_)
    show ‖areaDensity γ θ‖ ≤ R * K
    rw [Real.norm_eq_abs]
    exact abs_areaDensity_le hK hR ⟨hθ.1.le, hθ.2⟩
  have h1 : (fun θ => signedAreaDensity γ θ) =
      fun θ => areaDensity γ θ + Complex.imCLM (conj (γ 0) * deriv γ θ) := by
    funext θ; simp only [areaDensity, signedAreaDensity, map_sub, sub_mul, Complex.sub_im,
      Complex.imCLM_apply]; ring
  have h0 : ∫ θ in (0 : ℝ)..(2 * π), Complex.imCLM (conj (γ 0) * deriv γ θ) = 0 := by
    rw [Complex.imCLM.intervalIntegral_comp_comm hint1, intervalIntegral.integral_const_mul,
      integral_deriv_of_lipschitz hK, hclosed, sub_self, mul_zero, map_zero]
  rw [h1, intervalIntegral.integral_add hA hint2, h0, add_zero]

/-- `F(e₀) = 2 a_E`. -/
lemma imForm_monodromy_basisVec (W : ℝ → Ell2 →L[ℂ] Ell2) :
    imForm (monodromy W) (basisVec 0) = 2 * smallA W := by
  unfold imForm smallA monodromy
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_basisVec,
    Complex.conj_im]
  ring

/-- **Lemma 8.2 (sign of `a_E`).** For small `E > 0`, `F(e₀) = 2 a_E < 0`. -/
theorem small_energy_imForm_basisVec_neg {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      imForm (monodromy W) (basisVec 0) < 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨C, hC0, hC⟩ := smallA_approx hK
  set v := (volume Ω).toReal with hv
  have hvpos : 0 < v := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  have harea : ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ = 2 * v := by
    rw [integral_areaDensity_eq hK hclosed]; exact hγ.area
  refine ⟨min 1 ((v / (C + 1)) ^ 2), lt_min one_pos (by positivity),
    fun E hE hEδ W hW => ?_⟩
  have hE1 : E ≤ 1 := (hEδ.trans_le (min_le_left _ _)).le
  have hE2 : E < (v / (C + 1)) ^ 2 := hEδ.trans_le (min_le_right _ _)
  have hs : Real.sqrt E < v / (C + 1) := by
    rw [show v / (C + 1) = Real.sqrt ((v / (C + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt hE.le hE2
  have hs' : (C + 1) * Real.sqrt E < v := by
    rw [lt_div_iff₀ (by positivity)] at hs; linarith
  have h := hC E hE.le hE1 W hW
  rw [harea] at h
  have h2 := (abs_le.mp h).2
  have hsq := Real.sqrt_nonneg E
  rw [imForm_monodromy_basisVec]
  nlinarith [mul_lt_mul_of_pos_left hs' hE]

end PolyaNeumann

end
