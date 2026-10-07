module

public import RequestProject.BoundaryTransmutation

/-!
# The normalized conormal transmutation (Lemma 6.14, Fourier form)

Lemma 6.14 of the paper concerns `Ĵ_E = Λ^{-1/2} 𝒥_E Λ^{-1/2}`, where in conformal coordinates

  `𝒥_E h = |D| h + ∑_{j ≥ 1} (-E/4)^j / j! · (-i j γ' γ^{j-1} J^j h + i conj(γ') γ^j J^{j-1} h)`.

It asserts that `Ĵ_E` is the inclusion plus an operator gaining one derivative, and that it
depends continuously on `E` in operator norm. This file proves these two assertions in the
Fourier model of `BoundaryTransmutation.lean`. As there, the Fourier coefficients `b`, `a`, `g` of
`γ'`, `conj γ'`, `γ` are given sequences in the weighted `ℓ¹` space of order `s ≥ 0`.

* `SeqOpBound s t C Φ`: a map of coefficient sequences, linear on `H^s`, with
  `‖Φ h‖_{H^t} ≤ C ‖h‖_{H^s}`. Such maps form a calculus (composition, sums, scalars), and each
  gives a bounded operator on `ℓ²(ℤ)` in normalized coordinates (`SeqOpBound.toCLM`).
* `conormalRemOp`: the remainder `𝒥_E − |D|` on `H^s`, as a bounded operator on `ℓ²(ℤ)` in
  normalized coordinates. It is the operator-norm convergent series `∑_j (-E/4)^{j+1}/(j+1)! T_j`.
  On `sobVec s h` it gives the series of `vekuaConormal_sub_bound` (`conormalRemOp_sobVec`).
  It is continuous in `E ∈ ℂ` in operator norm (`continuous_conormalRemOp`).
* `normalizedConormal`: `Ĵ_E = Λ^{-1/2} |D| Λ^{-1/2} + Λ^{-1} ∘ (𝒥_E − |D|)` at `s = 1/2`. The
  principal part is the multiplier `|n|/(1+|n|)` (`normalizedConormal_principal_apply`).
* **Lemma 6.14** (`normalizedConormal_sub_one_eq`, `isCompactOperator_normalizedConormal_sub_one`,
  `continuous_normalizedConormal`): `Ĵ_E − I = Λ^{-1} ∘ ((𝒥_E − |D|) − I)` gains one derivative,
  hence is compact, and `E ↦ Ĵ_E` is norm-continuous.
* **Lemma 7.3 for `Ĵ_E`** (`normalizedConormal_fixed_complement`): if `Ĵ_{E₀}` is injective on a
  closed subspace `H₀`, a fixed `R = inclusion + finite rank` makes `Ĵ_E Π₀ + R Π₁` invertible
  near `E₀`, with continuous inverse.

The operators are defined on all of `ℓ²(ℤ)`; the paper's `Ĵ_E` is the restriction to the
nonpositive modes, and both properties pass to restrictions. The injectivity of `Ĵ_E` (from
Lemma 6.13, which needs elliptic regularity) is not proved here.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology

/-! ### Sobolev sequences in normalized coordinates -/

lemma isSobolevSeq_add {s : ℝ} {f f' : ℤ → ℂ} (hf : IsSobolevSeq s f) (hf' : IsSobolevSeq s f') :
    IsSobolevSeq s (f + f') := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((hf.mul_left 2).add (hf'.mul_left 2))
  have hw : 0 ≤ sobWeight n ^ s := by have := sobWeight_pos n; positivity
  have h1 : ‖(f + f') n‖ ≤ ‖f n‖ + ‖f' n‖ := norm_add_le _ _
  have h2 : sobWeight n ^ s * ‖(f + f') n‖ ≤
      sobWeight n ^ s * ‖f n‖ + sobWeight n ^ s * ‖f' n‖ := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left h1 hw
  have h3 : 0 ≤ sobWeight n ^ s * ‖(f + f') n‖ := by positivity
  nlinarith [sq_nonneg (sobWeight n ^ s * ‖f n‖ - sobWeight n ^ s * ‖f' n‖)]

lemma isSobolevSeq_smul {s : ℝ} (c : ℂ) {f : ℤ → ℂ} (hf : IsSobolevSeq s f) :
    IsSobolevSeq s (c • f) := by
  refine (hf.mul_left (‖c‖ ^ 2)).congr fun n => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]; ring

lemma sobVec_congr {s : ℝ} {f f' : ℤ → ℂ} (e : f = f') (hf : IsSobolevSeq s f)
    (hf' : IsSobolevSeq s f') : sobVec s f hf = sobVec s f' hf' := by
  subst e; rfl

@[simp] lemma sobVec_apply {s : ℝ} {f : ℤ → ℂ} (hf : IsSobolevSeq s f) (n : ℤ) :
    (sobVec s f hf : ℤ → ℂ) n = ((sobWeight n ^ s : ℝ) : ℂ) * f n := rfl

lemma sobVec_add {s : ℝ} {f f' : ℤ → ℂ} (hf : IsSobolevSeq s f) (hf' : IsSobolevSeq s f')
    (hff : IsSobolevSeq s (f + f')) :
    sobVec s (f + f') hff = sobVec s f hf + sobVec s f' hf' := by
  ext n
  simp [mul_add]

lemma sobVec_smul {s : ℝ} (c : ℂ) {f : ℤ → ℂ} (hf : IsSobolevSeq s f)
    (hcf : IsSobolevSeq s (c • f)) :
    sobVec s (c • f) hcf = c • sobVec s f hf := by
  ext n
  simp only [sobVec_apply, Pi.smul_apply, smul_eq_mul, lp.coeFn_smul]
  ring

lemma sobWeight_rpow_mul_neg (s : ℝ) (n : ℤ) : sobWeight n ^ s * sobWeight n ^ (-s) = 1 := by
  rw [Real.rpow_neg (sobWeight_pos n).le,
    mul_inv_cancel₀ (by have := sobWeight_pos n; positivity)]

/-- The coefficient sequence `(λₙ^{-s} fₙ)ₙ ∈ H^s` represented by `f ∈ ℓ²(ℤ)` in normalized
coordinates; inverse to `sobVec s`. -/
def fromL2 (s : ℝ) (f : L2Z) (n : ℤ) : ℂ := ((sobWeight n ^ (-s) : ℝ) : ℂ) * f n

lemma isSobolevSeq_fromL2 (s : ℝ) (f : L2Z) : IsSobolevSeq s (fromL2 s f) := by
  refine (summable_norm_sq_L2Z f).congr fun n => ?_
  unfold fromL2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by have := sobWeight_pos n; positivity), ← mul_assoc,
    sobWeight_rpow_mul_neg, one_mul]

lemma sobVec_fromL2 (s : ℝ) (f : L2Z) : sobVec s (fromL2 s f) (isSobolevSeq_fromL2 s f) = f := by
  ext n
  rw [sobVec_apply, fromL2, ← mul_assoc, ← Complex.ofReal_mul, sobWeight_rpow_mul_neg]
  simp

lemma fromL2_sobVec (s : ℝ) (h : ℤ → ℂ) (hh : IsSobolevSeq s h) : fromL2 s (sobVec s h hh) = h := by
  funext n
  rw [fromL2, sobVec_apply, ← mul_assoc, ← Complex.ofReal_mul, mul_comm (sobWeight n ^ (-s)),
    sobWeight_rpow_mul_neg]
  simp

lemma fromL2_add (s : ℝ) (f f' : L2Z) : fromL2 s (f + f') = fromL2 s f + fromL2 s f' := by
  funext n
  simp [fromL2, mul_add]

lemma fromL2_smul (s : ℝ) (c : ℂ) (f : L2Z) : fromL2 s (c • f) = c • fromL2 s f := by
  funext n
  simp only [fromL2, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Bounded linear maps of coefficient sequences -/

/-- `Φ` maps `H^s` to `H^t`, linearly on `H^s`, with `‖Φ h‖_{H^t} ≤ C ‖h‖_{H^s}`. -/
structure SeqOpBound (s t C : ℝ) (Φ : (ℤ → ℂ) → (ℤ → ℂ)) : Prop where
  nonneg : 0 ≤ C
  maps : ∀ h, IsSobolevSeq s h → IsSobolevSeq t (Φ h)
  bound : ∀ h, IsSobolevSeq s h → Real.sqrt (sobNormSq t (Φ h)) ≤ C * Real.sqrt (sobNormSq s h)
  map_add : ∀ h h', IsSobolevSeq s h → IsSobolevSeq s h' → Φ (h + h') = Φ h + Φ h'
  map_smul : ∀ (c : ℂ) h, IsSobolevSeq s h → Φ (c • h) = c • Φ h

namespace SeqOpBound

variable {s t u C D : ℝ} {Φ Ψ : (ℤ → ℂ) → (ℤ → ℂ)}

lemma mono_const (H : SeqOpBound s t C Φ) (hCD : C ≤ D) : SeqOpBound s t D Φ :=
  ⟨H.nonneg.trans hCD, H.maps,
    fun h hh => (H.bound h hh).trans (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _)),
    H.map_add, H.map_smul⟩

lemma comp (H : SeqOpBound s t C Φ) (H' : SeqOpBound t u D Ψ) :
    SeqOpBound s u (D * C) (Ψ ∘ Φ) := by
  refine ⟨mul_nonneg H'.nonneg H.nonneg, fun h hh => H'.maps _ (H.maps h hh),
    fun h hh => ?_, fun h h' hh hh' => ?_, fun c h hh => ?_⟩
  · calc _ ≤ D * Real.sqrt (sobNormSq t (Φ h)) := H'.bound _ (H.maps h hh)
      _ ≤ D * (C * Real.sqrt (sobNormSq s h)) :=
          mul_le_mul_of_nonneg_left (H.bound h hh) H'.nonneg
      _ = _ := by ring
  · simp only [Function.comp, H.map_add h h' hh hh',
      H'.map_add _ _ (H.maps h hh) (H.maps h' hh')]
  · simp only [Function.comp, H.map_smul c h hh, H'.map_smul c _ (H.maps h hh)]

lemma add (H : SeqOpBound s t C Φ) (H' : SeqOpBound s t D Ψ) :
    SeqOpBound s t (C + D) (fun h => Φ h + Ψ h) := by
  refine ⟨add_nonneg H.nonneg H'.nonneg, fun h hh => isSobolevSeq_add (H.maps h hh) (H'.maps h hh),
    fun h hh => ?_, fun h h' hh hh' => ?_, fun c h hh => ?_⟩
  · have e := sobVec_add (H.maps h hh) (H'.maps h hh) (isSobolevSeq_add (H.maps h hh) (H'.maps h hh))
    rw [← norm_sobVec _ _ (isSobolevSeq_add (H.maps h hh) (H'.maps h hh)), e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_sobVec, norm_sobVec, add_mul]
    exact add_le_add (H.bound h hh) (H'.bound h hh)
  · rw [H.map_add h h' hh hh', H'.map_add h h' hh hh']
    abel
  · rw [H.map_smul c h hh, H'.map_smul c h hh, smul_add]

lemma smul (c : ℂ) (H : SeqOpBound s t C Φ) :
    SeqOpBound s t (‖c‖ * C) (fun h => c • Φ h) := by
  refine ⟨mul_nonneg (norm_nonneg _) H.nonneg, fun h hh => isSobolevSeq_smul c (H.maps h hh),
    fun h hh => ?_, fun h h' hh hh' => ?_, fun d h hh => ?_⟩
  · rw [← norm_sobVec _ _ (isSobolevSeq_smul c (H.maps h hh)), sobVec_smul c (H.maps h hh),
      norm_smul, norm_sobVec, mul_assoc]
    exact mul_le_mul_of_nonneg_left (H.bound h hh) (norm_nonneg _)
  · rw [H.map_add h h' hh hh', smul_add]
  · rw [H.map_smul d h hh, smul_comm]

lemma id_mono (hst : s ≤ t) : SeqOpBound t s 1 id :=
  ⟨zero_le_one, fun _ hh => (sobNormSq_mono hst hh).1,
    fun _ hh => by rw [one_mul]; exact Real.sqrt_le_sqrt (sobNormSq_mono hst hh).2,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- The bounded operator on `ℓ²(ℤ)` given by `Φ` in normalized coordinates:
`f ↦ sobVec t (Φ (fromL2 s f))`. -/
def toCLM (H : SeqOpBound s t C Φ) : L2Z →L[ℂ] L2Z :=
  LinearMap.mkContinuous
    { toFun := fun f => sobVec t (Φ (fromL2 s f)) (H.maps _ (isSobolevSeq_fromL2 s f))
      map_add' := fun f g => by
        have e : Φ (fromL2 s (f + g)) = Φ (fromL2 s f) + Φ (fromL2 s g) := by
          rw [fromL2_add, H.map_add _ _ (isSobolevSeq_fromL2 s f) (isSobolevSeq_fromL2 s g)]
        rw [sobVec_congr e _ (isSobolevSeq_add (H.maps _ (isSobolevSeq_fromL2 s f))
          (H.maps _ (isSobolevSeq_fromL2 s g)))]
        exact sobVec_add _ _ _
      map_smul' := fun c f => by
        have e : Φ (fromL2 s (c • f)) = c • Φ (fromL2 s f) := by
          rw [fromL2_smul, H.map_smul _ _ (isSobolevSeq_fromL2 s f)]
        rw [sobVec_congr e _ (isSobolevSeq_smul c (H.maps _ (isSobolevSeq_fromL2 s f)))]
        exact sobVec_smul _ _ _ }
    C (fun f => by
      have e := norm_sobVec s (fromL2 s f) (isSobolevSeq_fromL2 s f)
      rw [sobVec_fromL2] at e
      change ‖sobVec t (Φ (fromL2 s f)) (H.maps _ (isSobolevSeq_fromL2 s f))‖ ≤ C * ‖f‖
      rw [norm_sobVec, e]
      exact H.bound _ (isSobolevSeq_fromL2 s f))

lemma toCLM_sobVec (H : SeqOpBound s t C Φ) (h : ℤ → ℂ) (hh : IsSobolevSeq s h) :
    H.toCLM (sobVec s h hh) = sobVec t (Φ h) (H.maps h hh) := by
  unfold toCLM
  rw [LinearMap.mkContinuous_apply]
  change sobVec t (Φ (fromL2 s (sobVec s h hh))) (H.maps _ (isSobolevSeq_fromL2 s _)) = _
  exact sobVec_congr (by rw [fromL2_sobVec]) _ _

lemma norm_toCLM_le (H : SeqOpBound s t C Φ) : ‖H.toCLM‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ H.nonneg _

end SeqOpBound

/-! ### The building blocks: multipliers and the normalized primitive -/

theorem seqOpBound_seqConv {s : ℝ} (hs : 0 ≤ s) {c : ℤ → ℂ} (hc : IsWL1 s c) :
    SeqOpBound s s (wl1Norm s c) (seqConv c) := by
  have h0 : 0 ≤ wl1Norm s c := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  refine ⟨h0, fun h hh => (sobNormSq_seqConv_le hs hc hh).2.1, fun h hh => ?_,
    fun h h' hh hh' => ?_, fun c' h hh => ?_⟩
  · calc _ ≤ Real.sqrt (wl1Norm s c ^ 2 * sobNormSq s h) :=
          Real.sqrt_le_sqrt (sobNormSq_seqConv_le hs hc hh).2.2
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h0]
  · funext n
    simp only [seqConv, Pi.add_apply, mul_add]
    exact Summable.tsum_add ((sobNormSq_seqConv_le hs hc hh).1 n)
      ((sobNormSq_seqConv_le hs hc hh').1 n)
  · funext n
    simp only [seqConv, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring

lemma primSeq_add (u v : ℤ → ℂ) : primSeq (u + v) = primSeq u + primSeq v := by
  funext n; simp [primSeq, add_div]

lemma primSeq_smul (c : ℂ) (u : ℤ → ℂ) : primSeq (c • u) = c • primSeq u := by
  funext n; simp [primSeq, mul_div_assoc]

lemma summable_primSeq_seqConv {s : ℝ} (hs : 0 ≤ s) {a h : ℤ → ℂ} (ha : IsWL1 s a)
    (hh : IsSobolevSeq s h) : Summable (primSeq (seqConv a h)) :=
  (sq_tsum_norm_le hs (sobNormSq_primSeq_seqConv_le hs ha hh).1).1.of_norm

theorem seqOpBound_antiPrim {s : ℝ} (hs : 0 ≤ s) {a : ℤ → ℂ} (ha : IsWL1 s a) :
    SeqOpBound s (s + 1) (Real.sqrt (primConst s a)) (antiPrim a) := by
  refine ⟨Real.sqrt_nonneg _, fun h hh => (antiPrim_bound hs ha hh).1, fun h hh => ?_,
    fun h h' hh hh' => ?_, fun c h hh => ?_⟩
  · calc _ ≤ Real.sqrt (primConst s a * sobNormSq s h) :=
          Real.sqrt_le_sqrt (antiPrim_bound hs ha hh).2
      _ = _ := Real.sqrt_mul (primConst_nonneg s a) _
  · have hc := (seqOpBound_seqConv hs ha).map_add h h' hh hh'
    funext n
    by_cases hn : n = 0
    · simp only [antiPrim, hn, if_true, Pi.add_apply, hc, primSeq_add]
      rw [Summable.tsum_add (summable_primSeq_seqConv hs ha hh)
        (summable_primSeq_seqConv hs ha hh'), neg_add]
    · simp [antiPrim, hn, hc, primSeq_add]
  · have hc := (seqOpBound_seqConv hs ha).map_smul c h hh
    funext n
    by_cases hn : n = 0
    · simp only [antiPrim, hn, if_true, Pi.smul_apply, hc, primSeq_smul, smul_eq_mul]
      rw [tsum_mul_left]; ring
    · simp [antiPrim, hn, hc, primSeq_smul]

theorem seqOpBound_antiPrimIter {s : ℝ} (hs : 0 ≤ s) {a : ℤ → ℂ} (ha : IsWL1 s a) (j : ℕ) :
    SeqOpBound s s (Real.sqrt (primConst s a) ^ j) (antiPrimIter a j) := by
  induction j with
  | zero => exact (SeqOpBound.id_mono le_rfl).mono_const (by simp)
  | succ j ih =>
    have e : antiPrimIter a (j + 1) = id ∘ (antiPrim a ∘ antiPrimIter a j) := by
      funext h; exact Function.iterate_succ_apply' _ _ _
    rw [e]
    exact ((ih.comp (seqOpBound_antiPrim hs ha)).comp
      (SeqOpBound.id_mono (by linarith : s ≤ s + 1))).mono_const (le_of_eq (by ring))

/-- Multiplication by `c · γ^j` on `H^s`, with bound `‖c‖_{ℓ¹_s} R^j`. -/
theorem seqOpBound_conv_pow {s : ℝ} (hs : 0 ≤ s) {c g : ℤ → ℂ} (hc : IsWL1 s c)
    (hg : IsWL1 s g) (j : ℕ) :
    SeqOpBound s s (wl1Norm s c * wl1Norm s g ^ j)
      (fun h => seqConv c (seqConv (seqConvPow g j) h)) := by
  have hc0 : 0 ≤ wl1Norm s c := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  exact ((seqOpBound_seqConv hs (wl1Norm_seqConvPow_le hs hg j).1).comp
    (seqOpBound_seqConv hs hc)).mono_const
    (mul_le_mul_of_nonneg_left (wl1Norm_seqConvPow_le hs hg j).2 hc0)

/-! ### The conormal remainder `𝒥_E − |D|` -/

/-- The `(j+1)`-th term of the conormal series (before its coefficient), as a map of coefficient
sequences: `-i (j+1) γ' γ^j J^{j+1} h + i conj(γ') γ^{j+1} J^j h`. -/
def conormalTermMap (b a g : ℤ → ℂ) (j : ℕ) (h : ℤ → ℂ) : ℤ → ℂ :=
  (-Complex.I * (j + 1 : ℕ)) • seqConv b (seqConv (seqConvPow g j) (antiPrimIter a (j + 1) h)) +
    Complex.I • seqConv a (seqConv (seqConvPow g (j + 1)) (antiPrimIter a j h))

/-- The bound `(j+1) B R^j q^{j+1} + M R^{j+1} q^j` on the `(j+1)`-th conormal term. -/
def conormalTermConst (s : ℝ) (b a g : ℤ → ℂ) (j : ℕ) : ℝ :=
  (j + 1) * (wl1Norm s b * wl1Norm s g ^ j * Real.sqrt (primConst s a) ^ (j + 1)) +
    wl1Norm s a * wl1Norm s g ^ (j + 1) * Real.sqrt (primConst s a) ^ j

theorem seqOpBound_conormalTerm {s : ℝ} (hs : 0 ≤ s) {b a g : ℤ → ℂ} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) (j : ℕ) :
    SeqOpBound s s (conormalTermConst s b a g j) (conormalTermMap b a g j) := by
  have H1 := ((seqOpBound_antiPrimIter hs ha (j + 1)).comp
    (seqOpBound_conv_pow hs hb hg j)).smul (-Complex.I * (j + 1 : ℕ))
  have H2 := ((seqOpBound_antiPrimIter hs ha j).comp
    (seqOpBound_conv_pow hs ha hg (j + 1))).smul Complex.I
  have hn : ‖-Complex.I * ((j + 1 : ℕ) : ℂ)‖ = j + 1 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_natCast]; push_cast; ring
  refine (H1.add H2).mono_const (le_of_eq ?_)
  rw [hn, Complex.norm_I, conormalTermConst]
  ring

/-- The `(j+1)`-th conormal term as a bounded operator on `ℓ²(ℤ)` (normalized `H^s`
coordinates). -/
def conormalTermOp {s : ℝ} (hs : 0 ≤ s) {b a g : ℤ → ℂ} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) (j : ℕ) : L2Z →L[ℂ] L2Z :=
  (seqOpBound_conormalTerm hs hb ha hg j).toCLM

lemma conormalTermOp_sobVec {s : ℝ} (hs : 0 ≤ s) {b a g h : ℤ → ℂ} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) (hh : IsSobolevSeq s h) (j : ℕ) :
    conormalTermOp hs hb ha hg j (sobVec s h hh) = vekuaConormalTerm hs hb ha hg hh j := by
  unfold conormalTermOp
  rw [SeqOpBound.toCLM_sobVec]
  unfold vekuaConormalTerm
  have h1 := (sobNormSq_conv_pow_iter_le hs hb hg ha hh j (j + 1)).1
  have h2 := (sobNormSq_conv_pow_iter_le hs ha hg ha hh (j + 1) j).1
  rw [sobVec_congr (by unfold conormalTermMap; rfl) _
    (isSobolevSeq_add (isSobolevSeq_smul (-Complex.I * (j + 1 : ℕ)) h1)
      (isSobolevSeq_smul Complex.I h2)),
    sobVec_add (isSobolevSeq_smul _ h1) (isSobolevSeq_smul _ h2), sobVec_smul _ h1,
    sobVec_smul _ h2]

/-- The coefficient `(-E/4)^{j+1}/(j+1)!` of the `(j+1)`-th conormal term. -/
def conormalCoeff (E : ℂ) (j : ℕ) : ℂ := (-E / 4) ^ (j + 1) / (j + 1).factorial

/-- Summable majorant of the operator-norm series on `‖E‖ ≤ r`. -/
lemma norm_conormalCoeff_smul_le {s : ℝ} (hs : 0 ≤ s) {b a g : ℤ → ℂ} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) {r : ℝ} {E : ℂ} (hE : ‖E‖ ≤ r) (j : ℕ) :
    ‖conormalCoeff E j • conormalTermOp hs hb ha hg j‖ ≤
      r / 4 * (wl1Norm s b * Real.sqrt (primConst s a) + wl1Norm s a * wl1Norm s g) *
        ((r * wl1Norm s g * Real.sqrt (primConst s a) / 4) ^ j / j.factorial) := by
  set B := wl1Norm s b
  set M := wl1Norm s a
  set R := wl1Norm s g
  set q := Real.sqrt (primConst s a) with hq
  have hB0 : 0 ≤ B := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  have hM0 : 0 ≤ M := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  have hR0 : 0 ≤ R := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := (norm_nonneg E).trans hE
  set e := r / 4 with he
  have he0 : 0 ≤ e := by positivity
  have hT : ‖conormalTermOp hs hb ha hg j‖ ≤
      (j + 1) * (B * R ^ j * q ^ (j + 1)) + M * R ^ (j + 1) * q ^ j :=
    (seqOpBound_conormalTerm hs hb ha hg j).norm_toCLM_le
  have hc : ‖conormalCoeff E j‖ ≤ e ^ (j + 1) / ((j + 1).factorial : ℝ) := by
    rw [conormalCoeff, norm_div, norm_pow, norm_div, norm_neg, Complex.norm_natCast,
      show ‖(4 : ℂ)‖ = 4 by norm_num]
    gcongr
    rw [he]; linarith
  have hf : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have hfp : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [norm_smul]
  calc ‖conormalCoeff E j‖ * ‖conormalTermOp hs hb ha hg j‖
      ≤ e ^ (j + 1) / ((j + 1).factorial : ℝ) *
          ((j + 1) * (B * R ^ j * q ^ (j + 1)) + M * R ^ (j + 1) * q ^ j) :=
        mul_le_mul hc hT (norm_nonneg _) (by positivity)
    _ = e ^ (j + 1) / j.factorial * (B * R ^ j * q ^ (j + 1)) +
          e ^ (j + 1) / ((j + 1) * j.factorial) * (M * R ^ (j + 1) * q ^ j) := by
        rw [hf]; field_simp
    _ ≤ e ^ (j + 1) / j.factorial * (B * R ^ j * q ^ (j + 1)) +
          e ^ (j + 1) / j.factorial * (M * R ^ (j + 1) * q ^ j) := by
        gcongr
        nlinarith
    _ = e * (B * q + M * R) * ((r * R * q / 4) ^ j / j.factorial) := by
        rw [he]; field_simp; ring

lemma summable_conormalSeries {s : ℝ} (hs : 0 ≤ s) {b a g : ℤ → ℂ} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) (E : ℂ) :
    Summable fun j => conormalCoeff E j • conormalTermOp hs hb ha hg j :=
  Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial _).mul_left _)
    (norm_conormalCoeff_smul_le hs hb ha hg le_rfl)

/-- The conormal remainder `𝒥_E − |D|` on `H^s`, in normalized coordinates on `ℓ²(ℤ)`. -/
def conormalRemOp {s : ℝ} (hs : 0 ≤ s) {b a g : ℤ → ℂ} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) (E : ℂ) : L2Z →L[ℂ] L2Z :=
  ∑' j, conormalCoeff E j • conormalTermOp hs hb ha hg j

/-- `conormalRemOp` is the series of Lemma 5.3 (`vekuaConormal_sub_bound`). -/
theorem conormalRemOp_sobVec {s : ℝ} (hs : 0 ≤ s) {b a g h : ℤ → ℂ} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) (hh : IsSobolevSeq s h) (E : ℂ) :
    conormalRemOp hs hb ha hg E (sobVec s h hh) =
      ∑' j : ℕ, ((-E / 4) ^ (j + 1) / (j + 1).factorial) • vekuaConormalTerm hs hb ha hg hh j := by
  unfold conormalRemOp
  have key := ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℂ L2Z (sobVec s h hh))
    (summable_conormalSeries hs hb ha hg E)
  simp only [ContinuousLinearMap.apply_apply] at key
  rw [key]
  refine tsum_congr fun j => ?_
  rw [ContinuousLinearMap.smul_apply, conormalTermOp_sobVec, conormalCoeff]

/-- The conormal remainder depends continuously on `E` in operator norm. -/
theorem continuous_conormalRemOp {s : ℝ} (hs : 0 ≤ s) {b a g : ℤ → ℂ} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) :
    Continuous fun E => conormalRemOp hs hb ha hg E := by
  refine continuous_iff_continuousAt.mpr fun E₀ => ?_
  have hcont : ContinuousOn (fun E => conormalRemOp hs hb ha hg E)
      (Metric.ball 0 (‖E₀‖ + 1)) := by
    refine continuousOn_tsum (fun j => ?_) ((Real.summable_pow_div_factorial _).mul_left _)
      (fun j E hE => norm_conormalCoeff_smul_le hs hb ha hg
        (le_of_lt (mem_ball_zero_iff.mp hE)) j)
    refine Continuous.continuousOn ?_
    unfold conormalCoeff
    fun_prop
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))

/-! ### The normalized conormal transmutation `Ĵ_E` -/

/-- The normalized principal part `Λ^{-1/2} |D| Λ^{-1/2} = I − Λ^{-1}`. -/
def normalizedConormalPrincipal : L2Z →L[ℂ] L2Z :=
  (1 : L2Z →L[ℂ] L2Z) - sobolevSmoothing 1 zero_le_one

/-- The principal part is the Fourier multiplier `|n| / (1 + |n|)`. -/
lemma normalizedConormal_principal_apply (f : L2Z) (n : ℤ) :
    (normalizedConormalPrincipal f : ℤ → ℂ) n = ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) * f n := by
  have hw : (0 : ℝ) < 1 + |(n : ℝ)| := by positivity
  have key : (|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) = 1 - sobWeight n ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, sobWeight]
    field_simp
    ring
  rw [key]
  simp only [normalizedConormalPrincipal, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, lp.coeFn_sub, Pi.sub_apply, sobolevSmoothing, diagOp_apply]
  push_cast
  ring

/-- **`Ĵ_E = Λ^{-1/2} 𝒥_E Λ^{-1/2}`** in Fourier form: principal part `Λ^{-1/2}|D|Λ^{-1/2}` plus
`Λ^{-1/2} (𝒥_E − |D|) Λ^{-1/2} = Λ^{-1} ∘ R_E`, where `R_E` is the conormal remainder on
`H^{1/2}` in normalized coordinates. -/
def normalizedConormal {b a g : ℤ → ℂ} (hb : IsWL1 (1 / 2) b) (ha : IsWL1 (1 / 2) a)
    (hg : IsWL1 (1 / 2) g) (E : ℂ) : L2Z →L[ℂ] L2Z :=
  normalizedConormalPrincipal +
    (sobolevSmoothing 1 zero_le_one).comp (conormalRemOp (by norm_num) hb ha hg E)

/-- **Lemma 6.14 (gain of one derivative).** `Ĵ_E − I = Λ^{-1} ∘ (R_E − I)`. -/
theorem normalizedConormal_sub_one_eq {b a g : ℤ → ℂ} (hb : IsWL1 (1 / 2) b)
    (ha : IsWL1 (1 / 2) a) (hg : IsWL1 (1 / 2) g) (E : ℂ) :
    normalizedConormal hb ha hg E - (1 : L2Z →L[ℂ] L2Z) =
      (sobolevSmoothing 1 zero_le_one).comp
        (conormalRemOp (by norm_num) hb ha hg E - (1 : L2Z →L[ℂ] L2Z)) := by
  unfold normalizedConormal normalizedConormalPrincipal
  have h1 : (sobolevSmoothing 1 zero_le_one).comp (1 : L2Z →L[ℂ] L2Z) =
      sobolevSmoothing 1 zero_le_one := ContinuousLinearMap.ext fun _ => rfl
  rw [ContinuousLinearMap.comp_sub, h1]
  abel

/-- **Lemma 6.14 (inclusion plus compact).** `Ĵ_E − I` is compact. -/
theorem isCompactOperator_normalizedConormal_sub_one {b a g : ℤ → ℂ} (hb : IsWL1 (1 / 2) b)
    (ha : IsWL1 (1 / 2) a) (hg : IsWL1 (1 / 2) g) (E : ℂ) :
    IsCompactOperator (normalizedConormal hb ha hg E - (1 : L2Z →L[ℂ] L2Z)) := by
  rw [normalizedConormal_sub_one_eq]
  exact (isCompactOperator_sobolevSmoothing one_pos).comp_clm _

/-- **Lemma 6.14 (continuity).** `E ↦ Ĵ_E` is continuous in operator norm. -/
theorem continuous_normalizedConormal {b a g : ℤ → ℂ} (hb : IsWL1 (1 / 2) b)
    (ha : IsWL1 (1 / 2) a) (hg : IsWL1 (1 / 2) g) :
    Continuous fun E => normalizedConormal hb ha hg E :=
  continuous_const.add (continuous_const.clm_comp (continuous_conormalRemOp _ hb ha hg))

/-- **Lemma 7.3 for `Ĵ_E`** (fixed complement to the transmuted range). Let `H₀ ⊆ ℓ²(ℤ)` be a
closed subspace (the paper takes the nonpositive Fourier modes) and let `E₀ ∈ ℝ` be an energy at
which `Ĵ_{E₀}` is injective on `H₀` (Lemma 6.13, assumed here). Then a fixed
`R = inclusion + finite rank` on `H₀ᗮ` makes `Ĵ_E Π₀ + R Π₁` invertible for all real `E` near
`E₀`, with inverse continuous in `E`. This combines Lemma 6.14 with the abstract Lemma 7.3
(`exists_fixed_complement`). -/
theorem normalizedConormal_fixed_complement (H₀ : Submodule ℂ L2Z) [H₀.HasOrthogonalProjection]
    {b a g : ℤ → ℂ} (hb : IsWL1 (1 / 2) b) (ha : IsWL1 (1 / 2) a) (hg : IsWL1 (1 / 2) g)
    {E₀ : ℝ} (hinj : Function.Injective ((normalizedConormal hb ha hg E₀).comp H₀.subtypeL)) :
    ∃ R : H₀ᗮ →L[ℂ] L2Z,
      FiniteDimensional ℂ
        (LinearMap.range ((R - Submodule.subtypeL H₀ᗮ : H₀ᗮ →L[ℂ] L2Z) : H₀ᗮ →ₗ[ℂ] L2Z)) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit ((normalizedConormal hb ha hg E).comp H₀.subtypeL ∘L
          H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E : ℝ => Ring.inverse ((normalizedConormal hb ha hg E).comp
          H₀.subtypeL ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) U := by
  have hJ : Continuous fun E : ℝ => (normalizedConormal hb ha hg E).comp H₀.subtypeL :=
    ((continuous_normalizedConormal hb ha hg).comp Complex.continuous_ofReal).clm_comp
      continuous_const
  have heq : (normalizedConormal hb ha hg E₀).comp H₀.subtypeL ∘L H₀.orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : L2Z →L[ℂ] L2Z) =
      (normalizedConormal hb ha hg E₀ - (1 : L2Z →L[ℂ] L2Z)) ∘L
        (H₀.subtypeL ∘L H₀.orthogonalProjection) := by
    ext1 x
    have hx := H₀.starProjection_add_starProjection_orthogonal x
    rw [Submodule.starProjection_apply, Submodule.starProjection_apply] at hx
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, Submodule.subtypeL_apply]
    rw [← sub_eq_zero]
    have : (H₀ᗮ.orthogonalProjection x : L2Z) = x - (H₀.orthogonalProjection x : L2Z) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hx
    rw [this]
    abel
  have hcpt : IsCompactOperator ((normalizedConormal hb ha hg E₀).comp H₀.subtypeL ∘L
      H₀.orthogonalProjection + Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection -
        (1 : L2Z →L[ℂ] L2Z)) := by
    rw [heq]
    exact (isCompactOperator_normalizedConormal_sub_one hb ha hg E₀).comp_clm _
  exact exists_fixed_complement H₀ hJ hcpt hinj

end PolyaNeumann
