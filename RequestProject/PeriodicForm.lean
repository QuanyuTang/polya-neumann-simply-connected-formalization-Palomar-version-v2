module

public import RequestProject.CutCorrection

/-!
# The periodic boundary form: endpoint jumps and transmuted nullspace (Lemmas 6.4, 6.9, 6.10)

For a transport `W = W_E` with endpoint `V_E = W(L)`, `c_E = (V_E^* - I)e₀`,
`s_E = (I + V_E^*)e₀` and the correction `B_E` of Definition 6.2, the paper considers
`𝒜_E g = 2 𝒩(E) g + i(T_E - T_E^*) g` and the corrected form `𝒫_E = 𝒜_E + O_E B_E O_E^*`.

The Neumann-to-Dirichlet map `𝒩(E)` is not formalized; we take its output `n = 𝒩(E) g` as an
arbitrary function, and impose on it exactly the properties the paper uses (periodicity in
Lemma 6.4; the trace identities from the transmutation endpoint formulas in Lemmas 6.9–6.10).

* `volterra_jump` / `periodicA_jump` / `periodicP_periodic` (**Lemma 6.4**):
  `(𝒜_E g)(L) - (𝒜_E g)(0) = i⟨s_E, O_E^* g⟩` and `(𝒫_E g)(L) = (𝒫_E g)(0)`.
* `periodicA_radial` (**Lemma 6.9**): if `O_E^* q = i c_E` and `𝒩(E) q = O_E e₀ - i T_E q`,
  then `𝒜_E q = O_E s_E`.
* `periodicP_radial`, `periodicP_of_observationAdj_eq_zero` (**Lemma 6.10**):
  `𝒫_E q = 0` and `T_E^♯ q = Π^c_E O_E^* q = 0` for the radial input, and
  `𝒫_E g = 0`, `T_E^♯ g = 0` whenever `O_E^* g = 0` and `𝒩(E) g = -i T_E g`.
* `schurC` (**Definition 8.1**) and `schurC_periodic`, `schurC_radial`,
  `schurC_of_observationAdj_eq_zero` (**Lemma 8.3**): with `b_E = 𝒜_E q`, `a_E = ⟨q, b_E⟩ ≠ 0`,
  the Schur complement `C^sc_E = 𝒜_E - a_E⁻¹ b_E ⟨b_E, ·⟩` has matching endpoint values,
  `C^sc_E q = 0`, and `C^sc_E g = 0` when `O_E^* g = 0` and `𝒩(E) g = -i T_E g`. The reality of
  `a_E = -i⟨c_E, s_E⟩` (`l2Inner_radial_eq`) is derived from unitarity of `V_E`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The form `(𝒜_E g)(θ) = 2 n(θ) + i((T_E g)(θ) - (T_E^* g)(θ))`, where `n = 𝒩(E) g` is the
Neumann-to-Dirichlet trace of `g` (supplied as data). -/
def periodicA (W : ℝ → Ell2 →L[ℂ] Ell2) (n g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  2 * n θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ)

/-- The corrected periodic form `𝒫_E g = 𝒜_E g + O_E B_E O_E^* g` of Definition 6.2, with
`B_E` built from `c_E = (V_E^* - I)e₀` and `d_E = i s_E`. -/
def periodicP (W : ℝ → Ell2 →L[ℂ] Ell2) (n g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  periodicA W n g θ +
    observation W (cutB (cutC (W (2 * π)) (basisVec 0))
      (Complex.I • cutS (W (2 * π)) (basisVec 0)) (observationAdj W g)) θ

/-- **Lemma 6.4 (jump of `i(T_E - T_E^*)`).** If `W` is continuous with `W(0) = I`, then
`i(T_E - T_E^*) g` jumps by `i⟨s_E, O_E^* g⟩` between `0` and `L`. -/
theorem volterra_jump {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    (hW0 : W 0 = 1) {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ}
    (hgB : ∀ s, ‖g s‖ ≤ B) :
    Complex.I * (volterraOp W g (2 * π) - volterraOpAdj W g (2 * π)) -
        Complex.I * (volterraOp W g 0 - volterraOpAdj W g 0) =
      Complex.I * ⟪cutS (W (2 * π)) (basisVec 0), observationAdj W g⟫_ℂ := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have h0 := volterraOp_add_adj hW hg hgB ⟨le_rfl, hL⟩
  have h1 := volterraOp_add_adj hW hg hgB ⟨hL, le_rfl⟩
  have hT0 : volterraOp W g 0 = 0 := by simp [volterraOp]
  have hT1 : volterraOpAdj W g (2 * π) = 0 := by simp [volterraOpAdj]
  rw [hT0, zero_add] at h0
  rw [hT1, add_zero] at h1
  rw [hT0, hT1, h0, h1]
  simp only [observation, hW0, ContinuousLinearMap.one_apply, cutS, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-- **Lemma 6.4 (jump of `𝒜_E`).** If the Neumann trace `n` is periodic, then
`(𝒜_E g)(L) - (𝒜_E g)(0) = i⟨s_E, O_E^* g⟩`. -/
theorem periodicA_jump {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    (hW0 : W 0 = 1) {n g : ℝ → ℂ} (hn : n (2 * π) = n 0) (hg : AEStronglyMeasurable g volume)
    {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) :
    periodicA W n g (2 * π) - periodicA W n g 0 =
      Complex.I * ⟪cutS (W (2 * π)) (basisVec 0), observationAdj W g⟫_ℂ := by
  rw [← volterra_jump hW hW0 hg hgB, periodicA, periodicA, hn]
  ring

lemma transport_zero {γ : ℝ → ℂ} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    W 0 = 1 := by
  have := hW.2 0 ⟨le_rfl, by positivity⟩
  simpa using this

/-- **Lemma 6.4 (periodicity of `𝒫_E`).** For a transport `W` of a Lipschitz curve with
`c_E ≠ 0` and a periodic Neumann trace `n`, the corrected form has matching endpoint values:
`(𝒫_E g)(L) = (𝒫_E g)(0)`. -/
theorem periodicP_periodic {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {n g : ℝ → ℂ} (hn : n (2 * π) = n 0)
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) :
    periodicP W n g (2 * π) = periodicP W n g 0 := by
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have hA := periodicA_jump hW.1 (transport_zero hW) hn hg hgB
  have hO := observation_jump hW (cutB (cutC (W (2 * π)) (basisVec 0))
      (Complex.I • cutS (W (2 * π)) (basisVec 0)) (observationAdj W g))
  rw [inner_cutC_cutB hU _ hc] at hO
  rw [← sub_eq_zero]
  simp only [periodicP]
  linear_combination hA + hO

/-- **Lemma 6.9 (radial identity `𝒜_E q_E = O_E s_E`).** Let `q` satisfy the endpoint identity
`O_E^* q = i c_E` and let its Neumann trace be `n = O_E e₀ - i T_E q` on `[0, L]`. Then
`𝒜_E q = O_E s_E` on `[0, L]`. -/
theorem periodicA_radial {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {n q : ℝ → ℂ} (hq : AEStronglyMeasurable q volume) {B : ℝ} (hqB : ∀ s, ‖q s‖ ≤ B)
    (hadj : observationAdj W q = Complex.I • cutC (W (2 * π)) (basisVec 0))
    (hn : ∀ θ ∈ Icc 0 (2 * π), n θ = observation W (basisVec 0) θ - Complex.I * volterraOp W q θ)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    periodicA W n q θ = observation W (cutS (W (2 * π)) (basisVec 0)) θ := by
  have hsum := volterraOp_add_adj hW hq hqB hθ
  rw [hadj] at hsum
  have hs : cutS (W (2 * π)) (basisVec 0) =
      (2 : ℂ) • basisVec 0 + cutC (W (2 * π)) (basisVec 0) := by
    simp only [cutS, cutC]
    rw [two_smul]; abel
  rw [periodicA, hn θ hθ, hs]
  simp only [observation, map_add, map_smul, inner_add_right, inner_smul_right] at hsum ⊢
  linear_combination (-Complex.I) * hsum - Complex.I_sq * (inner ℂ (basisVec 0)
    (W θ (cutC (W (2 * π)) (basisVec 0))))

/-- **Lemma 6.10 (radial nullspace).** Under the hypotheses of Lemma 6.9 and `c_E ≠ 0`,
`𝒫_E q = 0` on `[0, L]` and `T_E^♯ q = Π^c_E O_E^* q = 0`. -/
theorem periodicP_radial {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {n q : ℝ → ℂ}
    (hq : AEStronglyMeasurable q volume) {B : ℝ} (hqB : ∀ s, ‖q s‖ ≤ B)
    (hadj : observationAdj W q = Complex.I • cutC (W (2 * π)) (basisVec 0))
    (hn : ∀ θ ∈ Icc 0 (2 * π), n θ = observation W (basisVec 0) θ - Complex.I * volterraOp W q θ) :
    (∀ θ ∈ Icc 0 (2 * π), periodicP W n q θ = 0) ∧
      cutProj (cutC (W (2 * π)) (basisVec 0)) (observationAdj W q) = 0 := by
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have hBc := (cutB_transport hU (basisVec 0) hc).2
  refine ⟨fun θ hθ => ?_, ?_⟩
  · rw [periodicP, periodicA_radial hW.1 hq hqB hadj hn hθ, hadj, map_smul, hBc, smul_smul,
      Complex.I_mul_I]
    simp [observation]
  · rw [hadj, map_smul, cutProj_eq_starProjection,
      Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_span_singleton_self _),
      smul_zero]

/-- **Lemma 6.10 (nullspace on inputs with `h(0) = 0`).** If `O_E^* g = 0` and the Neumann trace
is `n = -i T_E g` on `[0, L]`, then `𝒜_E g = 𝒫_E g = 0` on `[0, L]` and `T_E^♯ g = 0`. -/
theorem periodicP_of_observationAdj_eq_zero {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : ContinuousOn W (Icc 0 (2 * π))) {n g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume)
    {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (hadj : observationAdj W g = 0)
    (hn : ∀ θ ∈ Icc 0 (2 * π), n θ = -Complex.I * volterraOp W g θ) :
    (∀ θ ∈ Icc 0 (2 * π), periodicA W n g θ = 0 ∧ periodicP W n g θ = 0) ∧
      cutProj (cutC (W (2 * π)) (basisVec 0)) (observationAdj W g) = 0 := by
  refine ⟨fun θ hθ => ?_, by rw [hadj, map_zero]⟩
  have hsum := volterraOp_add_adj hW hg hgB hθ
  rw [hadj] at hsum
  simp only [observation, map_zero, inner_zero_right] at hsum
  have hA : periodicA W n g θ = 0 := by
    rw [periodicA, hn θ hθ]
    linear_combination (-Complex.I) * hsum
  refine ⟨hA, ?_⟩
  rw [periodicP, hA, hadj]
  simp [observation]

/-! ### The small-energy Schur complement (Definition 8.1, Lemma 8.3) -/

/-- The `L²(0, L)` pairing `⟨f, g⟩ = ∫₀^L conj(f) g`. -/
def l2Inner (f g : ℝ → ℂ) : ℂ := ∫ s in (0 : ℝ)..(2 * π), conj (f s) * g s

/-- **Definition 8.1.** With `b = 𝒜_E q` and `a = ⟨q, b⟩`, the Schur complement
`C^sc_E g = 𝒜_E g - a⁻¹ b ⟨b, g⟩`. Here `nq = 𝒩(E) q` and `n = 𝒩(E) g` are the Neumann traces. -/
def schurC (W : ℝ → Ell2 →L[ℂ] Ell2) (nq q n g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  periodicA W n g θ - (l2Inner q (periodicA W nq q))⁻¹ * periodicA W nq q θ *
    l2Inner (periodicA W nq q) g

/-- `⟨x, O_E^* g⟩ = ⟨O_E x, g⟩_{L²}`. -/
lemma inner_observationAdj_right {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (x : Ell2) :
    ⟪x, observationAdj W g⟫_ℂ = l2Inner (observation W x) g := by
  rw [← inner_conj_symm, inner_observationAdj hW hg hgB, ← intervalIntegral_conj, l2Inner]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring

/-- Under the radial hypotheses, `⟨𝒜_E q, g⟩_{L²} = ⟨s_E, O_E^* g⟩`. -/
lemma l2Inner_periodicA_radial {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {nq q : ℝ → ℂ} (hq : AEStronglyMeasurable q volume) {B : ℝ} (hqB : ∀ s, ‖q s‖ ≤ B)
    (hadj : observationAdj W q = Complex.I • cutC (W (2 * π)) (basisVec 0))
    (hnq : ∀ θ ∈ Icc 0 (2 * π),
      nq θ = observation W (basisVec 0) θ - Complex.I * volterraOp W q θ)
    (f : ℝ → ℂ) :
    l2Inner (periodicA W nq q) f =
      l2Inner (observation W (cutS (W (2 * π)) (basisVec 0))) f := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hL] at hs
  simp only [periodicA_radial hW hq hqB hadj hnq hs]

/-- The normalizing constant `a_E = ⟨q, 𝒜_E q⟩ = -i⟨c_E, s_E⟩` is real. -/
lemma l2Inner_radial_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {nq q : ℝ → ℂ}
    (hq : AEStronglyMeasurable q volume) {B : ℝ} (hqB : ∀ s, ‖q s‖ ≤ B)
    (hadj : observationAdj W q = Complex.I • cutC (W (2 * π)) (basisVec 0))
    (hnq : ∀ θ ∈ Icc 0 (2 * π),
      nq θ = observation W (basisVec 0) θ - Complex.I * volterraOp W q θ) :
    l2Inner q (periodicA W nq q) =
        -Complex.I * ⟪cutC (W (2 * π)) (basisVec 0), cutS (W (2 * π)) (basisVec 0)⟫_ℂ ∧
      conj (l2Inner q (periodicA W nq q)) = l2Inner q (periodicA W nq q) := by
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have hcd := inner_cutC_cutD hU (basisVec 0)
  rw [inner_smul_right] at hcd
  have ha : l2Inner q (periodicA W nq q) =
      -Complex.I * ⟪cutC (W (2 * π)) (basisVec 0), cutS (W (2 * π)) (basisVec 0)⟫_ℂ := by
    have h1 := inner_observationAdj hW.1 hq hqB (cutS (W (2 * π)) (basisVec 0))
    rw [hadj, inner_smul_left, Complex.conj_I] at h1
    have hL : (0 : ℝ) ≤ 2 * π := by positivity
    rw [l2Inner, intervalIntegral.integral_congr (g := fun s =>
      conj (q s) * observation W (cutS (W (2 * π)) (basisVec 0)) s) (fun s hs => by
        rw [uIcc_of_le hL] at hs
        simp only [periodicA_radial hW.1 hq hqB hadj hnq hs]), ← h1]
  refine ⟨ha, ?_⟩
  have : l2Inner q (periodicA W nq q) = -((-2 * (⟪basisVec 0, W (2 * π) (basisVec 0)⟫_ℂ).im : ℝ) : ℂ) := by
    rw [ha, ← hcd]; ring
  rw [this, map_neg, Complex.conj_ofReal]

/-- **Lemma 8.3 (matching endpoints).** Let `q` satisfy the radial hypotheses (`O_E^* q = i c_E`
and `𝒩(E) q = O_E e₀ - i T_E q`), let `a_E = ⟨q, 𝒜_E q⟩ ≠ 0`, and let the Neumann trace `n` of
`g` be periodic. Then the output of the Schur complement has matching endpoint values. -/
theorem schurC_periodic {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {nq q : ℝ → ℂ}
    (hq : AEStronglyMeasurable q volume) {B : ℝ} (hqB : ∀ s, ‖q s‖ ≤ B)
    (hadj : observationAdj W q = Complex.I • cutC (W (2 * π)) (basisVec 0))
    (hnq : ∀ θ ∈ Icc 0 (2 * π),
      nq θ = observation W (basisVec 0) θ - Complex.I * volterraOp W q θ)
    (ha : l2Inner q (periodicA W nq q) ≠ 0) {n g : ℝ → ℂ} (hn : n (2 * π) = n 0)
    (hg : AEStronglyMeasurable g volume) {B' : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B') :
    schurC W nq q n g (2 * π) = schurC W nq q n g 0 := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hA := periodicA_jump hW.1 (transport_zero hW) hn hg hgB
  rw [inner_observationAdj_right hW.1 hg hgB,
    ← l2Inner_periodicA_radial hW.1 hq hqB hadj hnq] at hA
  have hb := observation_jump hW (cutS (W (2 * π)) (basisVec 0))
  rw [← periodicA_radial hW.1 hq hqB hadj hnq ⟨hL, le_rfl⟩,
    ← periodicA_radial hW.1 hq hqB hadj hnq ⟨le_rfl, hL⟩] at hb
  have hcs := (l2Inner_radial_eq hK hW hq hqB hadj hnq).1
  rw [← sub_eq_zero, schurC, schurC]
  set a := l2Inner q (periodicA W nq q)
  have hcs' : ⟪cutC (W (2 * π)) (basisVec 0), cutS (W (2 * π)) (basisVec 0)⟫_ℂ =
      Complex.I * a := by
    rw [hcs]
    linear_combination (⟪cutC (W (2 * π)) (basisVec 0),
      cutS (W (2 * π)) (basisVec 0)⟫_ℂ) * Complex.I_sq
  rw [hcs'] at hb
  field_simp
  linear_combination a * hA - l2Inner (periodicA W nq q) g * hb

/-- **Lemma 8.3 (`C^sc_E q_E = 0`).** Under the radial hypotheses and `a_E ≠ 0`, the Schur
complement annihilates `q` on `[0, L]`. -/
theorem schurC_radial {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {nq q : ℝ → ℂ}
    (hq : AEStronglyMeasurable q volume) {B : ℝ} (hqB : ∀ s, ‖q s‖ ≤ B)
    (hadj : observationAdj W q = Complex.I • cutC (W (2 * π)) (basisVec 0))
    (hnq : ∀ θ ∈ Icc 0 (2 * π),
      nq θ = observation W (basisVec 0) θ - Complex.I * volterraOp W q θ)
    (ha : l2Inner q (periodicA W nq q) ≠ 0) (θ : ℝ) :
    schurC W nq q nq q θ = 0 := by
  have hreal := (l2Inner_radial_eq hK hW hq hqB hadj hnq).2
  have hsymm : l2Inner (periodicA W nq q) q = conj (l2Inner q (periodicA W nq q)) := by
    rw [l2Inner, l2Inner, ← intervalIntegral_conj]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [schurC, hsymm, hreal]
  field_simp
  ring

/-- **Lemma 8.3 (`C^sc_E 𝒥_E h = 0` for `h(0) = 0`).** If `O_E^* g = 0` and the Neumann trace of
`g` is `n = -i T_E g` on `[0, L]`, then `C^sc_E g = 0` on `[0, L]`. -/
theorem schurC_of_observationAdj_eq_zero {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : ContinuousOn W (Icc 0 (2 * π))) {nq q : ℝ → ℂ}
    (hq : AEStronglyMeasurable q volume) {B : ℝ} (hqB : ∀ s, ‖q s‖ ≤ B)
    (hadjq : observationAdj W q = Complex.I • cutC (W (2 * π)) (basisVec 0))
    (hnq : ∀ θ ∈ Icc 0 (2 * π),
      nq θ = observation W (basisVec 0) θ - Complex.I * volterraOp W q θ)
    {n g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B' : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B')
    (hadj : observationAdj W g = 0)
    (hn : ∀ θ ∈ Icc 0 (2 * π), n θ = -Complex.I * volterraOp W g θ)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    schurC W nq q n g θ = 0 := by
  have hA := ((periodicP_of_observationAdj_eq_zero hW hg hgB hadj hn).1 θ hθ).1
  have hb : l2Inner (periodicA W nq q) g = 0 := by
    rw [l2Inner_periodicA_radial hW hq hqB hadjq hnq, ← inner_observationAdj_right hW hg hgB,
      hadj, inner_zero_right]
  rw [schurC, hA, hb]
  ring

end PolyaNeumann
