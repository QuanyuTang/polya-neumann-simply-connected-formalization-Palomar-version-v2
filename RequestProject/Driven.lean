module

public import RequestProject.CurveContinuity

/-!
# Driven transport equations and their endpoint identities (Lemma 4.10)

For a Lipschitz curve `γ`, an energy `E` and the transport `W = W_E`, consider an
`ℓ²(ℕ₀)`-valued solution `y` of the driven equation `y' = C_E y + f` (in integral form).
Variation of constants gives `y(θ) = W(θ) (y(0) + ∫₀^θ W(s)^* f(s) ds)`.

For the paper's forcing `f = -(i/√2) g e₀` this yields Lemma 4.10:
* `√2 ⟨e₀, y(θ)⟩ = √2 (O_E v)(θ) - i (T_E g)(θ)` (the trace identity `h_a = √2 O_E v - i T_E g`),
* if moreover `y(L) = y(0) = v`, then `(I - V_E) v = -(i/√2) V_E O_E^* g` and
  `O_E^* g = √2 i (V_E^* - I) v`,

where `(O_E v)(θ) = ⟨e₀, W(θ) v⟩`, `(T_E g)(θ) = ∫₀^θ ⟨e₀, W(θ) W(s)^* e₀⟩ g(s) ds` and
`O_E^* g = ∫₀^L g(s) W(s)^* e₀ ds`.  We also prove the adjoint formula for `O_E^*` and the
kernel identity `T_E + T_E^* = O_E O_E^*` of Lemma 4.6.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- The observation map `(O_E v)(θ) = ⟨e₀, W(θ) v⟩`. -/
def observation (W : ℝ → Ell2 →L[ℂ] Ell2) (v : Ell2) (θ : ℝ) : ℂ :=
  inner ℂ (basisVec 0) (W θ v)

/-- The adjoint observation map `O_E^* g = ∫₀^L g(s) W(s)^* e₀ ds`. -/
def observationAdj (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) : Ell2 :=
  ∫ s in (0 : ℝ)..(2 * π), g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)

/-- The Volterra kernel `k(θ, s) = ⟨e₀, W(θ) W(s)^* e₀⟩`. -/
def volterraKernel (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) : ℂ :=
  inner ℂ (basisVec 0) (W θ (ContinuousLinearMap.adjoint (W s) (basisVec 0)))

/-- The Volterra operator `(T_E g)(θ) = ∫₀^θ ⟨e₀, W(θ) W(s)^* e₀⟩ g(s) ds`. -/
def volterraOp (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..θ, volterraKernel W θ s * g s

/-- The adjoint Volterra operator `(T_E^* g)(θ) = ∫_θ^L conj(k(s, θ)) g(s) ds`. -/
def volterraOpAdj (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in θ..(2 * π), conj (volterraKernel W s θ) * g s

/-- Compatibility instance: real scalars commute with the adjoint star on complex operators. -/
instance instStarModuleRealCLMComplex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : StarModule ℝ (E →L[ℂ] E) :=
  ⟨fun r A => by
    have h : ∀ B : E →L[ℂ] E, r • B = (r : ℂ) • B := fun B =>
      RCLike.real_smul_eq_coe_smul (K := ℂ) r B
    rw [star_trivial r, h, h, star_smul, Complex.star_def, Complex.conj_ofReal]⟩

/-- A bounded Lipschitz family of operators applied to a bounded Lipschitz family of vectors
is Lipschitz. -/
theorem lipschitzOnWith_apply_of_bounded {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℝ → E →L[ℂ] F}
    {g : ℝ → E} {s : Set ℝ} {Kf Kg : NNReal} {B : ℝ} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) (hfB : ∀ x ∈ s, ‖f x‖ ≤ B) (hgB : ∀ x ∈ s, ‖g x‖ ≤ B) :
    LipschitzOnWith (Kf * B.toNNReal + B.toNNReal * Kg) (fun x => f x (g x)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hB : 0 ≤ B := (norm_nonneg _).trans (hfB x hx)
  have h1 := hf.dist_le_mul x hx y hy
  have h2 := hg.dist_le_mul x hx y hy
  rw [dist_eq_norm] at h1 h2 ⊢
  have e : f x (g x) - f y (g y) = (f x - f y) (g x) + f y (g x - g y) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
  rw [e]
  push_cast
  rw [Real.coe_toNNReal _ hB]
  calc ‖(f x - f y) (g x) + f y (g x - g y)‖
      ≤ ‖f x - f y‖ * ‖g x‖ + ‖f y‖ * ‖g x - g y‖ :=
        (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
          (ContinuousLinearMap.le_opNorm _ _))
    _ ≤ (Kf * dist x y) * B + B * (Kg * dist x y) := by
        gcongr
        · exact hgB x hx
        · exact hfB y hy
    _ = _ := by ring

/-- Product rule for a family of complex-linear operators applied to a family of vectors,
differentiated with respect to a real parameter. -/
theorem hasDerivAt_clm_apply_real {A : ℝ → Ell2 →L[ℂ] Ell2} {A' : Ell2 →L[ℂ] Ell2}
    {u : ℝ → Ell2} {u' : Ell2} {θ : ℝ} (hA : HasDerivAt A A' θ) (hu : HasDerivAt u u' θ) :
    HasDerivAt (fun x => A x (u x)) (A' (u θ) + A θ u') θ :=
  ((ContinuousLinearMap.restrictScalarsL ℂ Ell2 Ell2 ℝ ℝ).hasFDerivAt.comp_hasDerivAt θ
    hA).clm_apply hu

/-- Variation of constants for the driven transport equation: if `y` solves
`y(θ) = y(0) + ∫₀^θ (C_E y + f)` on `[0, L]` with a bounded measurable forcing `f`, then
`y(θ) = W(θ) (y(0) + ∫₀^θ W(s)^* f(s) ds)`. -/
theorem driven_eq_transport {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {f : ℝ → Ell2}
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (hfB : ∀ s, ‖f s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (y s) + f s)) :
    ∀ θ ∈ Icc 0 (2 * π),
      y θ = W θ (y 0 + ∫ s in (0 : ℝ)..θ, ContinuousLinearMap.adjoint (W s) (f s)) := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, hL⟩
  set C := transportCoeff γ E with hCdef
  have hC : AEStronglyMeasurable C volume := transportCoeff_aestronglyMeasurable γ E
  have hM := transportCoeff_norm_le γ E hK
  set M := ‖(-(Complex.I * (Real.sqrt E : ℂ)) / 2)‖ *
      (K * ‖(ContinuousLinearMap.adjoint shiftN : Ell2 →L[ℂ] Ell2)‖ + K * ‖shiftN‖)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hfB 0)
  obtain ⟨Sy, hSy⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  have hSy0 : 0 ≤ Sy := (norm_nonneg _).trans (hSy 0 h0)
  have happ : Continuous fun p : (Ell2 →L[ℂ] Ell2) × Ell2 => p.1 p.2 := by fun_prop
  -- the integrand of the driven equation
  set G : ℝ → Ell2 := fun s => C s (y s) + f s with hG
  have hGm : AEStronglyMeasurable G (volume.restrict (Icc 0 (2 * π))) :=
    (happ.comp_aestronglyMeasurable₂ hC.restrict
      (hy.aestronglyMeasurable measurableSet_Icc)).add hf.restrict
  have hGB : ∀ x ∈ Icc 0 (2 * π), ‖G x‖ ≤ M * Sy + B := fun x hx =>
    (norm_add_le _ _).trans (add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hM x) (hSy x hx) (norm_nonneg _) hM0)) (hfB x))
  have hGi : IntegrableOn G (Icc 0 (2 * π)) :=
    Integrable.of_bound hGm (M * Sy + B)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hGB))
  have hGii : ∀ θ ∈ Icc 0 (2 * π), IntervalIntegrable G volume 0 θ := fun θ hθ =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hθ.1).mpr
      (hGi.mono_set (Icc_subset_Icc le_rfl hθ.2))
  -- `y` is Lipschitz with a.e. derivative `G`
  have hyL : LipschitzOnWith (M * Sy + B).toNNReal y (Icc 0 (2 * π)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
    rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity), Real.dist_eq, ey x hx, ey x' hx',
      add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hGii x hx) (hGii x' hx')]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hGB t ?_
    have := uIoc_subset_uIcc ht
    rw [mem_uIcc] at this
    rcases this with h | h
    · exact ⟨hx'.1.trans h.1, h.2.trans hx.2⟩
    · exact ⟨hx.1.trans h.1, h.2.trans hx'.2⟩
  have hyd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) → HasDerivAt y (G θ) θ := by
    set g : ℝ → Ell2 := (Icc 0 (2 * π)).indicator G
    have hgi : Integrable g := hGi.integrable_indicator measurableSet_Icc
    filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hgi.locallyIntegrable]
      with θ hθ hmem
    have hmem' : θ ∈ Icc 0 (2 * π) := Ioo_subset_Icc_self hmem
    have h1 := (hθ 0).const_add (y 0)
    rw [show g θ = G θ by simp [g, indicator_of_mem hmem']] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
    rw [ey x (Ioo_subset_Icc_self hx)]
    congr 1
    refine intervalIntegral.integral_congr fun t ht => ?_
    have : t ∈ Icc 0 (2 * π) := by
      rw [uIcc_of_le hx.1.le] at ht; exact ⟨ht.1, ht.2.trans hx.2.le⟩
    simp [g, G, indicator_of_mem this]
  -- facts about `W^*`
  have hW0 : W 0 = 1 := by simpa using hW.2 0 h0
  obtain ⟨KW, hKW⟩ := volterra_lipschitzOn hC hM hW.1 hW.2
  have hKWs : LipschitzOnWith KW (fun θ => star (W θ)) (Icc 0 (2 * π)) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        ← map_sub, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
      exact hKW.dist_le_mul x hx y hy
  have hWs1 : ∀ x ∈ Icc 0 (2 * π), ‖star (W x)‖ ≤ 1 := fun x hx => by
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
    exact norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hx)
  have hds : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) →
      HasDerivAt (fun θ => star (W θ)) (-(star (W θ) * C θ)) θ := by
    filter_upwards [volterra_ae_hasDerivAt hC hM hW.1 hW.2] with θ hθ hmem
    have := (hθ hmem).star
    rw [star_mul, hCdef, transportCoeff_star] at this
    convert this using 1
    ext1 v
    simp [hCdef]
  -- `z = W^* y` has a.e. derivative `W^* f`
  set S := max 1 (Sy + 1) with hS
  have hzL := lipschitzOnWith_apply_of_bounded hKWs hyL (B := S)
    (fun x hx => (hWs1 x hx).trans (le_max_left _ _))
    (fun x hx => (hSy x hx).trans ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
  set g : ℝ → Ell2 := fun s => star (W s) (f s) with hg
  have hgB : ∀ x ∈ Icc 0 (2 * π), ‖g x‖ ≤ B := fun x hx =>
    (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul (hWs1 x hx) (hfB x) (norm_nonneg _) zero_le_one).trans_eq (one_mul B))
  haveI : SecondCountableTopologyEither ℝ (Ell2 →L[ℂ] Ell2) :=
    secondCountableTopologyEither_of_left _ _
  have hWm : AEStronglyMeasurable W (volume.restrict (Icc 0 (2 * π))) :=
    hW.1.aestronglyMeasurable measurableSet_Icc
  have hWsm : AEStronglyMeasurable (fun s => star (W s)) (volume.restrict (Icc 0 (2 * π))) := by
    have hcont : Continuous fun A : Ell2 →L[ℂ] Ell2 => star A := continuous_star
    exact hcont.comp_aestronglyMeasurable hWm
  have hgm : AEStronglyMeasurable g (volume.restrict (Icc 0 (2 * π))) :=
    happ.comp_aestronglyMeasurable₂ hWsm hf.restrict
  have hgi : IntegrableOn g (Icc 0 (2 * π)) :=
    Integrable.of_bound hgm B
      ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hgB))
  have hz := eq_add_integral_of_ae_hasDerivAt hzL hgi hgB (by
    filter_upwards [hyd, hds] with θ h1 h2 hmem
    have := hasDerivAt_clm_apply_real (h2 hmem) (h1 hmem)
    convert this using 1
    simp only [g, G, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply, map_add]
    abel)
  intro θ hθ
  have h1 := hz θ hθ
  rw [hW0, star_one, ContinuousLinearMap.one_apply] at h1
  have hu : W θ * star (W θ) = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint]; exact transport_mul_adjoint hK hW hθ
  have e1 : y θ = W θ (star (W θ) (y θ)) := by
    rw [← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply]
  rw [e1, h1]
  congr 2


/-- A bounded measurable scalar function times a function continuous on `[0, L]` is interval
integrable between any two points of `[0, L]`. -/
lemma intervalIntegrable_smul_of_continuousOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {u : ℝ → F} (hu : ContinuousOn u (Icc 0 (2 * π))) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {a b : ℝ}
    (ha : a ∈ Icc 0 (2 * π)) (hb : b ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (fun s => g s • u s) volume a b := by
  have hsub : uIcc a b ⊆ Icc 0 (2 * π) := uIcc_subset_Icc ha hb
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hm : AEStronglyMeasurable (fun s => g s • u s) (volume.restrict (Icc 0 (2 * π))) :=
    hg.restrict.smul (hu.aestronglyMeasurable measurableSet_Icc)
  have hI : IntegrableOn (fun s => g s • u s) (Icc 0 (2 * π)) :=
    Integrable.of_bound hm (B * S) ((ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall fun s hs => by
        rw [norm_smul]
        exact mul_le_mul (hgB s) (hS s hs) (norm_nonneg _) ((norm_nonneg _).trans (hgB s))))
  exact intervalIntegrable_iff.mpr (hI.mono_set (uIoc_subset_uIcc.trans hsub))

/-- `s ↦ W(s)^* e₀` is continuous on `[0, L]`. -/
lemma continuousOn_adjoint_apply {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    (x : Ell2) : ContinuousOn (fun s => ContinuousLinearMap.adjoint (W s) x) (Icc 0 (2 * π)) := by
  have h1 : ContinuousOn (fun s => ContinuousLinearMap.adjoint (W s)) (Icc 0 (2 * π)) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.comp_continuousOn hW
  exact h1.clm_apply continuousOn_const

/-- Pulling the observation functional `⟨e₀, W(θ) ·⟩` inside the integral defining `O_E^*`:
`⟨e₀, W(θ) ∫_a^b g(s) W(s)^* e₀ ds⟩ = ∫_a^b k(θ, s) g(s) ds`. -/
lemma inner_transport_integral {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (θ : ℝ)
    {a b : ℝ} (ha : a ∈ Icc 0 (2 * π)) (hb : b ∈ Icc 0 (2 * π)) :
    inner ℂ (basisVec 0) (W θ (∫ s in a..b, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))) =
      ∫ s in a..b, volterraKernel W θ s * g s := by
  have hi := intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB ha hb
  set Lf : Ell2 →L[ℂ] ℂ := (innerSL ℂ (basisVec 0)).comp (W θ)
  have := Lf.intervalIntegral_comp_comm hi
  simp only [Lf, ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul,
    smul_eq_mul] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [volterraKernel]
  ring

/-- Variation of constants for the paper's forcing `-(i/√2) g e₀`:
`y(θ) = W(θ) y(0) - (i/√2) W(θ) ∫₀^θ g(s) W(s)^* e₀ ds`. -/
theorem driven_formula {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in (0 : ℝ)..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0)) :
    ∀ θ ∈ Icc 0 (2 * π), y θ = W θ (y 0) + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
      W θ (∫ s in (0 : ℝ)..θ, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) := by
  set c : ℂ := -(Complex.I / (Real.sqrt 2 : ℂ))
  have hf : AEStronglyMeasurable (fun s => (c * g s) • basisVec 0) volume :=
    (hg.const_mul c).smul_const _
  have hfB : ∀ s, ‖(c * g s) • basisVec 0‖ ≤ ‖c‖ * B * ‖basisVec 0‖ := fun s => by
    rw [norm_smul, norm_mul]
    gcongr
    exact hgB s
  intro θ hθ
  rw [driven_eq_transport hK hW hf hfB hy ey θ hθ, map_add, ← map_smul]
  congr 2
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [map_smul, smul_smul]

/-- **Lemma 4.10 (trace identity).**  Let `y` solve the driven equation
`y' = C_E y - (i/√2) g e₀` on `[0, L]` (in integral form), with `g` bounded and measurable,
and let `v = y(0)`.  Then `h = √2 ⟨e₀, y⟩` satisfies `h = √2 O_E v - i T_E g` on `[0, L]`. -/
theorem driven_trace {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in (0 : ℝ)..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0)) :
    ∀ θ ∈ Icc 0 (2 * π), (Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0) (y θ) =
      (Real.sqrt 2 : ℂ) * observation W (y 0) θ - Complex.I * volterraOp W g θ := by
  intro θ hθ
  rw [driven_formula hK hW hg hgB hy ey θ hθ, inner_add_right, inner_smul_right,
    inner_transport_integral hW.1 hg hgB θ ⟨le_rfl, hθ.1.trans hθ.2⟩ hθ]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [observation, volterraOp]
  field_simp
  ring

/-- **Lemma 4.10 (endpoint identities).**  If in addition `y` is periodic, `y(L) = y(0) = v`,
then `(I - V_E) v = -(i/√2) V_E O_E^* g` and `O_E^* g = √2 i (V_E^* - I) v`. -/
theorem driven_endpoint {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in (0 : ℝ)..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0))
    (hper : y (2 * π) = y 0) :
    (1 - W (2 * π)) (y 0) = (-(Complex.I / (Real.sqrt 2 : ℂ))) • W (2 * π) (observationAdj W g) ∧
      observationAdj W g =
        ((Real.sqrt 2 : ℂ) * Complex.I) • (ContinuousLinearMap.adjoint (W (2 * π)) - 1) (y 0) := by
  have hL : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hform := driven_formula hK hW hg hgB hy ey (2 * π) hL
  rw [hper] at hform
  have hform' : y 0 = W (2 * π) (y 0) + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
      W (2 * π) (observationAdj W g) := hform
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    nth_rewrite 1 [hform']
    abel
  · have hu : ContinuousLinearMap.adjoint (W (2 * π)) * W (2 * π) = 1 := by
      have := (transport_mem_unitary hK hW hL)
      rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at this
      exact this.1
    have hV : ContinuousLinearMap.adjoint (W (2 * π)) (y 0) =
        y 0 + (-(Complex.I / (Real.sqrt 2 : ℂ))) • observationAdj W g := by
      conv_lhs => rw [hform']
      rw [map_add, map_smul, ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, hu,
        ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hV, add_sub_cancel_left,
      smul_smul]
    have : (Real.sqrt 2 : ℂ) * Complex.I * -(Complex.I / (Real.sqrt 2 : ℂ)) = 1 := by
      field_simp
      rw [Complex.I_sq]
      ring
    rw [this, one_smul]

/-- **Lemma 4.6 (adjoint formula).**  `O_E^* g = ∫₀^L W(s)^* e₀ g(s) ds` is the adjoint of
the observation map: `⟨O_E^* g, v⟩ = ∫₀^L conj(g(s)) (O_E v)(s) ds`. -/
theorem inner_observationAdj {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (v : Ell2) :
    inner ℂ (observationAdj W g) v =
      ∫ s in (0 : ℝ)..(2 * π), conj (g s) * observation W v s := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hi := intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩
  have := (innerSL ℂ v).intervalIntegral_comp_comm hi
  simp only [innerSL_apply_apply] at this
  rw [observationAdj, ← inner_conj_symm, ← this, intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_of_le hL, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [inner_smul_right, map_mul, inner_conj_symm,
    ContinuousLinearMap.adjoint_inner_left, observation]

/-- **Lemma 4.6 (`T_E + T_E^* = O_E O_E^*`).**  The kernels of the Volterra operator and its
adjoint combine to that of `O_E O_E^*`. -/
theorem volterraOp_add_adj {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    volterraOp W g θ + volterraOpAdj W g θ = observation W (observationAdj W g) θ := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hk : ∀ s, conj (volterraKernel W s θ) = volterraKernel W θ s := fun s => by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have hkc : ContinuousOn (fun s => volterraKernel W θ s) (Icc 0 (2 * π)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have hint : ∀ {a b : ℝ}, a ∈ Icc 0 (2 * π) → b ∈ Icc 0 (2 * π) →
      IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume a b := fun ha hb => by
    have := intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    simpa only [smul_eq_mul, mul_comm] using this
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, hL⟩
  have hL' : (2 * π) ∈ Icc 0 (2 * π) := ⟨hL, le_rfl⟩
  simp only [volterraOpAdj, hk, volterraOp]
  rw [intervalIntegral.integral_add_adjacent_intervals (hint h0 hθ) (hint hθ hL'), observation,
    observationAdj, inner_transport_integral hW hg hgB θ h0 hL']

/-- Complex conjugation commutes with interval integrals. -/
lemma intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-- **Lemma 4.6 (`T_E^*` is the adjoint of `T_E`).**  For bounded measurable `g` and `h`,
`∫₀^L conj(h(θ)) (T_E g)(θ) dθ = ∫₀^L conj((T_E^* h)(s)) g(s) ds`, i.e. the operator
`volterraOpAdj` with kernel `conj(k(s, θ))` on `s > θ` is the `L²(0, L)`-adjoint of `T_E`. -/
theorem volterraOp_adjoint {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g h : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    (hh : AEStronglyMeasurable h volume) {B' : ℝ} (hhB : ∀ s, ‖h s‖ ≤ B') :
    ∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * volterraOp W g θ =
      ∫ s in (0 : ℝ)..(2 * π), conj (volterraOpAdj W h s) * g s := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  haveI : SecondCountableTopologyEither ℝ (Ell2 →L[ℂ] Ell2) :=
    secondCountableTopologyEither_of_left _ _
  set μ : Measure ℝ := volume.restrict (Icc 0 (2 * π)) with hμ
  set u : ℝ → Ell2 := fun s => ContinuousLinearMap.adjoint (W s) (basisVec 0) with hudef
  have hu : ContinuousOn u (Icc 0 (2 * π)) := continuousOn_adjoint_apply hW (basisVec 0)
  obtain ⟨S1, hS1⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  obtain ⟨S2, hS2⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hS1' : 0 ≤ S1 := (norm_nonneg _).trans (hS1 0 ⟨le_rfl, hL⟩)
  have hB' : 0 ≤ B' := (norm_nonneg _).trans (hhB 0)
  set Φ : ℝ → ℝ → ℂ := fun θ s =>
    if s ≤ θ then conj (h θ) * (volterraKernel W θ s * g s) else 0 with hΦdef
  have happ : Continuous fun p : (Ell2 →L[ℂ] Ell2) × Ell2 => p.1 p.2 := by fun_prop
  have hΦ : Integrable (Function.uncurry Φ) (μ.prod μ) := by
    have hWm : AEStronglyMeasurable W μ := hW.aestronglyMeasurable measurableSet_Icc
    have hum : AEStronglyMeasurable u μ := hu.aestronglyMeasurable measurableSet_Icc
    have hk : AEStronglyMeasurable (fun p : ℝ × ℝ => volterraKernel W p.1 p.2) (μ.prod μ) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.1 (u p.2)) (μ.prod μ) :=
        happ.comp_aestronglyMeasurable₂ hWm.comp_fst hum.comp_snd
      exact (innerSL ℂ (basisVec 0)).continuous.comp_aestronglyMeasurable h1
    have hf : AEStronglyMeasurable
        (fun p : ℝ × ℝ => conj (h p.1) * (volterraKernel W p.1 p.2 * g p.2)) (μ.prod μ) :=
      (Complex.continuous_conj.comp_aestronglyMeasurable hh.restrict).comp_fst.mul
        (hk.mul hg.restrict.comp_snd)
    have heq : Function.uncurry Φ = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
        (fun p : ℝ × ℝ => conj (h p.1) * (volterraKernel W p.1 p.2 * g p.2)) := by
      funext p
      simp only [Function.uncurry, Φ, Set.indicator, mem_setOf_eq]
    have hm : AEStronglyMeasurable (Function.uncurry Φ) (μ.prod μ) := by
      rw [heq]
      exact hf.indicator (measurableSet_le measurable_snd measurable_fst)
    refine Integrable.of_bound hm (B' * (‖basisVec 0‖ * (S1 * S2)) * B) ?_
    rw [hμ, Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).mpr
      (Eventually.of_forall fun p hp => ?_)
    simp only [Function.uncurry, Φ]
    split_ifs
    · rw [norm_mul, norm_mul, Complex.norm_conj]
      have hk' : ‖volterraKernel W p.1 p.2‖ ≤ ‖basisVec 0‖ * (S1 * S2) := by
        refine (norm_inner_le_norm _ _).trans ?_
        gcongr
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        exact mul_le_mul (hS1 _ hp.1) (hS2 _ hp.2) (norm_nonneg _) hS1'
      have hkn : 0 ≤ ‖basisVec 0‖ * (S1 * S2) := (norm_nonneg _).trans hk'
      calc ‖h p.1‖ * (‖volterraKernel W p.1 p.2‖ * ‖g p.2‖)
          ≤ B' * (‖basisVec 0‖ * (S1 * S2) * B) := by
            gcongr
            · exact hhB _
            · exact hgB _
        _ = _ := by ring
    · rw [norm_zero]
      have : 0 ≤ ‖basisVec 0‖ * (S1 * S2) :=
        mul_nonneg (norm_nonneg _) (mul_nonneg hS1' ((norm_nonneg _).trans (hS2 0 ⟨le_rfl, hL⟩)))
      have := (norm_nonneg _).trans (hgB 0)
      positivity
  have key := integral_integral_swap hΦ
  have hlhs : ∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * volterraOp W g θ =
      ∫ θ, ∫ s, Φ θ s ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    have e : (fun s => Φ θ s) =
        (Iic θ).indicator (fun s => conj (h θ) * (volterraKernel W θ s * g s)) := by
      funext s; simp only [Φ, Set.indicator, mem_Iic]
    have e2 : Icc 0 (2 * π) ∩ Iic θ = Icc 0 θ := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hθ.2⟩, h3⟩
    simp only [hμ]
    rw [e, setIntegral_indicator measurableSet_Iic, e2, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hθ.1, volterraOp, intervalIntegral.integral_const_mul]
  have hrhs : ∫ s in (0 : ℝ)..(2 * π), conj (volterraOpAdj W h s) * g s =
      ∫ s, ∫ θ, Φ θ s ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have e : (fun θ => Φ θ s) =
        (Ici s).indicator (fun θ => conj (h θ) * (volterraKernel W θ s * g s)) := by
      funext θ; simp only [Φ, Set.indicator, mem_Ici]
    have e2 : Icc 0 (2 * π) ∩ Ici s = Icc s (2 * π) := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hs.1.trans h1, h2⟩, h1⟩
    simp only [hμ]
    rw [e, setIntegral_indicator measurableSet_Ici, e2, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hs.2, volterraOpAdj, ← intervalIntegral_conj,
      ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hlhs, hrhs, key]

end PolyaNeumann

end
