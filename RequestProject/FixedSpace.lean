module

public import RequestProject.Herglotz
public import RequestProject.NeumannEigenspace
public import RequestProject.CayleyFactorization

/-!
# The fixed space of the monodromy and Herglotz-compatible traces (Lemma 10.5)

The paper proves `dim ker(V_E - I) ≤ dim ker(A_N - E)` in two steps:

1. (pairing step, proved here) if `V_E v = v`, the observation `f₀ = O_E v = ⟨e₀, W_E(·) v⟩`
   is a Lipschitz closed boundary function orthogonal to the conormal trace `g_a` of every
   Herglotz wave (`observation_mem_compatibleTraces`, from Lemma 4.4 in `Herglotz.lean`);
2. (Cauchy reconstruction, Lemma 4.8) every such compatible boundary function `h` is the
   Dirichlet trace of a unique Helmholtz solution with zero Neumann data, i.e. of a Neumann
   eigenfunction, depending linearly on `h`.

We formalize the space of compatible traces (`compatibleTraces`) and deduce the injective map
from the fixed space into the Neumann eigenspace from any linear reconstruction map that only
kills traces vanishing on `[0, L]` (`fixedSpace_to_neumannEigenspace_of_reconstruction`),
using the injectivity of the observation map (Lemma 10.4).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- The boundary functions `h` on `[0, L]` compatible with the Herglotz waves at energy `E`:
`h` is Lipschitz on `[0, L]` (in particular in `H¹`), closed (`h(L) = h(0)`), and
`∫₀^L conj(g_a) h = 0` for the conormal trace `g_a` of every Herglotz wave with `L²` direction
density `a` (the compatibility condition of Lemma 4.8 with zero conormal data). -/
def compatibleTraces (γ : ℝ → ℂ) (E : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {h | (∃ K, LipschitzOnWith K h (Icc 0 (2 * π))) ∧ h (2 * π) = h 0 ∧
    ∀ a, IsDirDensity a →
      IntervalIntegrable (fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * h s) volume 0
        (2 * π) ∧
      ∫ s in (0 : ℝ)..(2 * π), conj (herglotzConormal (Real.sqrt E) a γ s) * h s = 0}
  zero_mem' := ⟨⟨0, LipschitzOnWith.of_dist_le_mul fun x _ y _ => by simp⟩, rfl, fun a _ => by
    simp⟩
  add_mem' := by
    rintro h₁ h₂ ⟨⟨K₁, hK₁⟩, hc₁, hi₁⟩ ⟨⟨K₂, hK₂⟩, hc₂, hi₂⟩
    refine ⟨⟨K₁ + K₂, hK₁.add hK₂⟩, by simp [hc₁, hc₂], fun a ha => ?_⟩
    obtain ⟨hI₁, hZ₁⟩ := hi₁ a ha
    obtain ⟨hI₂, hZ₂⟩ := hi₂ a ha
    have heq : (fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * (h₁ + h₂) s) =
        fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * h₁ s +
          conj (herglotzConormal (Real.sqrt E) a γ s) * h₂ s := by
      funext s; simp only [Pi.add_apply]; ring
    rw [heq]
    exact ⟨hI₁.add hI₂, by rw [intervalIntegral.integral_add hI₁ hI₂, hZ₁, hZ₂, add_zero]⟩
  smul_mem' := by
    rintro c h ⟨⟨K, hK⟩, hc, hi⟩
    refine ⟨⟨‖c‖₊ * K, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩, by simp [hc],
      fun a ha => ?_⟩
    · rw [dist_eq_norm, Pi.smul_apply, Pi.smul_apply, ← smul_sub, norm_smul, NNReal.coe_mul,
        coe_nnnorm, mul_assoc, ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (hK.dist_le_mul x hx y hy) (norm_nonneg _)
    · obtain ⟨hI, hZ⟩ := hi a ha
      have heq : (fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * (c • h) s) =
          fun s => c * (conj (herglotzConormal (Real.sqrt E) a γ s) * h s) := by
        funext s; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [heq]
      exact ⟨hI.const_mul c, by rw [intervalIntegral.integral_const_mul, hZ, mul_zero]⟩

/-- The observation `O_E v` of a fixed vector `V_E v = v` of the monodromy of a closed
Lipschitz curve is a compatible trace (Lemma 10.5, pairing step). -/
theorem observation_mem_compatibleTraces {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {v : Ell2} (hv : W (2 * π) v = v) : observation W v ∈ compatibleTraces γ E := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  obtain ⟨KW, hKW⟩ := volterra_lipschitzOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2
  have hW0 : W 0 = 1 := by simpa using hW.2 0 ⟨le_rfl, hπ⟩
  have hcont : ContinuousOn (observation W v) (Icc 0 (2 * π)) :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  refine ⟨⟨KW * ‖v‖₊, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩, ?_, fun a ha => ?_⟩
  · rw [dist_eq_norm, observation, observation, ← inner_sub_right, ← ContinuousLinearMap.sub_apply]
    refine (norm_inner_le_norm _ _).trans ?_
    have hb : ‖basisVec 0‖ = 1 := by simp [basisVec]
    rw [hb, one_mul, NNReal.coe_mul, coe_nnnorm]
    refine ((W x - W y).le_opNorm v).trans ?_
    rw [← dist_eq_norm]
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hKW.dist_le_mul x hx y hy) (norm_nonneg v)
  · simp only [observation, hv, hW0, ContinuousLinearMap.one_apply]
  · obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
    refine ⟨?_, integral_conj_herglotzConormal_mul_observation hK hclosed hW hv ha⟩
    have := intervalIntegrable_smul_of_continuousOn hcont
      (g := fun s => conj (herglotzConormal (Real.sqrt E) a γ s))
      (Complex.continuous_conj.comp_aestronglyMeasurable hgm)
      (B := B) (fun s => by rw [Complex.norm_conj]; exact hgB s) ⟨le_rfl, hπ⟩ ⟨hπ, le_rfl⟩
    simpa [smul_eq_mul] using this

/-- The observation map restricted to the fixed space `ker(V_E - I)`, with values in the
compatible traces. -/
def observationFixed {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) →ₗ[ℂ]
      compatibleTraces γ E where
  toFun v := ⟨observation W v, observation_mem_compatibleTraces hK hclosed hW (by
    have := v.2
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero] at this
    exact this)⟩
  map_add' v w := by
    ext θ
    show inner ℂ (basisVec 0) (W θ ((v : Ell2) + (w : Ell2))) =
      inner ℂ (basisVec 0) (W θ v) + inner ℂ (basisVec 0) (W θ w)
    rw [map_add, inner_add_right]
  map_smul' c v := by
    ext θ
    show inner ℂ (basisVec 0) (W θ (c • (v : Ell2))) = c * inner ℂ (basisVec 0) (W θ v)
    rw [map_smul, inner_smul_right]

/-- **Lemma 10.5 (first inequality), reduced to Cauchy reconstruction.** Given a linear
reconstruction map from compatible traces to the Neumann eigenspace which only kills traces
vanishing on `[0, L]`, the fixed space of `V_E` embeds injectively into the Neumann eigenspace:
`dim ker(V_E - I) ≤ dim ker(A_N - E)`. -/
theorem fixedSpace_to_neumannEigenspace_of_reconstruction {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W)
    (hR : ∃ R : compatibleTraces γ E →ₗ[ℂ] neumannEigenspace Ω E,
      ∀ h, R h = 0 → ∀ θ ∈ Icc 0 (2 * π), (h : ℝ → ℂ) θ = 0) :
    ∃ T : LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) →ₗ[ℂ]
      neumannEigenspace Ω E, Function.Injective T := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨R, hR⟩ := hR
  refine ⟨R ∘ₗ observationFixed hK hclosed hW, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h0 := hR _ hv
  have : (v : Ell2) = 0 := observation_injective_of_boundaryParam hγ hE hW v
    ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun θ hθ => h0 θ hθ))
  exact Subtype.ext this

/-- **Lemma 4.17 (range of the Herglotz data).** For a closed Lipschitz curve with boundary origin
`γ(0) = 0`, the vectors `O_E^* g_a`, `a` ranging over the `L²` direction densities, are exactly
the range of `I - V_E` (the domain of the Cayley transform `K_E`). -/
theorem range_observationAdj_herglotzConormal {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) (h0 : γ 0 = 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) :
    {x | ∃ (a : ℝ → ℂ) (_ : IsDirDensity a),
        x = observationAdj W (herglotzConormal (Real.sqrt E) a γ)} =
      Set.range ⇑((1 : Ell2 →L[ℂ] Ell2) - W (2 * π)) := by
  set V := W (2 * π)
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have hVV : V * ContinuousLinearMap.adjoint V = 1 := by
    have := (Unitary.mem_iff.mp hU).2
    rwa [ContinuousLinearMap.star_eq_adjoint] at this
  have hVV' : ContinuousLinearMap.adjoint V * V = 1 := by
    have := (Unitary.mem_iff.mp hU).1
    rwa [ContinuousLinearMap.star_eq_adjoint] at this
  -- `O_E^* g_a = (I - V) (√2 i V^* y_a(0))`
  have key : ∀ (a : ℝ → ℂ) (ha : IsDirDensity a),
      observationAdj W (herglotzConormal (Real.sqrt E) a γ) =
        (1 - V) (((Real.sqrt 2 : ℂ) * Complex.I) •
          ContinuousLinearMap.adjoint V (herglotzVec ha (Real.sqrt E) (γ 0))) := by
    intro a ha
    obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
    have hy : ContinuousOn (fun s => herglotzVec ha (Real.sqrt E) (γ s)) (Icc 0 (2 * π)) :=
      ((continuous_herglotzVec ha _).comp hK.continuous).continuousOn
    have hper : herglotzVec ha (Real.sqrt E) (γ (2 * π)) =
        herglotzVec ha (Real.sqrt E) (γ 0) := by rw [hclosed]
    obtain ⟨-, hadj⟩ := driven_endpoint hK hW hgm hgB hy
      (fun θ _ => herglotz_driven ha hK E θ) hper
    rw [hadj, map_smul]
    congr 1
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [← ContinuousLinearMap.mul_apply V, hVV, ContinuousLinearMap.one_apply]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, (key a ha).symm⟩
  · rintro ⟨w, rfl⟩
    have hc : ((Real.sqrt 2 : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    obtain ⟨a, ha, hav⟩ := exists_herglotzVec_zero_eq (Real.sqrt E)
      (((Real.sqrt 2 : ℂ) * Complex.I)⁻¹ • V w)
    refine ⟨a, ha, ?_⟩
    rw [key a ha, h0, hav, map_smul (ContinuousLinearMap.adjoint V), smul_smul,
      mul_inv_cancel₀ hc, one_smul,
      ← ContinuousLinearMap.mul_apply (ContinuousLinearMap.adjoint V), hVV',
      ContinuousLinearMap.one_apply]

/-- **Lemma 4.17 (Cayley factorization) for Herglotz waves.** For a closed Lipschitz curve with
`ker(I - V_E) = 0`, the vector `O_E^* g_a` lies in the domain of the Cayley transform `K_E` and
`2 h_a + i (T_E - T_E^*) g_a = -O_E K_E O_E^* g_a` on `[0, L]`, where `h_a = u_a ∘ γ` is the
Dirichlet trace of the Herglotz wave. (At a nonresonant energy `h_a = 𝒩(E) g_a`, so the left
side is `𝒜_E g_a`.) -/
theorem cayley_factorization_herglotz {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hinj : Function.Injective (1 - W (2 * π) : Ell2 →L[ℂ] Ell2)) {a : ℝ → ℂ}
    (ha : IsDirDensity a) :
    ∃ hx : observationAdj W (herglotzConormal (Real.sqrt E) a γ) ∈ cayleyDomain (W (2 * π)),
      ∀ θ ∈ Icc 0 (2 * π),
        2 * herglotzWave (Real.sqrt E) a (γ θ) +
            Complex.I * (volterraOp W (herglotzConormal (Real.sqrt E) a γ) θ -
              volterraOpAdj W (herglotzConormal (Real.sqrt E) a γ) θ) =
          -observation W (cayleyOp (W (2 * π)) hinj ⟨_, hx⟩) θ := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  have hy : ContinuousOn (fun s => herglotzVec ha (Real.sqrt E) (γ s)) (Icc 0 (2 * π)) :=
    ((continuous_herglotzVec ha _).comp hK.continuous).continuousOn
  have hper : herglotzVec ha (Real.sqrt E) (γ (2 * π)) =
      herglotzVec ha (Real.sqrt E) (γ 0) := by rw [hclosed]
  obtain ⟨hx, -, hfac⟩ := cayley_factorization hK hW hgm hgB hy
    (fun θ _ => herglotz_driven ha hK E θ) hper hinj
  refine ⟨hx, fun θ hθ => ?_⟩
  rw [← hfac θ hθ]
  congr 2
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [basisVec, inner_single, herglotzVec_apply, herglotzSeq, if_true, herglotzWave_eq]
  field_simp

end PolyaNeumann
