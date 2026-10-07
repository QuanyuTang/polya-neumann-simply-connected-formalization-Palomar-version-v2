module

public import RequestProject.Approximation

/-!
# Weighted masses (Lemma 10.11 for the mass form)

For uniformly bounded weights `ρ_n` on `Ω` converging almost everywhere to `1`, the weighted
masses `m_n[u,u] = ∫_Ω ρ_n |u|²` converge to `1` uniformly on the unit sphere of every
finite-dimensional subspace of `L²(Ω)` (`tendstoUniformlyOn_weightedMass`). This is the mass part of
Lemma 10.11 of the paper; the proof is the paper's: dominated convergence for the matrix entries
in a basis, then uniformity on bounded sets of a finite-dimensional space
(`tendstoUniformlyOn_sesq_of_basis`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ}

/-- The weighted mass `m[u,u] = ∫_Ω ρ |u|²`. -/
def weightedMass (Ω : Set ℂ) (ρ : ℂ → ℝ) (u : L2 Ω) : ℝ :=
  ∫ w in Ω, ρ w * ‖(u : ℂ → ℂ) w‖ ^ 2

/-- Integrability of `ρ ⟨u, v⟩` for a bounded weight `ρ`. -/
lemma integrable_weight_inner {ρ : ℂ → ℝ} {C : ℝ}
    (hρm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hρb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C) (u v : L2 Ω) :
    Integrable (fun w => (ρ w : ℂ) * inner ℂ ((u : ℂ → ℂ) w) ((v : ℂ → ℂ) w))
      (volume.restrict Ω) :=
  (L2.integrable_inner u v).bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hρm)
    (hρb.mono fun w hw => by simpa [Complex.norm_real] using hw)

/-- The weighted sesquilinear form `(u, v) ↦ ∫_Ω ρ ⟨u, v⟩` on a submodule of `L²(Ω)`. -/
def weightedSesq (S : Submodule ℂ (L2 Ω)) {ρ : ℂ → ℝ} {C : ℝ}
    (hρm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hρb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C) : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun u v => ∫ w in Ω, (ρ w : ℂ) *
      inner ℂ (((u : L2 Ω) : ℂ → ℂ) w) (((v : L2 Ω) : ℂ → ℂ) w))
    (fun u₁ u₂ v => by
      rw [← integral_add (integrable_weight_inner hρm hρb _ _)
        (integrable_weight_inner hρm hρb _ _)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add (u₁ : L2 Ω) (u₂ : L2 Ω)] with w hw
      rw [Submodule.coe_add, hw, Pi.add_apply, inner_add_left, mul_add])
    (fun c u v => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c (u : L2 Ω)] with w hw
      rw [Submodule.coe_smul, hw, Pi.smul_apply, inner_smul_left]
      simp only [starRingEnd_apply]
      ring)
    (fun u v₁ v₂ => by
      rw [← integral_add (integrable_weight_inner hρm hρb _ _)
        (integrable_weight_inner hρm hρb _ _)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add (v₁ : L2 Ω) (v₂ : L2 Ω)] with w hw
      rw [Submodule.coe_add, hw, Pi.add_apply, inner_add_right, mul_add])
    (fun c u v => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c (v : L2 Ω)] with w hw
      rw [Submodule.coe_smul, hw, Pi.smul_apply, inner_smul_right, RingHom.id_apply]
      ring)

lemma weightedSesq_apply (S : Submodule ℂ (L2 Ω)) {ρ : ℂ → ℝ} {C : ℝ}
    (hρm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hρb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C) (u v : S) :
    weightedSesq S hρm hρb u v = ∫ w in Ω, (ρ w : ℂ) *
      inner ℂ (((u : L2 Ω) : ℂ → ℂ) w) (((v : L2 Ω) : ℂ → ℂ) w) := rfl

lemma weightedSesq_self (S : Submodule ℂ (L2 Ω)) {ρ : ℂ → ℝ} {C : ℝ}
    (hρm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hρb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C) (u : S) :
    weightedSesq S hρm hρb u u = (weightedMass Ω ρ u : ℂ) := by
  rw [weightedSesq_apply, weightedMass, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [inner_self_eq_norm_sq_to_K]
  rw [Complex.ofReal_mul, Complex.ofReal_pow]
  rfl

/-- Mass part of Lemma 10.11: for weights `ρ_n` on `Ω`, uniformly bounded and converging to `1`
almost everywhere, `∫_Ω ρ_n |u|² → 1` uniformly on the unit sphere of every finite-dimensional
subspace of `L²(Ω)`. -/
theorem tendstoUniformlyOn_weightedMass (ρ : ℕ → ℂ → ℝ) (C : ℝ)
    (hρm : ∀ n, AEStronglyMeasurable (ρ n) (volume.restrict Ω))
    (hρb : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |ρ n w| ≤ C)
    (hρt : ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => ρ n w) atTop (𝓝 1))
    (S : Submodule ℂ (L2 Ω)) (hS : FiniteDimensional ℂ S) :
    TendstoUniformlyOn (fun n u => weightedMass Ω (ρ n) u) (fun _ => 1) atTop
      ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1) := by
  set b := Module.finBasis ℂ S
  set Bn : ℕ → S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ := fun n => weightedSesq S (hρm n) (hρb n)
  set B : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ := innerₛₗ ℂ
  have hentries : ∀ r s, Tendsto (fun n => Bn n (b r) (b s)) atTop (𝓝 (B (b r) (b s))) := by
    intro r s
    have hB : B (b r) (b s) = ∫ w in Ω, inner ℂ (((b r : S) : L2 Ω) w) (((b s : S) : L2 Ω) w) := by
      simp only [B, innerₛₗ_apply_apply, Submodule.coe_inner, L2.inner_def]
    rw [hB]
    refine tendsto_integral_of_dominated_convergence
      (fun w => C * ‖inner ℂ (((b r : S) : L2 Ω) w) (((b s : S) : L2 Ω) w)‖)
      (fun n => (integrable_weight_inner (hρm n) (hρb n) _ _).aestronglyMeasurable)
      ((L2.integrable_inner _ _).norm.const_mul C) (fun n => ?_) ?_
    · filter_upwards [hρb n] with w hw
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    · filter_upwards [hρt] with w hw
      have := ((Complex.continuous_ofReal.tendsto 1).comp hw).mul_const
        (inner ℂ (((b r : S) : L2 Ω) w) (((b s : S) : L2 Ω) w))
      simpa using this
  have hK : Bornology.IsBounded {u : S | ‖u‖ = 1} :=
    (Metric.isBounded_closedBall (x := (0 : S)) (r := 1)).subset fun u hu => by
      simp only [Set.mem_setOf_eq] at hu
      simp [hu]
  have hU := tendstoUniformlyOn_sesq_of_basis b Bn B hentries hK
  have hU' := Complex.uniformContinuous_re.comp_tendstoUniformlyOn hU
  intro t ht
  filter_upwards [hU' t ht] with n hn
  rintro u ⟨huS, hu1⟩
  have h1 := hn ⟨u, huS⟩ (by simpa using hu1)
  simp only [Function.comp_apply, Bn, weightedSesq_self, Complex.ofReal_re, B,
    innerₛₗ_apply_apply, inner_self_eq_norm_sq_to_K] at h1
  have hnorm : ‖(⟨u, huS⟩ : S)‖ = 1 := by simpa using hu1
  rw [hnorm] at h1
  simpa using h1

end PolyaNeumann

end
