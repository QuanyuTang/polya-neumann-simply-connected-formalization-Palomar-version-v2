module

public import RequestProject.Driven
public import RequestProject.Cayley

/-!
# Factorization through the Cayley transform (Lemma 4.17)

Let `y` be a periodic solution of the driven transport equation `y' = C_E y - (i/√2) g e₀`
(as in Lemma 4.10), `v = y(0)`, and assume `ker (I - V_E) = 0`.  Then
* `O_E^* g` lies in the domain `ran (I - V_E)` of the Cayley transform `K_E`, and
  `K_E O_E^* g = -√2 (I + V_E^*) v`;
* with `h = √2 ⟨e₀, y⟩` the boundary trace, `2 h + i (T_E - T_E^*) g = -O_E K_E O_E^* g`
  on `[0, L]`.

At a Neumann-nonresonant energy the paper identifies `h_a = N(E) g_a` for Herglotz data, so the
second identity is the factorization `A_E g_a = -O_E K_E O_E^* g_a` of Lemma 4.17, with
`A_E = 2 N(E) + i (T_E - T_E^*)`.  The identification `N(E) g_a = h_a` (which needs the
Helmholtz boundary value problem) is not formalized; it is replaced by the trace `h` itself.
-/

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- **Lemma 4.17 (factorization through the Cayley transform).** -/
theorem cayley_factorization {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in (0 : ℝ)..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0))
    (hper : y (2 * π) = y 0)
    (hinj : Function.Injective (1 - W (2 * π) : Ell2 →L[ℂ] Ell2)) :
    ∃ hx : observationAdj W g ∈ cayleyDomain (W (2 * π)),
      cayleyOp (W (2 * π)) hinj ⟨_, hx⟩ =
          (-(Real.sqrt 2 : ℂ)) • (y 0 + ContinuousLinearMap.adjoint (W (2 * π)) (y 0)) ∧
        ∀ θ ∈ Icc 0 (2 * π),
          2 * ((Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0) (y θ)) +
              Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) =
            -observation W (cayleyOp (W (2 * π)) hinj ⟨_, hx⟩) θ := by
  have hL : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  set V := W (2 * π) with hVdef
  set v := y 0 with hvdef
  set c : ℂ := (Real.sqrt 2 : ℂ) * Complex.I with hcdef
  have hVV : V (ContinuousLinearMap.adjoint V v) = v := by
    rw [← ContinuousLinearMap.mul_apply, transport_mul_adjoint hK hW hL,
      ContinuousLinearMap.one_apply]
  have hO : observationAdj W g = c • (ContinuousLinearMap.adjoint V - 1) v :=
    (driven_endpoint hK hW hg hgB hy ey hper).2
  have hrep : observationAdj W g =
      (1 - V : Ell2 →L[ℂ] Ell2) (c • ContinuousLinearMap.adjoint V v) := by
    rw [hO, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply, hVV]
  have hx : observationAdj W g ∈ cayleyDomain V := hrep ▸ mem_cayleyDomain _
  have hK' : cayleyOp V hinj (⟨_, hx⟩ : cayleyDomain V) =
      (-(Real.sqrt 2 : ℂ)) • (v + ContinuousLinearMap.adjoint V v) := by
    have h2 : Complex.I * c = -(Real.sqrt 2 : ℂ) := by
      rw [hcdef, mul_left_comm, Complex.I_mul_I, mul_neg_one]
    rw [cayleyOp_apply' hinj _ _ hrep, map_smul, hVV, ← smul_add, smul_smul, h2, add_comm]
  refine ⟨hx, hK', fun θ hθ => ?_⟩
  have htr := driven_trace hK hW hg hgB hy ey θ hθ
  have hadd := volterraOp_add_adj hW.1 hg hgB hθ
  erw [hK']
  rw [hO] at hadd
  simp only [observation, map_smul, map_add, map_sub, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_smul_right, inner_add_right, inner_sub_right] at htr hadd ⊢
  linear_combination 2 * htr - Complex.I * hadd +
    ((Real.sqrt 2 : ℂ) * (inner ℂ (basisVec 0) ((W θ) (y 0)) -
      inner ℂ (basisVec 0) ((W θ) ((ContinuousLinearMap.adjoint V) v)))) * Complex.I_sq

end PolyaNeumann

end
