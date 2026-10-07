module

public import RequestProject.HerglotzSchurPos
public import RequestProject.HerglotzAdmissible

/-!
# Lemma 8.6 (negative index at small energy)

Combining the Schur complement reduction (`SmallEnergyForm.lean`), Lemma 8.2
(`small_energy_imForm_basisVec_neg`), Lemma 8.5 on Herglotz data (`herglotz_imSchur_nonneg`) and
the construction of admissible Herglotz data (`exists_admissible_herglotzVec`), we prove the
analytic core `small_energy_schur_core` and hence Lemma 8.6 (`small_energy_herglotz_bound'`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section
namespace PolyaNeumann

/-- **Analytic core of Lemma 8.6** (Lemmas 8.3–8.5): for small `E > 0`, every finitely supported
vector can be moved along `e₀` to a vector on which the Schur complement is nonnegative. -/
theorem small_energy_schur_core {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ v : Ell2, (∃ N : ℕ, ∀ n, N ≤ n → (v : ℕ → ℂ) n = 0) →
        ∃ t : ℂ, 0 ≤ imSchur (monodromy W) (basisVec 0) (v + t • basisVec 0) := by
  obtain ⟨z₁, hz₁⟩ := hL.1.2.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hL.1.1 z₁ hz₁
  have hΩ : 0 < (volume Ω).toReal := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  obtain ⟨δ₅, hδ₅, h₅⟩ := herglotz_imSchur_nonneg hb hL hγ hr hball
  obtain ⟨δa, hδa, hadm⟩ := exists_admissible_herglotzVec hb hΩ (γ 0) z₁
  refine ⟨min δ₅ (δa ^ 2), lt_min hδ₅ (by positivity), fun E hE hEδ W hW v _ => ?_⟩
  have hk : |Real.sqrt E| < δa := by
    rw [abs_of_nonneg (Real.sqrt_nonneg E), show δa = Real.sqrt (δa ^ 2) from
      (Real.sqrt_sq hδa.le).symm]
    exact Real.sqrt_lt_sqrt hE.le (hEδ.trans_le (min_le_right _ _))
  obtain ⟨t, a, ha, hvec, hneg, hmean⟩ := hadm (Real.sqrt E) hk v
  refine ⟨t, ?_⟩
  rw [← hvec]
  exact h₅ E hE (hEδ.trans_le (min_le_left _ _)) W hW a ha hneg hmean

/-- **Lemma 8.6 on `ℓ²`.** For small `E > 0`, `-Im ⟨v, U_E v⟩ ≥ 0` on the closed hyperplane
`{B(e₀, ·) = 0}`. -/
theorem small_energy_imForm_nonneg {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ v : Ell2, imPair (monodromy W) (basisVec 0) v = 0 → 0 ≤ imForm (monodromy W) v := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := small_energy_imForm_basisVec_neg hb hL hγ
  obtain ⟨δ₂, hδ₂, h₂⟩ := small_energy_schur_core hb hL hγ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun E hE hEδ W hW v hv => ?_⟩
  have hneg := h₁ E hE (hEδ.trans_le (min_le_left _ _)) W hW
  have hS := h₂ E hE (hEδ.trans_le (min_le_right _ _)) W hW
  refine nonneg_of_imSchur_nonneg (monodromy W) dense_finSupp (fun w hw => ?_) v hv
  obtain ⟨t, ht⟩ := hS w hw
  rwa [imSchur_add_smul _ hneg.ne] at ht

/-- **Lemma 8.6 on Herglotz data.** -/
theorem small_energy_herglotz_bound' {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin 1 → ℂ), ∀ a, IsDirDensity a → L a = 0 →
        0 ≤ herglotzForm W γ E a := by
  obtain ⟨δ, hδ, h⟩ := small_energy_imForm_nonneg hb hL hγ
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  refine ⟨δ, hδ, fun E hE hEδ W hW => ?_⟩
  set U := monodromy W
  set ℓ : Ell2 →ₗ[ℂ] ℂ :=
    { toFun := fun v => imPair U (basisVec 0) v
      map_add' := fun v w => imPair_add_right U _ v w
      map_smul' := fun c v => imPair_smul_right U _ v c }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (ℓ.comp (herglotzVecLin (Real.sqrt E) (γ 0)))
  refine ⟨(LinearMap.pi fun _ => g), fun a ha hLa => ?_⟩
  have hga : g a = imPair U (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) := by
    have := congrArg (fun F => F ⟨a, ha⟩) hg
    simpa [ℓ, herglotzVecLin] using this
  have h0 : g a = 0 := by
    have := congrFun hLa 0
    simpa using this
  rw [herglotzForm_eq_im hK hclosed hW ha]
  have := h E hE hEδ W hW (herglotzVec ha (Real.sqrt E) (γ 0)) (by rw [← hga, h0])
  unfold imForm at this
  exact this

end PolyaNeumann

end
