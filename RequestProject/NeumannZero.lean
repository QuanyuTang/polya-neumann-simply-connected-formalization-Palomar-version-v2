module

public import RequestProject.NeumannEigenspace
public import RequestProject.WeakConstancy

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The zero weak Neumann eigenspace consists exactly of the constants. -/
theorem mem_neumannEigenspace_zero_iff {Ω : Set ℂ} (hΩ : IsDomain Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (u : L2 Ω) :
    u ∈ neumannEigenspace Ω 0 ↔ ∃ c : ℂ, u = Lp.const 2 (volume.restrict Ω) c := by
  constructor
  · rintro ⟨g, hg, hweak⟩
    have h := hweak u g hg
    simp only [inner_self_eq_norm_sq_to_K, Fin.sum_univ_two, Complex.ofReal_zero,
      zero_mul] at h
    have hnorm : ‖g 0‖ ^ 2 + ‖g 1‖ ^ 2 = 0 :=
      Complex.ofReal_injective (by push_cast; exact h)
    have hg0 : g = 0 := by
      have hzero0 : g 0 = 0 := norm_eq_zero.mp (by
        nlinarith [sq_nonneg ‖g 1‖, norm_nonneg (g 0)])
      have hzero1 : g 1 = 0 := norm_eq_zero.mp (by
        nlinarith [sq_nonneg ‖g 0‖, norm_nonneg (g 1)])
      funext i
      fin_cases i <;> simp [hzero0, hzero1]
    obtain ⟨c, hc⟩ := ae_const_of_weakGradient_zero hΩ u (by simpa [hg0] using hg)
    refine ⟨c, Lp.ext ?_⟩
    filter_upwards [hc, Lp.coeFn_const 2 (volume.restrict Ω) c] with w hw hconst
    exact hw.trans hconst.symm
  · rintro ⟨c, rfl⟩
    refine ⟨0, isWeakGradient_const Ω c, fun v h hv => ?_⟩
    simp

theorem lpConst_eq_smul_one (Ω : Set ℂ) [IsFiniteMeasure (volume.restrict Ω)] (c : ℂ) :
    Lp.const 2 (volume.restrict Ω) c = c • Lp.const 2 (volume.restrict Ω) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (Lp.const 2 (volume.restrict Ω) (1 : ℂ)),
    Lp.coeFn_const 2 (volume.restrict Ω) (1 : ℂ),
    Lp.coeFn_const 2 (volume.restrict Ω) c] with w h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3]
  simp

/-- Connectedness identifies the entire zero eigenspace, not merely one zero eigenvector. -/
theorem neumannEigenspace_zero_eq_span {Ω : Set ℂ} (hΩ : IsDomain Ω)
    [IsFiniteMeasure (volume.restrict Ω)] :
    neumannEigenspace Ω 0 = ℂ ∙ Lp.const 2 (volume.restrict Ω) (1 : ℂ) := by
  ext u
  rw [mem_neumannEigenspace_zero_iff hΩ, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (lpConst_eq_smul_one Ω c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, (lpConst_eq_smul_one Ω c).symm⟩

/-- The zero eigenvalue has complex multiplicity one on a bounded connected domain. -/
theorem neumannEigenspace_zero_finrank {Ω : Set ℂ} (hΩ : IsDomain Ω)
    (hb : Bornology.IsBounded Ω) : Module.finrank ℂ (neumannEigenspace Ω 0) = 1 := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  rw [neumannEigenspace_zero_eq_span hΩ]
  apply finrank_span_singleton
  have hpos : 0 < volume Ω := hΩ.1.measure_pos volume hΩ.2.1
  intro h
  have h1 : ‖Lp.const 2 (volume.restrict Ω) (1 : ℂ)‖ = 0 := by rw [h]; simp
  haveI : NeZero (volume.restrict Ω) := ⟨by
    intro h0
    rw [Measure.restrict_eq_zero] at h0
    exact hpos.ne' h0⟩
  rw [Lp.norm_const 2 (volume.restrict Ω) (1 : ℂ) (by norm_num)] at h1
  simp only [norm_one, one_mul] at h1
  have hvol : (volume.restrict Ω).real Set.univ ≠ 0 := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hb.measure_lt_top.ne⟩
  apply hvol
  rwa [Real.rpow_eq_zero (by positivity) (by norm_num)] at h1

end PolyaNeumann

end
