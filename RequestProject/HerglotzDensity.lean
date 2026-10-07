module

public import RequestProject.HerglotzSchurPos

/-!
# Herglotz data with vanishing negative modes at an interior point

Fix points `z₀, z₁`. For `v ∈ ℓ²(ℕ₀)` we synthesize an `L²` density `a_v` (`synthDens`) whose
Herglotz coefficients at `z₁` are `F_n(z₁) = v_n` (`n ≥ 1`), `F₀(z₁) = √2 v₀`, `F_{-j}(z₁) = 0`
(`j ≥ 1`), so that `y_{a_v}(z₁) = v`. The map `T v = y_{a_v}(z₀)` is linear with
`‖T − I‖ ≤ √2 |k| |z₀ − z₁|` (`norm_one_sub_synthOp_le`), hence onto for small `k`. Adjusting along
`e₀` we obtain, for small `k`, for every `w` a density with vanishing negative modes at `z₁`,
zero mean of `u_a` over a bounded `Ω`, and `y_a(z₀) = w + t e₀` (`exists_admissible_herglotzVec`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section
namespace PolyaNeumann

local instance factTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

lemma herglotzCoeff_congr_ae {a b : ℝ → ℂ} (h : a =ᵐ[volume.restrict (Ioc 0 (2 * π))] b)
    (k : ℝ) (m : ℤ) (z : ℂ) : herglotzCoeff k a m z = herglotzCoeff k b m z := by
  unfold herglotzCoeff
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity)]
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h
  filter_upwards [h] with φ hφ hmem
  rw [hφ hmem]

lemma herglotzVec_congr_ae {a b : ℝ → ℂ} (ha : IsDirDensity a) (hb : IsDirDensity b)
    (h : a =ᵐ[volume.restrict (Ioc 0 (2 * π))] b) (k : ℝ) (z : ℂ) :
    herglotzVec ha k z = herglotzVec hb k z := by
  refine lp.ext (funext fun n => ?_)
  rw [herglotzVec_apply, herglotzVec_apply]
  unfold herglotzSeq
  simp only [herglotzCoeff_congr_ae h]

/-- Pull back an a.e. statement on the circle to the parameter interval. -/
lemma ae_restrict_Ioc_of_ae_haar {p : AddCircle (2 * π) → Prop}
    (h : ∀ᵐ x ∂(@AddCircle.haarAddCircle (2 * π) _), p x) :
    ∀ᵐ φ : ℝ ∂(volume.restrict (Ioc 0 (2 * π))), p φ := by
  have hv : ∀ᵐ x ∂(volume : Measure (AddCircle (2 * π))), p x := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h _
  have := (AddCircle.measurePreserving_mk (2 * π) 0).quasiMeasurePreserving.ae hv
  simpa using this

section Synth

/-- The Fourier coefficients of the synthesized density: `c₀ = √2 v₀`, `c_n = v_n` (`n ≥ 1`),
`c_n = 0` (`n < 0`). -/
def synthCoeff (v : Ell2) (m : ℤ) : ℂ :=
  if m = 0 then (Real.sqrt 2 : ℂ) * (v : ℕ → ℂ) 0 else if 0 < m then (v : ℕ → ℂ) m.toNat else 0

lemma synthCoeff_add (v w : Ell2) (m : ℤ) :
    synthCoeff (v + w) m = synthCoeff v m + synthCoeff w m := by
  unfold synthCoeff; split_ifs <;> simp [mul_add]

lemma synthCoeff_smul (c : ℂ) (v : Ell2) (m : ℤ) :
    synthCoeff (c • v) m = c * synthCoeff v m := by
  unfold synthCoeff; split_ifs <;> simp; ring

lemma hasSum_sq_synthCoeff (v : Ell2) :
    HasSum (fun m => ‖synthCoeff v m‖ ^ 2) (‖v‖ ^ 2 + ‖(v : ℕ → ℂ) 0‖ ^ 2) := by
  have hv : HasSum (fun n : ℕ => ‖(v : ℕ → ℂ) n‖ ^ 2) (‖v‖ ^ 2) := by
    have := lp.hasSum_norm (p := 2) (by norm_num) v
    simpa [two_toReal] using this
  have hpos : HasSum (fun n : ℕ => ‖synthCoeff v n‖ ^ 2) (‖v‖ ^ 2 + ‖(v : ℕ → ℂ) 0‖ ^ 2) := by
    have h2 := hv.add (hasSum_ite_eq 0 (‖(v : ℕ → ℂ) 0‖ ^ 2))
    refine h2.congr_fun fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hr : ‖(Real.sqrt 2 : ℂ)‖ ^ 2 = 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
      simp [synthCoeff, mul_pow]
      ring
    · have h1 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
      have h2 : (0 : ℤ) < n := by exact_mod_cast hn
      rw [synthCoeff, if_neg h1, if_pos h2, Int.toNat_natCast, if_neg hn.ne', add_zero]
  have hneg : HasSum (fun n : ℕ => ‖synthCoeff v (-((n : ℤ) + 1))‖ ^ 2) 0 := by
    have : ∀ n : ℕ, ‖synthCoeff v (-((n : ℤ) + 1))‖ ^ 2 = 0 := fun n => by
      have h1 : -((n : ℤ) + 1) ≠ 0 := by omega
      have h2 : ¬ (0 : ℤ) < -((n : ℤ) + 1) := by omega
      rw [synthCoeff, if_neg h1, if_neg h2, norm_zero]; norm_num
    simp only [this]; exact hasSum_zero
  have := HasSum.of_nat_of_neg_add_one (f := fun m => ‖synthCoeff v m‖ ^ 2) hpos hneg
  rwa [add_zero] at this

lemma memℓp_synthCoeff (v : Ell2) : Memℓp (synthCoeff v) 2 := by
  rw [memℓp_gen_iff (by simp)]
  simpa [two_toReal] using (hasSum_sq_synthCoeff v).summable

/-- The synthesized `L²` function on the circle. -/
def synthL2 (v : Ell2) : Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _) :=
  fourierBasis.repr.symm ⟨synthCoeff v, memℓp_synthCoeff v⟩

lemma synthL2_add (v w : Ell2) : synthL2 (v + w) = synthL2 v + synthL2 w := by
  unfold synthL2
  rw [← map_add]
  congr 1
  exact lp.ext (funext fun m => synthCoeff_add v w m)

lemma synthL2_smul (c : ℂ) (v : Ell2) : synthL2 (c • v) = c • synthL2 v := by
  unfold synthL2
  rw [← map_smul]
  congr 1
  exact lp.ext (funext fun m => synthCoeff_smul c v m)

lemma fourierCoeff_synthL2 (v : Ell2) (m : ℤ) : fourierCoeff (synthL2 v) m = synthCoeff v m := by
  rw [← fourierBasis_repr, synthL2, LinearIsometryEquiv.apply_symm_apply]

/-- The synthesized density, shifted to the base point `z₁`. -/
def synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) (φ : ℝ) : ℂ :=
  (synthL2 v : AddCircle (2 * π) → ℂ) φ * planeWave k (-z₁) φ

lemma isDirDensity_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) : IsDirDensity (synthDens k z₁ v) := by
  have hfm : MemLp (synthL2 v : AddCircle (2 * π) → ℂ) 2 :=
    memLp_haarAddCircle_iff.mp (Lp.memLp _)
  have ha₀ : IsDirDensity fun φ : ℝ => (synthL2 v : AddCircle (2 * π) → ℂ) φ := by
    have := hfm.comp_measurePreserving (AddCircle.measurePreserving_mk (2 * π) 0)
    rw [zero_add] at this
    exact this
  exact ha₀.of_le ((MemLp.aestronglyMeasurable ha₀).mul (continuous_planeWave k (-z₁)).aestronglyMeasurable)
    (Eventually.of_forall fun φ => by rw [synthDens, norm_mul, norm_planeWave, mul_one])

lemma herglotzCoeff_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) (m : ℤ) :
    herglotzCoeff k (synthDens k z₁ v) m z₁ = synthCoeff v m := by
  unfold synthDens
  rw [herglotzCoeff_shift, herglotzCoeff_zero_eq_fourierCoeff, fourierCoeff_synthL2]

lemma herglotzCoeff_synthDens_neg (k : ℝ) (z₁ : ℂ) (v : Ell2) (j : ℕ) (hj : 1 ≤ j) :
    herglotzCoeff k (synthDens k z₁ v) (-(j : ℤ)) z₁ = 0 := by
  rw [herglotzCoeff_synthDens, synthCoeff, if_neg (by omega), if_neg (by omega)]

lemma herglotzVec_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) :
    herglotzVec (isDirDensity_synthDens k z₁ v) k z₁ = v := by
  refine lp.ext (funext fun n => ?_)
  rw [herglotzVec_apply]
  unfold herglotzSeq
  split_ifs with hn
  · subst hn
    rw [herglotzCoeff_synthDens, synthCoeff, if_pos rfl]
    have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    field_simp
  · rw [herglotzCoeff_synthDens, synthCoeff, if_neg (by exact_mod_cast hn),
      if_pos (by omega), Int.toNat_natCast]

lemma norm_sq_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) :
    (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖synthDens k z₁ v φ‖ ^ 2 =
      ‖v‖ ^ 2 + ‖(v : ℕ → ℂ) 0‖ ^ 2 := by
  have h1 := hasSum_sq_herglotzCoeff (isDirDensity_synthDens k z₁ v) k z₁
  simp only [herglotzCoeff_synthDens] at h1
  exact h1.unique (hasSum_sq_synthCoeff v)

lemma synthDens_add_ae (k : ℝ) (z₁ : ℂ) (v w : Ell2) :
    synthDens k z₁ (v + w) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      synthDens k z₁ v + synthDens k z₁ w := by
  have h := Lp.coeFn_add (synthL2 v) (synthL2 w)
  rw [← synthL2_add] at h
  filter_upwards [ae_restrict_Ioc_of_ae_haar h] with φ hφ
  simp only [synthDens, Pi.add_apply, hφ, add_mul]

lemma synthDens_smul_ae (k : ℝ) (z₁ : ℂ) (c : ℂ) (v : Ell2) :
    synthDens k z₁ (c • v) =ᵐ[volume.restrict (Ioc 0 (2 * π))] c • synthDens k z₁ v := by
  have h := Lp.coeFn_smul c (synthL2 v)
  rw [← synthL2_smul] at h
  filter_upwards [ae_restrict_Ioc_of_ae_haar h] with φ hφ
  simp only [synthDens, Pi.smul_apply, hφ, smul_eq_mul, mul_assoc]

lemma herglotzVec_synthDens_add (k : ℝ) (z₁ : ℂ) (v w : Ell2) (z : ℂ) :
    herglotzVec (isDirDensity_synthDens k z₁ (v + w)) k z =
      herglotzVec (isDirDensity_synthDens k z₁ v) k z +
        herglotzVec (isDirDensity_synthDens k z₁ w) k z := by
  rw [herglotzVec_congr_ae _ ((isDirDensity_synthDens k z₁ v).add (isDirDensity_synthDens k z₁ w))
    (synthDens_add_ae k z₁ v w), herglotzVec_add]

lemma herglotzVec_synthDens_smul (k : ℝ) (z₁ : ℂ) (c : ℂ) (v : Ell2) (z : ℂ) :
    herglotzVec (isDirDensity_synthDens k z₁ (c • v)) k z =
      c • herglotzVec (isDirDensity_synthDens k z₁ v) k z := by
  rw [herglotzVec_congr_ae _ ((isDirDensity_synthDens k z₁ v).const_smul c)
    (synthDens_smul_ae k z₁ c v), herglotzVec_smul]

end Synth
section Op

/-- `v ↦ y_{a_v}(z₀)`, where `a_v` is the synthesized density based at `z₁`. -/
def synthOpLin (k : ℝ) (z₁ z₀ : ℂ) : Ell2 →ₗ[ℂ] Ell2 where
  toFun v := herglotzVec (isDirDensity_synthDens k z₁ v) k z₀
  map_add' v w := herglotzVec_synthDens_add k z₁ v w z₀
  map_smul' c v := herglotzVec_synthDens_smul k z₁ c v z₀

lemma norm_synthDens_sq_le (k : ℝ) (z₁ : ℂ) (v : Ell2) :
    (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖synthDens k z₁ v φ‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  rw [norm_sq_synthDens]
  have := lp.norm_apply_le_norm (p := 2) (by norm_num) v 0
  nlinarith [norm_nonneg ((v : ℕ → ℂ) 0)]

lemma norm_herglotzVec_synthDens_sub_le (k : ℝ) (z₁ z : ℂ) (v : Ell2) :
    ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z - v‖ ≤
      |k| * Real.sqrt 2 * ‖v‖ * ‖z - z₁‖ := by
  have h := norm_herglotzVec_sub_le (isDirDensity_synthDens k z₁ v) k z z₁
  rw [herglotzVec_synthDens] at h
  refine h.trans ?_
  have hs : Real.sqrt ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖synthDens k z₁ v φ‖ ^ 2) ≤
      Real.sqrt 2 * ‖v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (norm_synthDens_sq_le k z₁ v)
  have := mul_le_mul_of_nonneg_left hs (abs_nonneg k)
  have := mul_le_mul_of_nonneg_right this (norm_nonneg (z - z₁))
  linarith [show |k| * (Real.sqrt 2 * ‖v‖) * ‖z - z₁‖ = |k| * Real.sqrt 2 * ‖v‖ * ‖z - z₁‖ by ring]

/-- The synthesis operator as a bounded operator. -/
def synthOp (k : ℝ) (z₁ z₀ : ℂ) : Ell2 →L[ℂ] Ell2 :=
  (synthOpLin k z₁ z₀).mkContinuous (1 + |k| * Real.sqrt 2 * ‖z₀ - z₁‖) fun v => by
    have h := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v
    have := norm_le_insert' (herglotzVec (isDirDensity_synthDens k z₁ v) k z₀) v
    show ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z₀‖ ≤ _
    nlinarith [norm_nonneg v]

lemma synthOp_apply (k : ℝ) (z₁ z₀ : ℂ) (v : Ell2) :
    synthOp k z₁ z₀ v = herglotzVec (isDirDensity_synthDens k z₁ v) k z₀ := rfl

lemma norm_one_sub_synthOp_le (k : ℝ) (z₁ z₀ : ℂ) :
    ‖1 - synthOp k z₁ z₀‖ ≤ |k| * Real.sqrt 2 * ‖z₀ - z₁‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, synthOp_apply, norm_sub_rev]
  have := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v
  linarith [show |k| * Real.sqrt 2 * ‖v‖ * ‖z₀ - z₁‖ = |k| * Real.sqrt 2 * ‖z₀ - z₁‖ * ‖v‖ by ring]

lemma synthOp_surjective {k : ℝ} {z₁ z₀ : ℂ} (h : |k| * Real.sqrt 2 * ‖z₀ - z₁‖ < 1) :
    Function.Surjective (synthOp k z₁ z₀) := by
  have hu : IsUnit (synthOp k z₁ z₀) := by
    have := isUnit_one_sub_of_norm_lt_one ((norm_one_sub_synthOp_le k z₁ z₀).trans_lt h)
    simpa using this
  obtain ⟨S, hS⟩ := hu.exists_right_inv
  intro w
  refine ⟨S w, ?_⟩
  have := congrArg (fun T : Ell2 →L[ℂ] Ell2 => T w) hS
  simpa using this

end Op
end PolyaNeumann
