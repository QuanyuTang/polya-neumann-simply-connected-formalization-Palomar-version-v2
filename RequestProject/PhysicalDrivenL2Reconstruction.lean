module

public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.PhysicalDrivenReconstruction

/-!
# Actual driven reconstruction for integrable and L² forcing

The positive finite gauge has a true pointwise derivative despite merely
integrable forcing. Finite FTC and the generic continuous-vector series
limits give the actual primitive recurrence. The proved factorial inverse
then reconstructs the true zeroth physical row at the original real energy.
No primitive, interior reconstruction or exceptional-row derivative is
assumed in the input hypotheses.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

private theorem physicalDrivenGaugePartial_primitive_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (j N : ℕ) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGaugePartial γ E (physicalDrivenVector W g) (j + 1) N θ =
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ,
        conj (deriv γ s) * physicalDrivenGaugePartial γ E (physicalDrivenVector W g) j N s) +
      ∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) (j + 2) N s := by
  let y := physicalDrivenVector W g
  let p := physicalDrivenGaugePartial γ E y (j + 1) N
  let a : ℝ → ℂ := fun s => conj (deriv γ s) * physicalDrivenGaugePartial γ E y j N s
  let t : ℝ → ℂ := fun s => deriv γ s * physicalDrivenGaugeTerm γ E y (j + 2) N s
  have hy : ContinuousOn y (Icc 0 (2 * Real.pi)) :=
    physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hp : ContinuousOn p (Icc 0 (2 * Real.pi)) :=
    physicalDrivenGaugePartial_continuousOn γ hγ.continuous E y hy (j + 1) N
  have ha : ContinuousOn a (Icc 0 (2 * Real.pi)) :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenGaugePartial_continuousOn γ hγ.continuous E y hy j N)
  have ht : ContinuousOn t (Icc 0 (2 * Real.pi)) :=
    hγ.continuous_deriv_one.continuousOn.mul
      (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E y hy (j + 2) N)
  have hsub : Icc 0 θ ⊆ Icc 0 (2 * Real.pi) := Icc_subset_Icc le_rfl hθ.2
  have hd (s : ℝ) (hs : s ∈ Ioo 0 θ) :
      HasDerivAt p (physicalDrivenQ E ^ 2 * a s + t s) s := by
    have hs' : s ∈ Ioo 0 (2 * Real.pi) := ⟨hs.1, hs.2.trans_le hθ.2⟩
    simpa only [p, a, t, physicalDrivenGaugeTerm, Nat.add_assoc, mul_assoc] using
      physicalDrivenGaugePartial_hasDerivAt_of_intervalIntegrable hK hγ hW g hg hs' j N
  have hia : IntervalIntegrable a volume 0 θ :=
    ((ha.mono hsub).mono (by rw [uIcc_of_le hθ.1])).intervalIntegrable
  have hit : IntervalIntegrable t volume 0 θ :=
    ((ht.mono hsub).mono (by rw [uIcc_of_le hθ.1])).intervalIntegrable
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1
    (hp.mono hsub) hd ((hia.const_mul _).add hit)
  have hp0 : p 0 = 0 := physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y _ _
    (physicalDrivenVector_zero W g)
  rw [hp0, sub_zero, intervalIntegral.integral_add (hia.const_mul _) hit,
    intervalIntegral.integral_const_mul] at hi
  exact hi.symm

/-- The true infinite primitive recurrence, with its boundary basepoint
fixed by the actual zero initial driven vector. -/
theorem physicalDrivenGauge_primitive_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) (j + 1) θ =
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        physicalDrivenGauge γ E (physicalDrivenVector W g) j s) := by
  let y := physicalDrivenVector W g
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hp : Tendsto (fun N : ℕ => physicalDrivenGaugePartial γ E y (j + 1) N θ) atTop
      (𝓝 (physicalDrivenGauge γ E y (j + 1) θ)) := by
    have h_simpa := ((summable_norm_physicalDrivenGaugeTerm γ E y (j + 1) θ).of_norm.hasSum.tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 1)
    simp only [physicalDrivenGaugePartial, Function.comp_apply, Function.comp_def] at h_simpa ⊢
    exact h_simpa
  have ha := physicalDrivenGaugePartial_weightedIntegral_tendsto_to γ hγ.continuous E y hy j
    (fun s => conj (deriv γ s))
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn hθ
  have ht := (physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ.continuous E y hy (j + 2)
    (deriv γ) hγ.continuous_deriv_one.continuousOn hθ).summable.tendsto_atTop_zero
  have he (N : ℕ) := physicalDrivenGaugePartial_primitive_of_intervalIntegrable hK hγ hW g hg j N hθ
  have hr := (ha.const_mul (physicalDrivenQ E ^ 2)).add ht
  simp only [add_zero] at hr
  exact tendsto_nhds_unique hp (hr.congr' (Eventually.of_forall fun N => (he N).symm))

/-- Every actual gauge row is the iterated physical boundary primitive
of the zeroth gauge, including its prescribed constant. -/
theorem physicalDrivenGauge_eq_volterraPrimitiveIterate_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) j θ =
      (physicalDrivenQ E ^ 2) ^ j * volterraPrimitiveIterate
        (fun s => conj (deriv γ s))
        (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ := by
  induction j generalizing θ with
  | zero => simp [volterraPrimitiveIterate]
  | succ j ih =>
    rw [physicalDrivenGauge_primitive_of_intervalIntegrable hK hγ hW g hg j hθ]
    have hi : (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        physicalDrivenGauge γ E (physicalDrivenVector W g) j s) =
        (physicalDrivenQ E ^ 2) ^ j * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
          volterraPrimitiveIterate (fun s => conj (deriv γ s))
            (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hθ.1] at hs
      dsimp only
      rw [ih ⟨hs.1, hs.2.trans hθ.2⟩]
      ring
    rw [hi, pow_succ', volterraPrimitiveIterate]
    ring

/-- Fixed-energy reconstruction of the actual zeroth physical trace.
Absolute convergence and the factorial inverse have already been proved. -/
theorem physicalDrivenRow_eq_volterraVekua_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenRow (physicalDrivenVector W g) 0 θ =
      ∑' j : ℕ, physicalDrivenCentered γ θ ^ j / (j.factorial : ℂ) *
        ((physicalDrivenQ E ^ 2) ^ j * volterraPrimitiveIterate
          (fun s => conj (deriv γ s))
          (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ) := by
  rw [← physicalDrivenGauge_inverse γ E (physicalDrivenVector W g) θ]
  apply tsum_congr
  intro j
  rw [physicalDrivenGauge_eq_volterraPrimitiveIterate_of_intervalIntegrable hK hγ hW g hg j hθ]

/-- The coefficient is exactly the physical Vekua coefficient at the
original real energy, using the actual square-root wave number. -/
theorem physicalDrivenRow_eq_volterraVekua_of_nonnegative_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenRow (physicalDrivenVector W g) 0 θ =
      ∑' j : ℕ, (-(E : ℂ) / 4) ^ j / (j.factorial : ℂ) *
        physicalDrivenCentered γ θ ^ j * volterraPrimitiveIterate
          (fun s => conj (deriv γ s))
          (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ := by
  rw [physicalDrivenRow_eq_volterraVekua_of_intervalIntegrable hK hγ hW g hg hθ]
  apply tsum_congr
  intro j
  rw [physicalDrivenQ_sq hE]
  ring

/-- The genuine primitive recurrence applies directly to arbitrary L²
forcing on the actual parameter interval. -/
theorem physicalDrivenGauge_primitive_of_memLp
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (j : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) (j + 1) θ =
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        physicalDrivenGauge γ E (physicalDrivenVector W g) j s) :=
  physicalDrivenGauge_primitive_of_intervalIntegrable hK hγ hW g
    (intervalIntegrable_boundary_of_memLp g hg) j hθ

theorem physicalDrivenGauge_eq_volterraPrimitiveIterate_of_memLp
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (j : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) j θ =
      (physicalDrivenQ E ^ 2) ^ j * volterraPrimitiveIterate
        (fun s => conj (deriv γ s))
        (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ :=
  physicalDrivenGauge_eq_volterraPrimitiveIterate_of_intervalIntegrable hK hγ hW g
    (intervalIntegrable_boundary_of_memLp g hg) j hθ

theorem physicalDrivenRow_eq_volterraVekua_of_memLp
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenRow (physicalDrivenVector W g) 0 θ =
      ∑' j : ℕ, physicalDrivenCentered γ θ ^ j / (j.factorial : ℂ) *
        ((physicalDrivenQ E ^ 2) ^ j * volterraPrimitiveIterate
          (fun s => conj (deriv γ s))
          (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ) :=
  physicalDrivenRow_eq_volterraVekua_of_intervalIntegrable hK hγ hW g
    (intervalIntegrable_boundary_of_memLp g hg) hθ

/-- Reconstruction retains the original real energy and boundary origin
for every actual L² forcing, with no extra zeroth-row derivative premise. -/
theorem physicalDrivenRow_eq_volterraVekua_of_nonnegative_of_memLp
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenRow (physicalDrivenVector W g) 0 θ =
      ∑' j : ℕ, (-(E : ℂ) / 4) ^ j / (j.factorial : ℂ) *
        physicalDrivenCentered γ θ ^ j * volterraPrimitiveIterate
          (fun s => conj (deriv γ s))
          (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ :=
  physicalDrivenRow_eq_volterraVekua_of_nonnegative_of_intervalIntegrable hK hγ hE hW g
    (intervalIntegrable_boundary_of_memLp g hg) hθ

theorem physicalDrivenGauge_primitive_boundaryL2
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) (j : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) (j + 1) θ =
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        physicalDrivenGauge γ E (physicalDrivenVector W g) j s) :=
  physicalDrivenGauge_primitive_of_intervalIntegrable hK hγ hW g
    (intervalIntegrable_boundaryL2 g) j hθ

theorem physicalDrivenGauge_eq_volterraPrimitiveIterate_boundaryL2
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) (j : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) j θ =
      (physicalDrivenQ E ^ 2) ^ j * volterraPrimitiveIterate
        (fun s => conj (deriv γ s))
        (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ :=
  physicalDrivenGauge_eq_volterraPrimitiveIterate_of_intervalIntegrable hK hγ hW g
    (intervalIntegrable_boundaryL2 g) j hθ

theorem physicalDrivenRow_eq_volterraVekua_of_nonnegative_boundaryL2
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenRow (physicalDrivenVector W g) 0 θ =
      ∑' j : ℕ, (-(E : ℂ) / 4) ^ j / (j.factorial : ℂ) *
        physicalDrivenCentered γ θ ^ j * volterraPrimitiveIterate
          (fun s => conj (deriv γ s))
          (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) j θ :=
  physicalDrivenRow_eq_volterraVekua_of_nonnegative_of_intervalIntegrable hK hγ hE hW g
    (intervalIntegrable_boundaryL2 g) hθ

end PolyaNeumann

end
