module

public import RequestProject.LocalConformalPrincipalModes

/-!
# Compactness of the actual normalized Neumann principal remainder

The nonzero weak mode equations give a factorization through one Sobolev
derivative. The constant Fourier coefficient is retained by the genuine
rank-one projection. All operators below use the supplied physical conformal
coordinates and the actual Neumann resolvent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric

/-- The bounded symbol `(1 + |n|) / |n|`, with its zero mode removed. -/
def normalizedInverseAbsSymbol (n : ℤ) : ℂ :=
  if n = 0 then 0 else ((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)

theorem normalizedInverseAbsSymbol_pos (m : ℕ) :
    normalizedInverseAbsSymbol ((m + 1 : ℕ) : ℤ) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hn : ((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
  have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_natCast,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  simp only [normalizedInverseAbsSymbol, if_neg hn, hweight, Int.cast_natCast,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]

theorem normalizedInverseAbsSymbol_neg (m : ℕ) :
    normalizedInverseAbsSymbol (-((m + 1 : ℕ) : ℤ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hn : -((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
  have hweight : sobWeight (-((m + 1 : ℕ) : ℤ)) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  simp only [normalizedInverseAbsSymbol, if_neg hn, hweight, Int.cast_neg,
    Int.cast_natCast, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]

private theorem norm_successor_ratio_le_two (m : ℕ) :
    ‖(((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ))‖ ≤ 2 := by
  have hk : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [Complex.norm_of_nonneg (div_nonneg (by positivity) hk.le), div_le_iff₀ hk]
  push_cast
  linarith

theorem norm_normalizedInverseAbsSymbol_le (n : ℤ) :
    ‖normalizedInverseAbsSymbol n‖ ≤ 2 := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => norm_num [normalizedInverseAbsSymbol]
      | succ m =>
          change ‖normalizedInverseAbsSymbol ((m + 1 : ℕ) : ℤ)‖ ≤ 2
          rw [normalizedInverseAbsSymbol_pos]
          exact norm_successor_ratio_le_two m
  | negSucc m =>
      have hi : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
      rw [hi, normalizedInverseAbsSymbol_neg]
      exact norm_successor_ratio_le_two m

/-- The bounded diagonal operator for the inverse absolute frequency symbol. -/
def normalizedInverseAbsOperator : L2Z →L[ℂ] L2Z :=
  diagOp normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le

@[simp] theorem normalizedInverseAbsOperator_apply (b : L2Z) (n : ℤ) :
    normalizedInverseAbsOperator b n = normalizedInverseAbsSymbol n * b n :=
  diagOp_apply normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le b n

theorem norm_normalizedInverseAbsOperator_le : ‖normalizedInverseAbsOperator‖ ≤ 2 :=
  norm_diagOp_le normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le

/-- The rank-one projection onto the constant Fourier coefficient. -/
def zeroModeProjection : L2Z →L[ℂ] L2Z :=
  diagOp (fun n : ℤ => if n = 0 then (1 : ℂ) else 0) 1
    (fun n => by
      change ‖(if n = 0 then (1 : ℂ) else 0)‖ ≤ 1
      split_ifs <;> simp)

@[simp] theorem zeroModeProjection_apply (b : L2Z) (n : ℤ) :
    zeroModeProjection b n = (if n = 0 then 1 else 0) * b n :=
  diagOp_apply _ _ _ b n

theorem zeroModeProjection_eq_single (b : L2Z) :
    zeroModeProjection b = lp.single 2 0 (b 0) := by
  apply lp.ext
  funext n
  rw [zeroModeProjection_apply, lp.single_apply]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn]

theorem isCompactOperator_zeroModeProjection : IsCompactOperator zeroModeProjection := by
  unfold zeroModeProjection
  apply isCompactOperator_diagOp_of_finite _ _ _ ({0} : Finset ℤ)
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [hn]

private theorem sobolevSmoothing_one_apply (b : L2Z) (n : ℤ) :
    sobolevSmoothing 1 (by norm_num) b n = (sobWeight n : ℂ)⁻¹ * b n := by
  simp only [sobolevSmoothing, diagOp_apply, Real.rpow_neg_one, Complex.ofReal_inv]

private theorem principal_remainder_scalar {s k : ℝ}
    (hk : k ≠ 0) (hs : s ≠ 0) (hsk : s = k + 1)
    {t b d E : ℂ} (h : t - ((s / k : ℝ) : ℂ) * b = E * d) :
    t - b = (s : ℂ)⁻¹ *
      (((s / k : ℝ) : ℂ) * b + E * ((s : ℂ) * d)) := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hskc : (s : ℂ) = (k : ℂ) + 1 := by exact_mod_cast hsk
  have hsc' : (k : ℂ) + 1 ≠ 0 := by rwa [hskc] at hsc
  calc
    t - b = ((s / k : ℝ) : ℂ) * b - b + E * d := by linear_combination h
    _ = _ := by
      simp only [Complex.ofReal_div, hskc]
      field_simp [hkc, hsc']
      ring

private theorem principal_remainder_mode (n : ℤ) (hn : n ≠ 0)
    {t b d E : ℂ}
    (h : t - normalizedInverseAbsSymbol n * b = E * d) :
    t - b = (sobWeight n : ℂ)⁻¹ *
      (normalizedInverseAbsSymbol n * b + E * ((sobWeight n : ℂ) * d)) := by
  have hk : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hn)
  have hs : sobWeight n ≠ 0 := (sobWeight_pos n).ne'
  have hsk : sobWeight n = |(n : ℝ)| + 1 := by unfold sobWeight; ring
  simp only [normalizedInverseAbsSymbol, if_neg hn] at h ⊢
  exact principal_remainder_scalar hk hs hsk h

private theorem principal_factorization_of_modes
    (T M : L2Z →L[ℂ] L2Z) (E : ℝ) (d : L2Z → ℤ → ℂ)
    (hM : ∀ b n, M b n = (sobWeight n : ℂ) * d b n)
    (hz : ∀ b, d b 0 = 0)
    (hp : ∀ b (m : ℕ), T b ((m + 1 : ℕ) : ℤ) -
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        b ((m + 1 : ℕ) : ℤ) = (E : ℂ) * d b ((m + 1 : ℕ) : ℤ))
    (hn : ∀ b (m : ℕ), T b (-((m + 1 : ℕ) : ℤ)) -
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        b (-((m + 1 : ℕ) : ℤ)) = (E : ℂ) * d b (-((m + 1 : ℕ) : ℤ))) :
    T - 1 = (sobolevSmoothing 1 (by norm_num)).comp
      (normalizedInverseAbsOperator + (E : ℂ) • M) +
        zeroModeProjection.comp (T - 1) := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, sobolevSmoothing_one_apply,
    normalizedInverseAbsOperator_apply, zeroModeProjection_apply,
    lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, hM]
  by_cases hn0 : n = 0
  · subst n
    simp [normalizedInverseAbsSymbol, hz]
  · rw [if_neg hn0, zero_mul, add_zero]
    apply principal_remainder_mode n hn0
    cases n with
    | ofNat k =>
        cases k with
        | zero => exact (hn0 rfl).elim
        | succ m =>
            change T b ((m + 1 : ℕ) : ℤ) -
              normalizedInverseAbsSymbol ((m + 1 : ℕ) : ℤ) *
                b ((m + 1 : ℕ) : ℤ) = (E : ℂ) * d b ((m + 1 : ℕ) : ℤ)
            rw [normalizedInverseAbsSymbol_pos]
            exact hp b m
    | negSucc m =>
        have hi : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
        rw [hi, normalizedInverseAbsSymbol_neg]
        exact hn b m

private theorem normalizedNeumannBoundary_apply {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E : ℝ) (b : L2Z) :
    normalizedNeumannBoundary Q E b = Q (normalizedNeumannPoisson Q E b) :=
  ContinuousLinearMap.comp_apply Q (normalizedNeumannPoisson Q E) b

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

/-- The bounded factor before the compact one-derivative Fourier smoothing. -/
def localConformalPrincipalFactor (E : ℝ) : L2Z →L[ℂ] L2Z :=
  normalizedInverseAbsOperator + (E : ℂ) •
    ((localConformalMassFourierH1 hR F hFs hL hK).comp
      (normalizedNeumannPoisson (localConformalDiskHalfTrace hR F hFs hL) E))

include hb hhol hinj hC e he hsource hes in
theorem localConformal_principal_factorization (E : ℝ)
    (hE : IsUnit (h1HelmholtzForm (F '' ball (0 : ℂ) 1) E)) :
    normalizedNeumannBoundary (localConformalDiskHalfTrace hR F hFs hL) E - 1 =
      (sobolevSmoothing 1 (by norm_num)).comp
        (localConformalPrincipalFactor hR F hFs hL hK E) +
      zeroModeProjection.comp
        (normalizedNeumannBoundary (localConformalDiskHalfTrace hR F hFs hL) E - 1) := by
  refine principal_factorization_of_modes
    (normalizedNeumannBoundary (localConformalDiskHalfTrace hR F hFs hL) E)
    ((localConformalMassFourierH1 hR F hFs hL hK).comp
      (normalizedNeumannPoisson (localConformalDiskHalfTrace hR F hFs hL) E)) E
    (fun b n => diskMassForcingCoeff
      (localConformalMassForcing hR F hFs hL hK
        (normalizedNeumannPoisson (localConformalDiskHalfTrace hR F hFs hL) E b)) n)
    ?_ ?_ ?_ ?_
  · intro b n
    simp only [ContinuousLinearMap.comp_apply, localConformalMassFourierH1_apply]
  · intro b
    simp only [diskMassForcingCoeff]
  · intro b m
    have hu := normalizedNeumannPoisson_isSolution
      (localConformalDiskHalfTrace hR F hFs hL) hE b
    simpa only [normalizedNeumannBoundary_apply] using
      localConformal_principal_mode_pos hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b
        (normalizedNeumannPoisson (localConformalDiskHalfTrace hR F hFs hL) E b) hu m
  · intro b m
    have hu := normalizedNeumannPoisson_isSolution
      (localConformalDiskHalfTrace hR F hFs hL) hE b
    simpa only [normalizedNeumannBoundary_apply] using
      localConformal_principal_mode_neg hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b
        (normalizedNeumannPoisson (localConformalDiskHalfTrace hR F hFs hL) E b) hu m

include hb hhol hinj hC e he hsource hes in
theorem isCompactOperator_localConformal_normalizedNeumannBoundary_sub_one
    (E : ℝ) (hE : IsUnit (h1HelmholtzForm (F '' ball (0 : ℂ) 1) E)) :
    IsCompactOperator
      (normalizedNeumannBoundary (localConformalDiskHalfTrace hR F hFs hL) E -
        (1 : L2Z →L[ℂ] L2Z)) := by
  obtain ⟨K, _, hK⟩ := exists_localConformalMassDensity_bound hR F hFs
  rw [localConformal_principal_factorization hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE]
  exact ((isCompactOperator_sobolevSmoothing (by norm_num : (0 : ℝ) < 1)).comp_clm
    (localConformalPrincipalFactor hR F hFs hL hK E)).add
      (isCompactOperator_zeroModeProjection.comp_clm
        (normalizedNeumannBoundary (localConformalDiskHalfTrace hR F hFs hL) E - 1))

end

end PolyaNeumann

end
