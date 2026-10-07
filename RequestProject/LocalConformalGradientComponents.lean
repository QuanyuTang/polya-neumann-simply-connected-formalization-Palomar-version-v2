module

public import RequestProject.LocalConformalMass
public import RequestProject.ChainRule

/-!
# Genuine componentwise conformal transport

The checked physical mass identity extends through the dense H¹ inclusion
to a norm-preserving weighted L² pullback. Bounded coordinate ratios of the
actual Jacobian then transport each actual weak gradient component.
This uses the supplied local conformal map and no plane homeomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

private theorem gradient_extendOfNorm_eq
    {H X Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (V : H →L[ℂ] X) (M : H →L[ℂ] Y) (hd : DenseRange V)
    (hn : ∀ u, ‖M u‖ = ‖V u‖) (u : H) :
    M.toLinearMap.extendOfNorm V.toLinearMap (V u) = M u := by
  exact LinearMap.extendOfNorm_eq (f := M.toLinearMap) (e := V.toLinearMap) hd
    ⟨1, fun w => by rw [one_mul]; exact (hn w).le⟩ u

private theorem gradient_norm_extendOfNorm
    {H X Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (V : H →L[ℂ] X) (M : H →L[ℂ] Y) (hd : DenseRange V)
    (hn : ∀ u, ‖M u‖ = ‖V u‖) (v : X) :
    ‖M.toLinearMap.extendOfNorm V.toLinearMap v‖ = ‖v‖ := by
  let A : X →L[ℂ] Y := M.toLinearMap.extendOfNorm V.toLinearMap
  refine hd.induction_on (p := fun w => ‖A w‖ = ‖w‖) v ?_ ?_
  · exact isClosed_eq A.continuous.norm continuous_norm
  · intro u
    exact (congrArg norm (gradient_extendOfNorm_eq V M hd hn u)).trans (hn u)

private theorem gradient_eq_of_dense
    {S H Y : Type*} [TopologicalSpace H] [TopologicalSpace Y] [T2Space Y]
    (ι : S → H) (hd : DenseRange ι) (A B : H → Y)
    (hA : Continuous A) (hB : Continuous B)
    (he : ∀ s, A (ι s) = B (ι s)) (u : H) : A u = B u := by
  exact hd.induction_on u (isClosed_eq hA hB) he

section Coordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)

include hb hhol hinj hC in
private theorem mass_norm_eq_value (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖localConformalMassPullback hR F hFs hL hK u‖ =
      ‖h1Value (F '' ball (0 : ℂ) 1) u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (norm_sq_localConformalMassPullback hR F hFs hb hL hhol hinj hC hK u)

include hb hhol hinj hC in
private theorem mass_bound_by_value (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    ‖localConformalMassPullback hR F hFs hL hK u‖ ≤
      1 * ‖h1Value (F '' ball (0 : ℂ) 1) u‖ := by
  rw [one_mul, mass_norm_eq_value hR F hFs hb hL hhol hinj hC hK u]

/-- The actual Jacobian-weighted pullback on the whole physical L² space. -/
def localConformalWeightedL2Pullback :
    L2 (F '' ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  (localConformalMassPullback hR F hFs hL hK).toLinearMap.extendOfNorm
    (h1Value (F '' ball (0 : ℂ) 1)).toLinearMap

include hb hhol hinj hC in
theorem localConformalWeightedL2Pullback_h1Value
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    localConformalWeightedL2Pullback hR F hFs hL hK
      (h1Value (F '' ball (0 : ℂ) 1) u) =
        localConformalMassPullback hR F hFs hL hK u :=
  gradient_extendOfNorm_eq
    (h1Value (F '' ball (0 : ℂ) 1))
    (localConformalMassPullback hR F hFs hL hK)
    (h1Value_denseRange hL.1.1)
    (mass_norm_eq_value hR F hFs hb hL hhol hinj hC hK) u

include hb hhol hinj hC in
theorem norm_localConformalWeightedL2Pullback
    (v : L2 (F '' ball (0 : ℂ) 1)) :
    ‖localConformalWeightedL2Pullback hR F hFs hL hK v‖ = ‖v‖ :=
  gradient_norm_extendOfNorm
    (h1Value (F '' ball (0 : ℂ) 1))
    (localConformalMassPullback hR F hFs hL hK)
    (h1Value_denseRange hL.1.1)
    (mass_norm_eq_value hR F hFs hb hL hhol hinj hC hK) v

include hb hhol hinj hC in
theorem localConformalWeightedL2Pullback_injective :
    Function.Injective (localConformalWeightedL2Pullback hR F hFs hL hK) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← norm_localConformalWeightedL2Pullback hR F hFs hb hL hhol hinj hC hK (u - v),
    map_sub, huv, sub_self, norm_zero]

include hb hhol hinj hC in
theorem localConformalWeightedL2Pullback_smooth_ae (f : smoothTraceTests) :
    (localConformalWeightedL2Pullback hR F hFs hL hK
      (h1Value (F '' ball (0 : ℂ) 1) (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)) : ℂ → ℂ)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
        fun z => localConformalMassDensity F z * f (F z) := by
  rw [localConformalWeightedL2Pullback_h1Value hR F hFs hb hL hhol hinj hC hK,
    localConformalMassPullback_smooth_eq hR F hFs hb hL hhol hinj hC hK f]
  filter_upwards [lpBoundedMultiplier_ae (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)
    ((smoothTraceTests_memLp (ball (0 : ℂ) 1) (smoothDiskCompositionLin hR F hFs f)).toLp _),
    (smoothTraceTests_memLp (ball (0 : ℂ) 1) (smoothDiskCompositionLin hR F hFs f)).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hm hv hz
  rw [hm, hv, smoothDiskCompositionLin_eq_closedDisk hR F hFs f (ball_subset_closedBall hz)]

end Coordinates

/-- A real Jacobian coordinate divided by the actual conformal scale. -/
def localConformalChainRatio (F : ℂ → ℂ) (i j : Fin 2) (z : ℂ) : ℂ :=
  (coordRe j (fderiv ℝ F z (coordDir i)) / ‖fderiv ℝ F z 1‖ : ℝ)

private theorem real_fderiv_eq_complex_deriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (v : ℂ) :
    fderiv ℝ F z v = deriv F z * v := by
  rw [hF.fderiv_restrictScalars ℝ]
  change fderiv ℂ F z v = _
  exact fderiv_eq_deriv_mul

private theorem scale_ne_zero {C : ℝ} {F : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : ‖fderiv ℝ F z 1‖ ≠ 0 := by
  rw [real_fderiv_eq_complex_deriv (hhol.differentiableAt (isOpen_ball.mem_nhds hz)), mul_one]
  intro hzero
  have h := hC z hz
  rw [hzero] at h
  norm_num at h

theorem norm_localConformalChainRatio_le_one {F : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (i j : Fin 2)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : ‖localConformalChainRatio F i j z‖ ≤ 1 := by
  have hn : ‖fderiv ℝ F z (coordDir i)‖ = ‖fderiv ℝ F z 1‖ := by
    simp only [real_fderiv_eq_complex_deriv (hhol.differentiableAt (isOpen_ball.mem_nhds hz)),
      norm_mul, norm_coordDir, mul_one]
  have hb := abs_coordRe_le j (fderiv ℝ F z (coordDir i))
  rw [hn] at hb
  unfold localConformalChainRatio
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _)]
  by_cases hs : ‖fderiv ℝ F z 1‖ = 0
  · simp [hs]
  · exact (div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs))).mpr hb

theorem localConformalChainRatio_aestronglyMeasurable (F : ℂ → ℂ) (i j : Fin 2) :
    AEStronglyMeasurable (localConformalChainRatio F i j)
      (volume.restrict (ball (0 : ℂ) 1)) := by
  have hn : Measurable (fun z => ‖fderiv ℝ F z 1‖) :=
    (measurable_fderiv_apply_const ℝ F (1 : ℂ)).norm
  exact (Complex.measurable_ofReal.comp ((measurable_coordRe_fderiv F i j).div hn)).aestronglyMeasurable

def localConformalChainRatioMultiplier (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (i j : Fin 2) :
    L2 (ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  lpBoundedMultiplier (C := (1 : ℝ)) (localConformalChainRatio F i j)
    (localConformalChainRatio_aestronglyMeasurable F i j)
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact norm_localConformalChainRatio_le_one hhol i j hz)

theorem localConformalChainRatioMultiplier_ae (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (i j : Fin 2)
    (v : L2 (ball (0 : ℂ) 1)) :
    (localConformalChainRatioMultiplier F hhol i j v : ℂ → ℂ)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)] fun z => localConformalChainRatio F i j z * v z :=
  lpBoundedMultiplier_ae (C := (1 : ℝ)) (localConformalChainRatio F i j)
    (localConformalChainRatio_aestronglyMeasurable F i j)
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact norm_localConformalChainRatio_le_one hhol i j hz) v

private theorem chainRatio_mul_massDensity {C : ℝ} (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (i j : Fin 2) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    localConformalChainRatio F i j z * localConformalMassDensity F z =
      (coordRe j (fderiv ℝ F z (coordDir i)) : ℂ) := by
  unfold localConformalChainRatio localConformalMassDensity
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (scale_ne_zero hhol hC hz)]

private def smoothTraceDirectionalTest (f : smoothTraceTests) (j : Fin 2) : smoothTraceTests :=
  ⟨dirD (f : ℂ → ℂ) (coordDir j), f.property.dirD (coordDir j)⟩

private theorem smoothTraceDirectionalTest_value (Ω : Set ℂ) (f : smoothTraceTests) (j : Fin 2) :
    h1Value Ω (smoothTraceH1 Ω (smoothTraceDirectionalTest f j)) =
      h1Gradient Ω j (smoothTraceH1 Ω f) := by
  rw [h1Value_smoothTraceH1, h1Gradient_smoothTraceH1]
  exact MemLp.toLp_congr (smoothTraceTests_memLp Ω (smoothTraceDirectionalTest f j))
    (smoothTraceTests_memLp_deriv Ω f j) (Eventually.of_forall fun _ => rfl)

section Components

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)

def localConformalGradientComponent (i : Fin 2) :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  ∑ j : Fin 2, (localConformalChainRatioMultiplier F hhol i j).comp
    ((localConformalWeightedL2Pullback hR F hFs hL hK).comp
      (h1Gradient (F '' ball (0 : ℂ) 1) j))

include hb hinj hC in
private theorem localConformalGradientComponent_smooth (i : Fin 2) (f : smoothTraceTests) :
    h1Gradient (ball (0 : ℂ) 1) i
      (localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)) =
      localConformalGradientComponent hR F hFs hL hhol hK i
        (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) := by
  rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f,
    h1Gradient_smoothTraceH1]
  let v (j : Fin 2) := localConformalWeightedL2Pullback hR F hFs hL hK
    (h1Gradient (F '' ball (0 : ℂ) 1) j (smoothTraceH1 (F '' ball (0 : ℂ) 1) f))
  have hv (j : Fin 2) : (v j : ℂ → ℂ) =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      fun z => localConformalMassDensity F z * dirD (f : ℂ → ℂ) (coordDir j) (F z) := by
    dsimp only [v]
    rw [← smoothTraceDirectionalTest_value]
    exact localConformalWeightedL2Pullback_smooth_ae hR F hFs hb hL hhol hinj hC hK
      (smoothTraceDirectionalTest f j)
  simp only [localConformalGradientComponent, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  change (smoothTraceTests_memLp_deriv (ball (0 : ℂ) 1)
    (smoothDiskCompositionLin hR F hFs f) i).toLp _ =
      localConformalChainRatioMultiplier F hhol i 0 (v 0) +
        localConformalChainRatioMultiplier F hhol i 1 (v 1)
  apply Lp.ext
  filter_upwards [(smoothTraceTests_memLp_deriv (ball (0 : ℂ) 1)
    (smoothDiskCompositionLin hR F hFs f) i).coeFn_toLp,
    Lp.coeFn_add (localConformalChainRatioMultiplier F hhol i 0 (v 0))
      (localConformalChainRatioMultiplier F hhol i 1 (v 1)),
    localConformalChainRatioMultiplier_ae F hhol i 0 (v 0),
    localConformalChainRatioMultiplier_ae F hhol i 1 (v 1), hv 0, hv 1,
    ae_restrict_mem measurableSet_ball] with z hd ha h₀ h₁ hv₀ hv₁ hz
  rw [hd, ha]
  simp only [Pi.add_apply]
  rw [h₀, h₁, hv₀, hv₁, ← mul_assoc, ← mul_assoc,
    chainRatio_mul_massDensity F hhol hC i 0 hz, chainRatio_mul_massDensity F hhol hC i 1 hz,
    fderiv_smoothDiskCompositionLin hR F hFs f (ball_subset_closedBall hz)]
  change (fderiv ℝ (f : ℂ → ℂ) (F z)) (fderiv ℝ F z (coordDir i)) = _
  simpa only [Fin.sum_univ_two, smul_eq_mul, dirD] using
    (clm_apply_eq_sum_coordRe (fderiv ℝ (f : ℂ → ℂ) (F z))
      (fderiv ℝ F z (coordDir i)))

include hb hinj hC in
/-- The full componentwise chain rule for every genuine physical H¹ input. -/
theorem localConformalH1Pullback_gradient_component
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) (i : Fin 2) :
    h1Gradient (ball (0 : ℂ) 1) i (localConformalH1Pullback hR F hFs hL u) =
      localConformalGradientComponent hR F hFs hL hhol hK i u := by
  have hd : DenseRange (fun f : smoothTraceTests =>
      smoothTraceH1 (F '' ball (0 : ℂ) 1) f) :=
    denseRange_smoothTraceH1Lin hb hL
  exact gradient_eq_of_dense
    (S := smoothTraceTests) (H := NeumannH1 (F '' ball (0 : ℂ) 1))
    (Y := L2 (ball (0 : ℂ) 1))
    (fun f => smoothTraceH1 (F '' ball (0 : ℂ) 1) f) hd
    (fun v => h1Gradient (ball (0 : ℂ) 1) i (localConformalH1Pullback hR F hFs hL v))
    (fun v => localConformalGradientComponent hR F hFs hL hhol hK i v)
    ((h1Gradient (ball (0 : ℂ) 1) i).continuous.comp
      (localConformalH1Pullback hR F hFs hL).continuous)
    (localConformalGradientComponent hR F hFs hL hhol hK i).continuous
    (localConformalGradientComponent_smooth hR F hFs hb hL hhol hinj hC hK i) u

end Components

/-- The actual unit phase converting the antiholomorphic physical derivative
to its conformal-coordinate derivative. -/
def localConformalAntiholomorphicPhase (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  star (fderiv ℝ F z 1) / (‖fderiv ℝ F z 1‖ : ℂ)

theorem antiholomorphicPhase_measurable (F : ℂ → ℂ) :
    Measurable (localConformalAntiholomorphicPhase F) := by
  have hd := measurable_fderiv_apply_const ℝ F (1 : ℂ)
  exact (Complex.continuous_conj.measurable.comp hd).div (Complex.measurable_ofReal.comp hd.norm)

theorem norm_antiholomorphicPhase_le_one (F : ℂ → ℂ) (z : ℂ) :
    ‖localConformalAntiholomorphicPhase F z‖ ≤ 1 := by
  unfold localConformalAntiholomorphicPhase
  rw [norm_div, norm_star, Complex.norm_of_nonneg (norm_nonneg _)]
  by_cases h : ‖fderiv ℝ F z 1‖ = 0
  · simp [h]
  · simp [div_self h]

def localConformalAntiholomorphicPhaseMultiplier (F : ℂ → ℂ) :
    L2 (ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  lpBoundedMultiplier (localConformalAntiholomorphicPhase F)
    (antiholomorphicPhase_measurable F).aestronglyMeasurable
    (Eventually.of_forall (norm_antiholomorphicPhase_le_one F))

theorem localConformalAntiholomorphicPhaseMultiplier_ae (F : ℂ → ℂ)
    (v : L2 (ball (0 : ℂ) 1)) :
    (localConformalAntiholomorphicPhaseMultiplier F v : ℂ → ℂ)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
        fun z => localConformalAntiholomorphicPhase F z * v z :=
  lpBoundedMultiplier_ae (localConformalAntiholomorphicPhase F)
    (antiholomorphicPhase_measurable F).aestronglyMeasurable
    (Eventually.of_forall (norm_antiholomorphicPhase_le_one F)) v

private def antiholomorphicPhaseInverseMultiplier (F : ℂ → ℂ) :
    L2 (ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  lpBoundedMultiplier (C := (1 : ℝ)) (fun z => star (localConformalAntiholomorphicPhase F z))
    (Complex.continuous_conj.measurable.comp (antiholomorphicPhase_measurable F)).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℂ => by
      rw [norm_star]
      exact norm_antiholomorphicPhase_le_one F z))

private theorem antiholomorphicPhaseInverseMultiplier_ae (F : ℂ → ℂ)
    (v : L2 (ball (0 : ℂ) 1)) :
    (antiholomorphicPhaseInverseMultiplier F v : ℂ → ℂ)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
        fun z => star (localConformalAntiholomorphicPhase F z) * v z :=
  lpBoundedMultiplier_ae (C := (1 : ℝ)) (fun z => star (localConformalAntiholomorphicPhase F z))
    (Complex.continuous_conj.measurable.comp (antiholomorphicPhase_measurable F)).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℂ => by
      rw [norm_star]
      exact norm_antiholomorphicPhase_le_one F z)) v

private theorem norm_antiholomorphicPhase_eq_one {C : ℝ} (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖localConformalAntiholomorphicPhase F z‖ = 1 := by
  unfold localConformalAntiholomorphicPhase
  rw [norm_div, norm_star, Complex.norm_of_nonneg (norm_nonneg _),
    div_self (scale_ne_zero hhol hC hz)]

/-- Cancellation of this genuine Jacobian phase on the actual disk L² space. -/
theorem localConformalAntiholomorphicPhaseMultiplier_injective {C : ℝ} (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2) :
    Function.Injective (localConformalAntiholomorphicPhaseMultiplier F) := by
  have hinv : Function.LeftInverse (antiholomorphicPhaseInverseMultiplier F)
      (localConformalAntiholomorphicPhaseMultiplier F) := by
    intro v
    apply Lp.ext
    filter_upwards [antiholomorphicPhaseInverseMultiplier_ae F
      (localConformalAntiholomorphicPhaseMultiplier F v),
      localConformalAntiholomorphicPhaseMultiplier_ae F v,
      ae_restrict_mem measurableSet_ball] with z hi hd hz
    rw [hi, hd, ← mul_assoc]
    change star (localConformalAntiholomorphicPhase F z) *
      localConformalAntiholomorphicPhase F z * v z = v z
    simp only [Complex.star_def]
    rw [Complex.conj_mul', norm_antiholomorphicPhase_eq_one F hhol hC hz]
    simp
  exact hinv.injective

private theorem antiholomorphicPhase_eq_ratios (F : ℂ → ℂ) (z : ℂ) :
    localConformalAntiholomorphicPhase F z = localConformalChainRatio F 0 0 z +
      (-Complex.I) * localConformalChainRatio F 0 1 z := by
  apply Complex.ext <;>
    simp [localConformalAntiholomorphicPhase, localConformalChainRatio,
      coordDir, coordRe, Complex.div_ofReal_re, Complex.div_ofReal_im, neg_div]

private theorem antiholomorphicPhaseMultiplier_eq_ratios (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (v : L2 (ball (0 : ℂ) 1)) :
    localConformalAntiholomorphicPhaseMultiplier F v =
      localConformalChainRatioMultiplier F hhol 0 0 v +
        (-Complex.I) • localConformalChainRatioMultiplier F hhol 0 1 v := by
  apply Lp.ext
  filter_upwards [localConformalAntiholomorphicPhaseMultiplier_ae F v,
    localConformalChainRatioMultiplier_ae F hhol 0 0 v,
    localConformalChainRatioMultiplier_ae F hhol 0 1 v,
    Lp.coeFn_add (localConformalChainRatioMultiplier F hhol 0 0 v)
      ((-Complex.I) • localConformalChainRatioMultiplier F hhol 0 1 v),
    Lp.coeFn_smul (-Complex.I) (localConformalChainRatioMultiplier F hhol 0 1 v)]
    with z hd h₀ h₁ ha hs
  rw [hd, ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h₀, h₁, antiholomorphicPhase_eq_ratios]
  ring

/-- The true chain rule specialized to an actual weak antiholomorphic vector. -/
theorem localConformalH1Pullback_gradient_antiholomorphic {R C K : ℝ}
    (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (u : NeumannH1 (F '' ball (0 : ℂ) 1))
    (hu : h1Gradient (F '' ball (0 : ℂ) 1) 0 u =
      Complex.I • h1Gradient (F '' ball (0 : ℂ) 1) 1 u) :
    h1Gradient (ball (0 : ℂ) 1) 0 (localConformalH1Pullback hR F hFs hL u) =
      localConformalAntiholomorphicPhaseMultiplier F
        (localConformalWeightedL2Pullback hR F hFs hL hK
          (h1Gradient (F '' ball (0 : ℂ) 1) 0 u)) := by
  have hy : h1Gradient (F '' ball (0 : ℂ) 1) 1 u =
      (-Complex.I) • h1Gradient (F '' ball (0 : ℂ) 1) 0 u := by
    rw [hu, smul_smul]
    simp
  rw [localConformalH1Pullback_gradient_component hR F hFs hb hL hhol hinj hC hK u 0,
    antiholomorphicPhaseMultiplier_eq_ratios F hhol]
  simp only [localConformalGradientComponent, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, hy, map_smul]

end PolyaNeumann

end
