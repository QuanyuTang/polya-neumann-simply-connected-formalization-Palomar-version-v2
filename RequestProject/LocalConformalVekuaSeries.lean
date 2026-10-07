module

public import RequestProject.LocalConformalHardyPrimitive
public import RequestProject.NeumannH1AffineMultiplier
public import RequestProject.NeumannH1VekuaWeakIdentity
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A Vekua series in the genuine physical H¹ space

The actual affine H¹ multiplier, the actual supplied-coordinate Hardy
extension, and the bounded normalized Hardy primitive give a norm-convergent
operator series. Its values are genuine physical H¹ vectors and its trace
series is obtained by applying the actual continuous H¹ trace.

All conformal coordinates and their smooth local inverse are supplied
explicitly. No initial boundary-map existence or Neumann boundary equation
is assumed by this construction.

Chosen-boundary-origin applications use p = F(1), the point corresponding
to angular origin zero in the actual normalized primitive. The general-p
construction below does not assert injectivity of the Vekua conormal map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

/-- The genuine complex coefficient at a fixed energy. -/
def physicalVekuaCoeff (E : ℂ) (j : ℕ) : ℂ := (-E / 4) ^ j / (j.factorial : ℂ)

theorem physicalVekuaCoeff_zero (E : ℂ) : physicalVekuaCoeff E 0 = 1 := by
  simp [physicalVekuaCoeff]

theorem physicalVekuaCoeff_succ (E : ℂ) (j : ℕ) :
    physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ) =
      (-E / 4) * physicalVekuaCoeff E j := by
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hjs : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : j + 1 ≠ 0)
  simp only [physicalVekuaCoeff, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp [hj, hjs]

theorem norm_physicalVekuaCoeff (E : ℂ) (j : ℕ) :
    ‖physicalVekuaCoeff E j‖ = ‖-E / 4‖ ^ j / (j.factorial : ℝ) := by
  simp only [physicalVekuaCoeff, norm_div, norm_pow, Complex.norm_natCast]

section BoundedSeries

variable {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

private theorem vekua_norm_clm_pow_le (A : X →L[ℂ] X) (j : ℕ) :
    ‖A ^ j‖ ≤ ‖A‖ ^ j := by
  induction j with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := X)
  | succ j ih =>
    calc
      ‖A ^ (j + 1)‖ = ‖A ^ j * A‖ := by rw [pow_succ]
      _ ≤ ‖A ^ j‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ ‖A‖ ^ j * ‖A‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg A)
      _ = ‖A‖ ^ (j + 1) := (pow_succ ‖A‖ j).symm

/-- The j-th bounded operator giving the genuine H¹ series term. -/
def boundedPhysicalVekuaTerm (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) : X →L[ℂ] H :=
  physicalVekuaCoeff E j • ((M ^ j).comp (U.comp (J ^ j)))

omit [CompleteSpace H] in
theorem boundedPhysicalVekuaTerm_apply (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) (b : X) :
    boundedPhysicalVekuaTerm M U J E j b =
      physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)) := rfl

omit [CompleteSpace H] in
theorem norm_boundedPhysicalVekuaTerm_le (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) :
    ‖boundedPhysicalVekuaTerm M U J E j‖ ≤
      ‖U‖ * ((‖-E / 4‖ * ‖M‖ * ‖J‖) ^ j / (j.factorial : ℝ)) := by
  have hc : ‖(M ^ j).comp (U.comp (J ^ j))‖ ≤
      ‖M ^ j‖ * (‖U‖ * ‖J ^ j‖) :=
    ((M ^ j).opNorm_comp_le (U.comp (J ^ j))).trans
      (mul_le_mul_of_nonneg_left (U.opNorm_comp_le (J ^ j)) (norm_nonneg _))
  calc
    _ = ‖physicalVekuaCoeff E j‖ * ‖(M ^ j).comp (U.comp (J ^ j))‖ := norm_smul _ _
    _ ≤ ‖physicalVekuaCoeff E j‖ * (‖M ^ j‖ * (‖U‖ * ‖J ^ j‖)) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ ≤ ‖physicalVekuaCoeff E j‖ * (‖M‖ ^ j * (‖U‖ * ‖J‖ ^ j)) := by
      gcongr
      · exact vekua_norm_clm_pow_le M j
      · exact vekua_norm_clm_pow_le J j
    _ = _ := by rw [norm_physicalVekuaCoeff]; simp only [mul_pow]; ring

omit [CompleteSpace H] in
theorem summable_norm_boundedPhysicalVekuaTerm (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) :
    Summable (fun j : ℕ => ‖boundedPhysicalVekuaTerm M U J E j‖) := by
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (norm_boundedPhysicalVekuaTerm_le M U J E)
    ((Real.summable_pow_div_factorial (‖-E / 4‖ * ‖M‖ * ‖J‖)).mul_left ‖U‖)

/-- A norm-convergent series of actual bounded maps. -/
def boundedPhysicalVekuaSeries (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) : X →L[ℂ] H :=
  ∑' j : ℕ, boundedPhysicalVekuaTerm M U J E j

theorem boundedPhysicalVekuaSeries_hasSum (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) :
    HasSum (fun j : ℕ => boundedPhysicalVekuaTerm M U J E j)
      (boundedPhysicalVekuaSeries M U J E) :=
  (summable_norm_boundedPhysicalVekuaTerm M U J E).of_norm.hasSum

omit [CompleteSpace H] in
theorem boundedPhysicalVekuaSeries_zero (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) : boundedPhysicalVekuaSeries M U J 0 = U := by
  unfold boundedPhysicalVekuaSeries
  rw [tsum_eq_single 0]
  · ext b
    simp only [boundedPhysicalVekuaTerm_apply, physicalVekuaCoeff_zero, pow_zero,
      ContinuousLinearMap.one_apply, one_smul]
  · intro j hj
    simp [boundedPhysicalVekuaTerm, physicalVekuaCoeff, hj]

theorem boundedPhysicalVekuaSeries_hasSum_apply (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (b : X) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)))
      (boundedPhysicalVekuaSeries M U J E b) := by
  simpa only [ContinuousLinearMap.apply_apply, boundedPhysicalVekuaTerm_apply] using
    (ContinuousLinearMap.apply ℂ H b).hasSum (boundedPhysicalVekuaSeries_hasSum M U J E)

omit [CompleteSpace H] in
theorem summable_norm_boundedPhysicalVekuaSeries_apply (M : H →L[ℂ] H)
    (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ) (b : X) :
    Summable (fun j : ℕ => ‖physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b))‖) := by
  have hs := (summable_norm_boundedPhysicalVekuaTerm M U J E).mul_right ‖b‖
  have h := Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => (boundedPhysicalVekuaTerm M U J E j).le_opNorm b) hs
  simpa only [boundedPhysicalVekuaTerm_apply] using h

omit [CompleteSpace H] in
theorem norm_boundedPhysicalVekuaSeries_le (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) :
    ‖boundedPhysicalVekuaSeries M U J E‖ ≤
      ‖U‖ * Real.exp (‖-E / 4‖ * ‖M‖ * ‖J‖) := by
  have hn := summable_norm_boundedPhysicalVekuaTerm M U J E
  have hd := (Real.summable_pow_div_factorial (‖-E / 4‖ * ‖M‖ * ‖J‖)).mul_left ‖U‖
  calc
    _ ≤ ∑' j : ℕ, ‖boundedPhysicalVekuaTerm M U J E j‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, ‖U‖ * ((‖-E / 4‖ * ‖M‖ * ‖J‖) ^ j / (j.factorial : ℝ)) :=
      Summable.tsum_le_tsum (norm_boundedPhysicalVekuaTerm_le M U J E) hn hd
    _ = _ := by rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

private theorem vekua_pow_commutes_apply (J : X →L[ℂ] X) (j : ℕ) (b : X) :
    (J ^ j) (J b) = J ((J ^ j) b) := by
  rw [← ContinuousLinearMap.mul_apply, ← pow_succ, pow_succ', ContinuousLinearMap.mul_apply]

private theorem vekua_series_D_shift {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X)
    (V D : H →L[ℂ] Y)
    (hD0 : ∀ b : X, D (U b) = 0)
    (hD : ∀ (j : ℕ) (b : X), D ((M ^ (j + 1)) (U b)) =
      ((j + 1 : ℕ) : ℂ) • V ((M ^ j) (U b))) (E : ℂ) (b : X) :
    D (boundedPhysicalVekuaSeries M U J E b) =
      (-E / 4) • V (boundedPhysicalVekuaSeries M U J E (J b)) := by
  let f : ℕ → Y := fun j =>
    D (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)))
  have hs : HasSum f (D (boundedPhysicalVekuaSeries M U J E b)) :=
    D.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E b)
  have hz : f 0 = 0 := by
    simp only [f, physicalVekuaCoeff_zero, pow_zero, ContinuousLinearMap.one_apply,
      one_smul, hD0]
  have hs1 : HasSum (fun j : ℕ => f (j + 1))
      (D (boundedPhysicalVekuaSeries M U J E b)) := by
    simpa only [Finset.sum_range_one, hz, sub_zero] using
      (hasSum_nat_add_iff' (f := f) 1).2 hs
  have hf (j : ℕ) : f (j + 1) = (-E / 4) •
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))) := by
    calc
      _ = (physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
          V ((M ^ j) (U ((J ^ (j + 1)) b))) := by
        dsimp only [f]
        rw [map_smul, hD, smul_smul]
      _ = _ := by
        rw [physicalVekuaCoeff_succ, pow_succ, ContinuousLinearMap.mul_apply,
          map_smul, smul_smul]
  have hr := (V.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E (J b))).const_smul
    (-E / 4)
  have hl : HasSum (fun j : ℕ => (-E / 4) •
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))))
      (D (boundedPhysicalVekuaSeries M U J E b)) := by
    simpa only [hf] using hs1
  exact hl.unique hr

private theorem vekua_series_Dbar_primitive {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X)
    (V Dbar : H →L[ℂ] Y) (b : X)
    (hDbar : ∀ j : ℕ, Dbar ((M ^ j) (U (J ((J ^ j) b)))) =
      V ((M ^ j) (U ((J ^ j) b)))) (E : ℂ) :
    Dbar (boundedPhysicalVekuaSeries M U J E (J b)) =
      V (boundedPhysicalVekuaSeries M U J E b) := by
  have hl := Dbar.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E (J b))
  have hr := V.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E b)
  have he (j : ℕ) :
      Dbar (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))) =
        V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b))) := by
    simp only [map_smul]
    rw [vekua_pow_commutes_apply J j b, hDbar j]
  have hl' : HasSum (fun j : ℕ =>
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b))))
      (Dbar (boundedPhysicalVekuaSeries M U J E (J b))) := by
    simpa only [he] using hl
  exact hl'.unique hr

end BoundedSeries

private theorem vekua_mapped_equality {Y : Type*} (N : Y → Y)
    {a b c d : Y} (ha : a = N b) (hb : b = c) (hd : d = N c) : a = d :=
  ha.trans ((congrArg N hb).trans hd.symm)

/-- The j-th affine power acts on actual H¹ values as the genuine polynomial. -/
theorem h1Value_neumannH1AffineMultiplier_pow_ae {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (j : ℕ) (u : NeumannH1 Ω) :
    (h1Value Ω (((neumannH1AffineMultiplier hb p) ^ j) u) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] fun z => (z - p) ^ j * h1Value Ω u z := by
  induction j with
  | zero =>
    simp only [pow_zero, ContinuousLinearMap.one_apply, pow_zero, one_mul]
    exact EventuallyEq.rfl
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    filter_upwards [h1Value_neumannH1AffineMultiplier_ae hb p
      (((neumannH1AffineMultiplier hb p) ^ j) u), ih] with z hm hj
    rw [hm, hj, pow_succ']
    ring

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

/-- The genuine physical Vekua operator, based at the supplied point p. -/
def localConformalVekuaH1 (p E : ℂ) :
    L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  boundedPhysicalVekuaSeries (neumannH1AffineMultiplier hb p)
    (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes)
    (localConformalHardyPrimitive hR F hFs) E

/-- The physical series based at the same boundary point F(1) as `antiPrim`. -/
def localConformalVekuaH1AtBoundaryOrigin (E : ℂ) :
    L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes (F 1) E

theorem localConformalVekuaH1_zero (p : ℂ) :
    localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p 0 =
      localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes :=
  boundedPhysicalVekuaSeries_zero _ _ _

theorem localConformalVekuaH1_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j •
      ((neumannH1AffineMultiplier hb p) ^ j)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
          (((localConformalHardyPrimitive hR F hFs) ^ j) b)))
      (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b) :=
  boundedPhysicalVekuaSeries_hasSum_apply _ _ _ E b

theorem summable_norm_localConformalVekuaH1 (p E : ℂ) (b : L2Z) :
    Summable (fun j : ℕ => ‖physicalVekuaCoeff E j •
      ((neumannH1AffineMultiplier hb p) ^ j)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
          (((localConformalHardyPrimitive hR F hFs) ^ j) b))‖) :=
  summable_norm_boundedPhysicalVekuaSeries_apply _ _ _ E b

theorem norm_localConformalVekuaH1_le (p E : ℂ) :
    ‖localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E‖ ≤
      ‖localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes‖ *
        Real.exp (‖-E / 4‖ * ‖neumannH1AffineMultiplier hb p‖ *
          ‖localConformalHardyPrimitive hR F hFs‖) :=
  norm_boundedPhysicalVekuaSeries_le _ _ _ E

/-- Applying the actual coordinate half trace preserves the true H¹ series. -/
theorem localConformalVekuaH1_halfTrace_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j •
      localConformalDiskHalfTrace hR F hFs hL
        (((neumannH1AffineMultiplier hb p) ^ j)
          (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
            (((localConformalHardyPrimitive hR F hFs) ^ j) b))))
      (localConformalDiskHalfTrace hR F hFs hL
        (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)) := by
  simpa only [map_smul] using (localConformalDiskHalfTrace hR F hFs hL).hasSum
    (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)

/-- The actual ordinary physical trace is the trace of the genuine H¹ limit. -/
theorem localConformalVekuaH1_boundaryTrace_hasSum {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ) (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j •
      h1BoundaryTrace hb hL hγ
        (((neumannH1AffineMultiplier hb p) ^ j)
          (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
            (((localConformalHardyPrimitive hR F hFs) ^ j) b))))
      (h1BoundaryTrace hb hL hγ
        (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)) := by
  simpa only [map_smul] using (h1BoundaryTrace hb hL hγ).hasSum
    (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)

include hhol in
theorem localConformalHardyPrimitive_pow_nonpositive (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    IsNonpositiveFourierSupport (((localConformalHardyPrimitive hR F hFs) ^ j) b) := by
  induction j with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply] using hbn
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact localConformalHardyPrimitive_nonpositive hR F hFs hhol _ ih

theorem localConformalHardyH1Extension_primitive_pow_gradient (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    h1Gradient (F '' ball (0 : ℂ) 1) 0
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (((localConformalHardyPrimitive hR F hFs) ^ (j + 1)) b)) =
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
          (((localConformalHardyPrimitive hR F hFs) ^ j) b)) := by
  rw [pow_succ', ContinuousLinearMap.mul_apply]
  exact localConformalHardyH1Extension_primitive_gradient hR F hFs hb hL hhol hinj hC hK
    e he hsource hes _ (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j)

theorem localConformalHardyH1Extension_primitive_pow_gradient_y (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    h1Gradient (F '' ball (0 : ℂ) 1) 1
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (((localConformalHardyPrimitive hR F hFs) ^ (j + 1)) b)) =
      (-Complex.I) • h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
          (((localConformalHardyPrimitive hR F hFs) ^ j) b)) := by
  rw [pow_succ', ContinuousLinearMap.mul_apply]
  exact localConformalHardyH1Extension_primitive_gradient_y hR F hFs hb hL hhol hinj hC hK
    e he hsource hes _ (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j)

/-- The actual physical Hardy extension is killed by the true first
Wirtinger derivative, for every normalized input. -/
theorem localConformalHardyH1Extension_wirtingerD_eq_zero (b : L2Z) :
    h1WirtingerD (F '' ball (0 : ℂ) 1)
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) = 0 :=
  h1WirtingerD_eq_zero_of_cauchyRiemann _ _
    (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b)

/-- The true conjugate derivative of the physical primitive is the
physical Hardy value; this keeps the full nonpositive subspace. -/
theorem localConformalHardyH1Extension_wirtingerDbar_primitive (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar (F '' ball (0 : ℂ) 1)
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (localConformalHardyPrimitive hR F hFs b)) =
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b) :=
  h1WirtingerDbar_eq_value_of_components _ _ _
    (localConformalHardyH1Extension_primitive_gradient hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b hbn)
    (localConformalHardyH1Extension_primitive_gradient_y hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b hbn)

/-- Differentiation of the genuine H¹ series shifts the primitive once.
The factorial identity is applied only after continuous L² differentiation. -/
theorem localConformalVekuaH1_wirtingerD (p E : ℂ) (b : L2Z) :
    h1WirtingerD (F '' ball (0 : ℂ) 1)
      (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b) =
      (-E / 4) • h1Value (F '' ball (0 : ℂ) 1)
        (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E
          (localConformalHardyPrimitive hR F hFs b)) := by
  apply vekua_series_D_shift
  · intro x
    exact localConformalHardyH1Extension_wirtingerD_eq_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes x
  · intro j x
    exact h1WirtingerD_affine_pow_of_antiholomorphic hb p
      (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes x)
      (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
        e he hsource hes x) j

/-- The conjugate derivative of the shifted series is exactly the original
physical value series, by the actual primitive derivative and affine rule. -/
theorem localConformalVekuaH1_wirtingerDbar_primitive (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar (F '' ball (0 : ℂ) 1)
      (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E
        (localConformalHardyPrimitive hR F hFs b)) =
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b) := by
  apply vekua_series_Dbar_primitive
  intro j
  let q : L2Z := ((localConformalHardyPrimitive hR F hFs) ^ j) b
  let u : NeumannH1 (F '' ball (0 : ℂ) 1) :=
    localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
      (localConformalHardyPrimitive hR F hFs q)
  let v : NeumannH1 (F '' ball (0 : ℂ) 1) :=
    localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes q
  have hq : IsNonpositiveFourierSupport q :=
    localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j
  have hprimitive : h1WirtingerDbar (F '' ball (0 : ℂ) 1) u =
      h1Value (F '' ball (0 : ℂ) 1) v :=
    localConformalHardyH1Extension_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes q hq
  exact vekua_mapped_equality
    (fun x : L2 (F '' ball (0 : ℂ) 1) =>
      (neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) ^ j) x)
    (h1WirtingerDbar_affine_pow hb p u j) hprimitive
    (h1Value_neumannH1AffineMultiplier_pow hb p v j)

/-- The genuine physical H¹ Vekua series satisfies the compact-test
Helmholtz equation at every complex energy on nonpositive normalized input. -/
theorem localConformalVekuaH1_weakHelmholtz (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) {φ : ℂ → ℂ}
    (hφ : TestFunction (F '' ball (0 : ℂ) 1) φ) :
    (∫ z in F '' ball (0 : ℂ) 1,
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b) z *
          (lap φ z + E * φ z)) = 0 := by
  have hu : h1WirtingerD (F '' ball (0 : ℂ) 1)
      (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b) =
      h1Value (F '' ball (0 : ℂ) 1) ((-E / 4) •
        localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E
          (localConformalHardyPrimitive hR F hFs b)) := by
    rw [map_smul]
    exact localConformalVekuaH1_wirtingerD hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b
  have hv : h1WirtingerDbar (F '' ball (0 : ℂ) 1) ((-E / 4) •
      localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E
        (localConformalHardyPrimitive hR F hFs b)) =
      (-E / 4) • h1Value (F '' ball (0 : ℂ) 1)
        (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b) := by
    rw [map_smul, localConformalVekuaH1_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b hbn]
  have h := h1_weak_helmholtz_of_wirtinger_factorization _ _ (-E / 4) hu hv hφ
  have heq (z : ℂ) : lap φ z - 4 * (-E / 4) * φ z = lap φ z + E * φ z := by ring
  simpa only [heq] using h

end PhysicalCoordinates

end PolyaNeumann

end
