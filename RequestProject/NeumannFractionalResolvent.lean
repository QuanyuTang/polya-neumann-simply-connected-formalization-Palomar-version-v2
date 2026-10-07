module

public import RequestProject.DiskHalfTrace
public import RequestProject.NeumannBoundaryDifference
public import RequestProject.NeumannResidueRank

/-!
# Fractional Neumann boundary resolvents from the actual half-order trace

`boundaryFourier` is unitary for ordinary `dθ`. If `λₙ = 1 + |n|`, a
physical negative-half-order conormal density has normalized coordinates
`bₙ = λₙ^(-1/2) sqrt(2π) averageFourierCoeff(g)(n)`. A Dirichlet value has
positive-half-order coordinates `λₙ^(1/2) sqrt(2π) averageFourierCoeff(f)(n)`.
The dual pairing is therefore the unscaled `ℓ²` pairing.

The auxiliary `H1HalfBoundaryTrace` requires a bounded map with precisely
these coordinates of the constructed physical trace. Its existence on a
general domain is not asserted here. The proved disk trace gives a concrete
instance without a trace hypothesis. All resolvents below use the actual
weak Helmholtz form; compact energy differences use the interior mass
operator, rather than a compactness assumption on the half-order trace.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Filter Topology Metric
open scoped Real InnerProductSpace

/-- The existing bounded multiplier `Λ^(-1/2)`. It converts positive-half
Dirichlet coordinates to ordinary Fourier coordinates, and ordinary
conormal coordinates to negative-half coordinates. -/
def halfBoundarySmoothing : L2Z →L[ℂ] L2Z :=
  sobolevSmoothing (1 / 2 : ℝ) (by norm_num)

@[simp] theorem halfBoundarySmoothing_apply (b : L2Z) (n : ℤ) :
    halfBoundarySmoothing b n = (Real.sqrt (sobWeight n) : ℂ)⁻¹ * b n := by
  simp only [halfBoundarySmoothing, sobolevSmoothing, diagOp_apply,
    Real.rpow_neg (sobWeight_pos n).le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]

theorem halfBoundarySmoothing_isSelfAdjoint : IsSelfAdjoint halfBoundarySmoothing := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [halfBoundarySmoothing_apply, RCLike.inner_apply', map_mul, map_inv₀,
    Complex.conj_ofReal]
  ring

@[simp] theorem halfBoundarySmoothing_adjoint :
    ContinuousLinearMap.adjoint halfBoundarySmoothing = halfBoundarySmoothing :=
  halfBoundarySmoothing_isSelfAdjoint.adjoint_eq

theorem halfBoundarySmoothing_injective : Function.Injective halfBoundarySmoothing := by
  intro x y hxy
  apply lp.ext
  funext n
  have hn : (Real.sqrt (sobWeight n) : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos n)).ne'
  have h := congrArg (fun b : L2Z => b n) hxy
  simp only [halfBoundarySmoothing_apply] at h
  exact mul_left_cancel₀ hn h

/-- Ordinary L² conormal densities are dense in the full negative-half
space, in the actual normalized Fourier coordinates. -/
theorem halfBoundarySmoothing_denseRange : DenseRange halfBoundarySmoothing := by
  change Dense (halfBoundarySmoothing.range : Set L2Z)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range,
    halfBoundarySmoothing_adjoint]
  exact LinearMap.ker_eq_bot.mpr halfBoundarySmoothing_injective

theorem halfBoundaryPhysicalDensity_denseRange :
    DenseRange (fun g : BoundaryL2 => halfBoundarySmoothing (boundaryFourier g)) :=
  halfBoundarySmoothing_denseRange.comp boundaryFourier.surjective.denseRange
    halfBoundarySmoothing.continuous

/-- The ordinary Fourier coefficients of an arbitrary negative-half density,
decoded from its `ℓ²` Sobolev coordinates. They need not belong to `ℓ²`. -/
def halfBoundaryDensityCoeff (b : L2Z) (n : ℤ) : ℂ :=
  (Real.sqrt (sobWeight n) : ℂ) * b n

private theorem halfBoundaryDensityCoeff_weight (b : L2Z) (n : ℤ) :
    (sobWeight n ^ (-(1 / 2 : ℝ)) * ‖halfBoundaryDensityCoeff b n‖) ^ 2 =
      ‖b n‖ ^ 2 := by
  have hs : Real.sqrt (sobWeight n) ≠ 0 := (Real.sqrt_pos.mpr (sobWeight_pos n)).ne'
  rw [halfBoundaryDensityCoeff, norm_mul,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.rpow_neg (sobWeight_pos n).le, ← Real.sqrt_eq_rpow,
    ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- Every input coordinate vector is a genuine Fourier negative-half density. -/
theorem halfBoundaryDensityCoeff_isSobolevSeq (b : L2Z) :
    IsSobolevSeq (-(1 / 2 : ℝ)) (halfBoundaryDensityCoeff b) :=
  (summable_norm_sq_L2Z b).congr (fun n => (halfBoundaryDensityCoeff_weight b n).symm)

private theorem halfBoundarySmoothing_weight (b : L2Z) (n : ℤ) :
    (sobWeight n ^ (1 / 2 : ℝ) * ‖halfBoundarySmoothing b n‖) ^ 2 = ‖b n‖ ^ 2 := by
  have hs : Real.sqrt (sobWeight n) ≠ 0 := (Real.sqrt_pos.mpr (sobWeight_pos n)).ne'
  rw [halfBoundarySmoothing_apply, norm_mul, norm_inv,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_eq_rpow,
    ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- Decoding an output vector gives a genuine positive-half Dirichlet value. -/
theorem halfBoundarySmoothing_isSobolevSeq (b : L2Z) :
    IsSobolevSeq (1 / 2 : ℝ) (halfBoundarySmoothing b : ℤ → ℂ) :=
  (summable_norm_sq_L2Z b).congr (fun n => (halfBoundarySmoothing_weight b n).symm)

/-- Every existing negative-half Sobolev sequence has `ℓ²` coordinates;
the coordinate model therefore contains all densities, not only L² ones. -/
def halfBoundaryDensityCoordinates {g : ℤ → ℂ}
    (hg : IsSobolevSeq (-(1 / 2 : ℝ)) g) : L2Z :=
  ⟨fun n => (Real.sqrt (sobWeight n) : ℂ)⁻¹ * g n,
    memℓp_two_iff_summable.mpr (hg.congr (fun n => by
      rw [Real.rpow_neg (sobWeight_pos n).le, ← Real.sqrt_eq_rpow,
        norm_mul, norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]))⟩

theorem halfBoundaryDensityCoeff_coordinates {g : ℤ → ℂ}
    (hg : IsSobolevSeq (-(1 / 2 : ℝ)) g) (n : ℤ) :
    halfBoundaryDensityCoeff (halfBoundaryDensityCoordinates hg) n = g n := by
  have hs : (Real.sqrt (sobWeight n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos n)).ne'
  change (Real.sqrt (sobWeight n) : ℂ) *
    ((Real.sqrt (sobWeight n) : ℂ)⁻¹ * g n) = g n
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- Likewise every existing positive-half Sobolev value has all its
normalized coordinates in `ℓ²`. -/
def halfBoundaryValueCoordinates {f : ℤ → ℂ}
    (hf : IsSobolevSeq (1 / 2 : ℝ) f) : L2Z :=
  ⟨fun n => (Real.sqrt (sobWeight n) : ℂ) * f n,
    memℓp_two_iff_summable.mpr (hf.congr (fun n => by
      rw [← Real.sqrt_eq_rpow, norm_mul,
        Complex.norm_of_nonneg (Real.sqrt_nonneg _)]))⟩

theorem halfBoundarySmoothing_valueCoordinates {f : ℤ → ℂ}
    (hf : IsSobolevSeq (1 / 2 : ℝ) f) (n : ℤ) :
    halfBoundarySmoothing (halfBoundaryValueCoordinates hf) n = f n := by
  have hs : (Real.sqrt (sobWeight n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos n)).ne'
  rw [halfBoundarySmoothing_apply]
  change (Real.sqrt (sobWeight n) : ℂ)⁻¹ *
    ((Real.sqrt (sobWeight n) : ℂ) * f n) = f n
  rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem halfBoundaryDensityCoeff_sobNormSq (b : L2Z) :
    sobNormSq (-(1 / 2 : ℝ)) (halfBoundaryDensityCoeff b) = ‖b‖ ^ 2 := by
  simp only [sobNormSq, halfBoundaryDensityCoeff_weight]
  exact (norm_sq_L2Z b).symm

theorem halfBoundarySmoothing_sobNormSq (b : L2Z) :
    sobNormSq (1 / 2 : ℝ) (halfBoundarySmoothing b : ℤ → ℂ) = ‖b‖ ^ 2 := by
  simp only [sobNormSq, halfBoundarySmoothing_weight]
  exact (norm_sq_L2Z b).symm

/-- For an actual L² density the negative-half coordinates decode to its
ordinary-`dθ` orthonormal Fourier coefficients, with the precise `sqrt(2π)` factor. -/
theorem halfBoundaryDensityCoeff_actual (g : BoundaryL2) (n : ℤ) :
    halfBoundaryDensityCoeff (halfBoundarySmoothing (boundaryFourier g)) n =
      (√(2 * π) : ℂ) *
        fourierCoeffOn Real.two_pi_pos (g : ℝ → ℂ) n := by
  have hs : (Real.sqrt (sobWeight n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos n)).ne'
  rw [halfBoundaryDensityCoeff, halfBoundarySmoothing_apply, ← mul_assoc,
    mul_inv_cancel₀ hs, one_mul, boundaryFourier_apply]

/-- An auxiliary bounded half-order trace, tied coefficient by coefficient
to the already constructed actual boundary trace. A general domain instance
must be constructed from a proved trace estimate, not postulated in `main`. -/
structure H1HalfBoundaryTrace {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) where
  operator : NeumannH1 Ω →L[ℂ] L2Z
  coefficient_eq : ∀ (u : NeumannH1 Ω) (n : ℤ),
    operator u n = (Real.sqrt (sobWeight n) : ℂ) *
      boundaryFourier (h1BoundaryTrace hb hL hγ u) n

namespace H1HalfBoundaryTrace

variable {Ω : Set ℂ} {hb : Bornology.IsBounded Ω} {hL : IsLipschitzDomain Ω}
  {γ : ℝ → ℂ} {hγ : IsBoundaryParam Ω γ} (Q : H1HalfBoundaryTrace hb hL hγ)

theorem smoothing_apply (u : NeumannH1 Ω) :
    halfBoundarySmoothing (Q.operator u) = boundaryFourier (h1BoundaryTrace hb hL hγ u) := by
  apply lp.ext
  funext n
  have hs : (Real.sqrt (sobWeight n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos n)).ne'
  rw [halfBoundarySmoothing_apply, Q.coefficient_eq, ← mul_assoc,
    inv_mul_cancel₀ hs, one_mul]

theorem smoothing_comp :
    halfBoundarySmoothing.comp Q.operator =
      (boundaryFourier : BoundaryL2 →L[ℂ] L2Z).comp (h1BoundaryTrace hb hL hγ) := by
  apply ContinuousLinearMap.ext
  intro u
  exact Q.smoothing_apply u

/-- The negative-half coordinates give the physical conormal load. -/
theorem adjoint_smoothing :
    (ContinuousLinearMap.adjoint Q.operator).comp halfBoundarySmoothing =
      (h1BoundaryLoad hb hL hγ).comp
        (boundaryFourier.symm : L2Z →L[ℂ] BoundaryL2) := by
  have h := congrArg ContinuousLinearMap.adjoint Q.smoothing_comp
  simpa only [ContinuousLinearMap.adjoint_comp, halfBoundarySmoothing_adjoint,
    boundaryFourier.adjoint_eq_symm, h1BoundaryLoad] using h

theorem adjoint_smoothing_apply (b : L2Z) :
    ContinuousLinearMap.adjoint Q.operator (halfBoundarySmoothing b) =
      h1BoundaryLoad hb hL hγ (boundaryFourier.symm b) :=
  congrArg (fun A : L2Z →L[ℂ] NeumannH1 Ω => A b) Q.adjoint_smoothing

theorem adjoint_actual_density (g : BoundaryL2) :
    ContinuousLinearMap.adjoint Q.operator
      (halfBoundarySmoothing (boundaryFourier g)) = h1BoundaryLoad hb hL hγ g := by
  rw [Q.adjoint_smoothing_apply, boundaryFourier.symm_apply_apply]

end H1HalfBoundaryTrace

/-- The auxiliary trace has an actual unit-disk instance, using the harmonic
Fourier--Green estimate proved in `DiskHalfTrace`. -/
def diskHalfBoundaryTrace :
    H1HalfBoundaryTrace unitDisk_bounded isLipschitzDomain_unitDisk
      unitCircle_isBoundaryParam where
  operator := diskHalfTrace
  coefficient_eq u n := by
    simpa only [sobWeight, diskH1Trace] using diskHalfTrace_apply u n

section FractionalResolvent

variable {Ω : Set ℂ} {hb : Bornology.IsBounded Ω} {hL : IsLipschitzDomain Ω}
  {γ : ℝ → ℂ} {hγ : IsBoundaryParam Ω γ} (Q : H1HalfBoundaryTrace hb hL hγ)

/-- Sandwich an actual interior operator between the true half-order trace
and its adjoint. -/
def halfBoundarySandwich (R : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) : L2Z →L[ℂ] L2Z :=
  Q.operator ∘L R ∘L ContinuousLinearMap.adjoint Q.operator

/-- The full ordinary-L² coordinate identity, proved from the actual trace
compatibility. This also applies to regular inverses and projections. -/
theorem halfBoundarySandwich_smoothing (R : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) :
    halfBoundarySmoothing ∘L halfBoundarySandwich Q R ∘L halfBoundarySmoothing =
      boundaryFourierConjugate
        (h1BoundaryTrace hb hL hγ ∘L R ∘L h1BoundaryLoad hb hL hγ) := by
  apply ContinuousLinearMap.ext
  intro b
  change halfBoundarySmoothing
    (Q.operator (R (ContinuousLinearMap.adjoint Q.operator (halfBoundarySmoothing b)))) =
      boundaryFourier
        (h1BoundaryTrace hb hL hγ (R (h1BoundaryLoad hb hL hγ (boundaryFourier.symm b))))
  rw [Q.adjoint_smoothing_apply, Q.smoothing_apply]

theorem halfBoundarySandwich_isSelfAdjoint
    (R : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) (hR : IsSelfAdjoint R) :
    IsSelfAdjoint (halfBoundarySandwich Q R) := hR.conj_adjoint Q.operator

/-- The negative-half-order Poisson solution of the actual weak form. -/
def neumannHalfBoundaryPoisson (E : ℝ) : L2Z →L[ℂ] NeumannH1 Ω :=
  (h1HelmholtzResolvent Ω E).comp (ContinuousLinearMap.adjoint Q.operator)

/-- The true fractional NtD operator in negative-/positive-half Hilbert
coordinates. Its physical output coefficients are obtained by `Λ^(-1/2)`. -/
def neumannToDirichletHalf (E : ℝ) : L2Z →L[ℂ] L2Z :=
  halfBoundarySandwich Q (h1HelmholtzResolvent Ω E)

/-- The actual weak equation, tested against every genuine H¹ vector. The
right side is the negative-/positive-half physical boundary dual pairing. -/
def IsHalfBoundaryNeumannSolution (E : ℝ) (b : L2Z) (u : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      (E : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ = ⟪Q.operator v, b⟫_ℂ

theorem isHalfBoundaryNeumannSolution_iff_form_eq (E : ℝ) (b : L2Z) (u : NeumannH1 Ω) :
    IsHalfBoundaryNeumannSolution Q E b u ↔
      h1HelmholtzForm Ω E u = ContinuousLinearMap.adjoint Q.operator b := by
  constructor
  · intro hu
    apply ext_inner_left ℂ
    intro v
    rw [h1HelmholtzForm_inner, ContinuousLinearMap.adjoint_inner_right]
    exact hu v
  · intro hu v
    rw [← h1HelmholtzForm_inner, hu, ContinuousLinearMap.adjoint_inner_right]

/-- On actual L² densities the fractional equation is exactly the original
physical equation, not a different boundary model. -/
theorem isHalfBoundaryNeumannSolution_actual_density (E : ℝ) (g : BoundaryL2)
    (u : NeumannH1 Ω) :
    IsHalfBoundaryNeumannSolution Q E (halfBoundarySmoothing (boundaryFourier g)) u ↔
      IsBoundaryNeumannSolution hb hL hγ E g u := by
  rw [isHalfBoundaryNeumannSolution_iff_form_eq,
    isBoundaryNeumannSolution_iff_form_eq, Q.adjoint_actual_density]

theorem neumannHalfBoundaryPoisson_isSolution {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (b : L2Z) :
    IsHalfBoundaryNeumannSolution Q E b (neumannHalfBoundaryPoisson Q E b) := by
  apply (isHalfBoundaryNeumannSolution_iff_form_eq Q E b _).2
  change h1HelmholtzForm Ω E
    (Ring.inverse (h1HelmholtzForm Ω E) (ContinuousLinearMap.adjoint Q.operator b)) = _
  rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hE,
    ContinuousLinearMap.one_apply]

theorem existsUnique_halfBoundaryNeumannSolution {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (b : L2Z) :
    ∃! u : NeumannH1 Ω, IsHalfBoundaryNeumannSolution Q E b u := by
  have hsol := neumannHalfBoundaryPoisson_isSolution Q hE b
  refine ⟨neumannHalfBoundaryPoisson Q E b, hsol, ?_⟩
  intro u hu
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hE).1
  rw [(isHalfBoundaryNeumannSolution_iff_form_eq Q E b u).1 hu,
    (isHalfBoundaryNeumannSolution_iff_form_eq Q E b _).1 hsol]

/-- An actual L² conormal density produces precisely the already constructed
physical Poisson solution. -/
theorem neumannHalfBoundaryPoisson_actual_density (E : ℝ) (g : BoundaryL2) :
    neumannHalfBoundaryPoisson Q E (halfBoundarySmoothing (boundaryFourier g)) =
      neumannBoundaryPoisson hb hL hγ E g := by
  change h1HelmholtzResolvent Ω E
    (ContinuousLinearMap.adjoint Q.operator (halfBoundarySmoothing (boundaryFourier g))) = _
  rw [Q.adjoint_actual_density]
  rfl

theorem neumannToDirichletHalf_smoothing (E : ℝ) :
    halfBoundarySmoothing ∘L neumannToDirichletHalf Q E ∘L halfBoundarySmoothing =
      boundaryFourierConjugate (neumannToDirichletL2 hb hL hγ E) :=
  halfBoundarySandwich_smoothing Q (h1HelmholtzResolvent Ω E)

theorem neumannToDirichletHalf_isSelfAdjoint (E : ℝ) :
    IsSelfAdjoint (neumannToDirichletHalf Q E) :=
  halfBoundarySandwich_isSelfAdjoint Q _ (h1HelmholtzResolvent_isSelfAdjoint Ω E)

/-- The exact two-energy identity contains the real compact interior mass
operator between the two actual inverses, in the correct order. -/
theorem neumannToDirichletHalf_sub {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (hF : IsUnit (h1HelmholtzForm Ω F)) :
    neumannToDirichletHalf Q E - neumannToDirichletHalf Q F =
      ((E - F : ℝ) : ℂ) •
        (Q.operator ∘L h1HelmholtzResolvent Ω E ∘L h1MassOperator Ω ∘L
          h1HelmholtzResolvent Ω F ∘L ContinuousLinearMap.adjoint Q.operator) := by
  have h := congrArg (fun R : NeumannH1 Ω →L[ℂ] NeumannH1 Ω =>
    Q.operator ∘L R ∘L ContinuousLinearMap.adjoint Q.operator)
    (h1HelmholtzResolvent_sub Ω hE hF)
  simpa only [neumannToDirichletHalf, halfBoundarySandwich,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_assoc] using h

/-- The fractional energy difference is compact without requiring the
half-order trace itself to be compact. -/
theorem neumannToDirichletHalf_sub_isCompactOperator {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (hF : IsUnit (h1HelmholtzForm Ω F)) :
    IsCompactOperator (neumannToDirichletHalf Q E - neumannToDirichletHalf Q F) := by
  change IsCompactOperator
    ((Q.operator ∘L h1HelmholtzResolvent Ω E ∘L ContinuousLinearMap.adjoint Q.operator) -
      (Q.operator ∘L h1HelmholtzResolvent Ω F ∘L ContinuousLinearMap.adjoint Q.operator))
  rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  exact ((h1HelmholtzResolvent_sub_isCompactOperator hb hL hE hF).comp_clm
    (ContinuousLinearMap.adjoint Q.operator)).clm_comp Q.operator

@[simp] theorem neumannToDirichletHalf_neg_one :
    neumannToDirichletHalf Q (-1) = Q.operator.comp (ContinuousLinearMap.adjoint Q.operator) := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [neumannToDirichletHalf, halfBoundarySandwich,
    h1HelmholtzResolvent_neg_one, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply]

theorem neumannToDirichletHalf_sub_reference_isCompactOperator {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) :
    IsCompactOperator (neumannToDirichletHalf Q E -
      Q.operator.comp (ContinuousLinearMap.adjoint Q.operator)) := by
  simpa only [neumannToDirichletHalf_neg_one] using
    neumannToDirichletHalf_sub_isCompactOperator Q hE (h1HelmholtzForm_neg_one_isUnit Ω)

/-- The actual fractional boundary residue, with the shifted-H¹ factor. -/
def neumannHalfBoundaryResidue (E₀ : ℝ) : L2Z →L[ℂ] L2Z :=
  ((E₀ + 1 : ℝ) : ℂ) • halfBoundarySandwich Q (h1ResonantSpace Ω E₀).starProjection

/-- The actual fractional regular boundary map, including the reference
energy itself. -/
def neumannHalfBoundaryRegular (E₀ E : ℝ) : L2Z →L[ℂ] L2Z :=
  halfBoundarySandwich Q (h1RegularResolvent Ω E₀ E)

/-- The actual resonance trace in positive-half Fourier coordinates. -/
def neumannHalfResonantTrace (E : ℝ) : h1ResonantSpace Ω E →L[ℂ] L2Z :=
  Q.operator.comp (h1ResonantSpace Ω E).subtypeL

/-- The half-order trace retains every actual Neumann resonance vector:
smoothing gives the proved injective ordinary boundary trace. -/
theorem neumannHalfResonantTrace_injective {E : ℝ} (hE : 0 ≤ E) :
    Function.Injective (neumannHalfResonantTrace Q E) := by
  intro u v huv
  apply neumannResonantTrace_injective_nonneg hb hL hγ hE
  apply boundaryFourier.injective
  change Q.operator (u : NeumannH1 Ω) = Q.operator (v : NeumannH1 Ω) at huv
  exact (Q.smoothing_apply (u : NeumannH1 Ω)).symm.trans
    ((congrArg halfBoundarySmoothing huv).trans (Q.smoothing_apply (v : NeumannH1 Ω)))

theorem neumannHalfBoundaryResidue_eq_trace_gram (E : ℝ) :
    neumannHalfBoundaryResidue Q E = ((E + 1 : ℝ) : ℂ) •
      ((neumannHalfResonantTrace Q E).comp
        (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := h1ResonantSpace Ω E)
          (F := L2Z) (neumannHalfResonantTrace Q E))) := by
  simp only [neumannHalfResonantTrace, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, neumannHalfBoundaryResidue, halfBoundarySandwich,
    Submodule.starProjection, ContinuousLinearMap.comp_assoc]

/-- The fractional residue has precisely the range of the actual
resonance traces, including at energy zero. -/
theorem neumannHalfBoundaryResidue_range_eq {E : ℝ} (hE : 0 ≤ E) :
    (neumannHalfBoundaryResidue Q E).range = (neumannHalfResonantTrace Q E).range := by
  haveI := finiteDimensional_h1ResonantSpace hb hL E
  have hc : ((E + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show E + 1 ≠ 0 by linarith)
  exact range_scaled_projected_trace_gram (h1ResonantSpace Ω E)
    Q.operator (neumannHalfResonantTrace_injective Q hE) hc

theorem neumannHalfBoundaryResidue_finrank_eq {E : ℝ} (hE : 0 ≤ E) :
    Module.finrank ℂ (neumannHalfBoundaryResidue Q E).range =
      Module.finrank ℂ (h1ResonantSpace Ω E) := by
  rw [neumannHalfBoundaryResidue_range_eq Q hE]
  exact LinearMap.finrank_range_of_inj (neumannHalfResonantTrace_injective Q hE)

/-- Fractional normalization preserves the multiplicity of the original
variational Neumann sequence. -/
theorem neumannHalfBoundaryResidue_multiplicity_eq {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (neumannHalfBoundaryResidue Q E).range : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  rw [neumannHalfBoundaryResidue_finrank_eq Q hE]
  exact h1ResonantSpace_multiplicity_eq hb hL hE

theorem neumannHalfBoundaryResidue_smoothing (E₀ : ℝ) :
    halfBoundarySmoothing ∘L neumannHalfBoundaryResidue Q E₀ ∘L halfBoundarySmoothing =
      boundaryFourierConjugate (neumannBoundaryResidue hb hL hγ E₀) := by
  have h := halfBoundarySandwich_smoothing Q
    (((E₀ + 1 : ℝ) : ℂ) • (h1ResonantSpace Ω E₀).starProjection)
  simpa only [halfBoundarySandwich, neumannHalfBoundaryResidue,
    neumannBoundaryResidue, boundaryFourierConjugate,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc] using h

theorem neumannHalfBoundaryRegular_smoothing (E₀ E : ℝ) :
    halfBoundarySmoothing ∘L neumannHalfBoundaryRegular Q E₀ E ∘L halfBoundarySmoothing =
      boundaryFourierConjugate (neumannBoundaryRegular hb hL hγ E₀ E) :=
  halfBoundarySandwich_smoothing Q (h1RegularResolvent Ω E₀ E)

theorem finiteDimensional_range_neumannHalfBoundaryResidue (E₀ : ℝ) :
    FiniteDimensional ℂ (neumannHalfBoundaryResidue Q E₀).range := by
  haveI := finiteDimensional_h1ResonantSpace hb hL E₀
  let T : h1ResonantSpace Ω E₀ →L[ℂ] L2Z :=
    Q.operator.comp (h1ResonantSpace Ω E₀).subtypeL
  haveI : FiniteDimensional ℂ T.range := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := T.range)
  rintro _ ⟨b, rfl⟩
  refine ⟨((E₀ + 1 : ℝ) : ℂ) •
    (h1ResonantSpace Ω E₀).orthogonalProjection (ContinuousLinearMap.adjoint Q.operator b), ?_⟩
  calc
    _ = ((E₀ + 1 : ℝ) : ℂ) •
        T ((h1ResonantSpace Ω E₀).orthogonalProjection
          (ContinuousLinearMap.adjoint Q.operator b)) := map_smul T _ _
    _ = _ := rfl

theorem continuousOn_neumannHalfBoundaryRegular {E₀ : ℝ} {U : Set ℝ}
    (hi : ContinuousOn (fun E => Ring.inverse (h1ComplementForm Ω E₀ E)) U) :
    ContinuousOn (neumannHalfBoundaryRegular Q E₀) U :=
  continuousOn_const.clm_comp ((continuousOn_h1RegularResolvent hi).clm_comp continuousOn_const)

/-- Exact fractional pole stripping follows from the actual interior pole
identity. No singular boundary inverse or principal part is assumed. -/
theorem neumannToDirichletHalf_eq_pole_add_regular {E₀ E : ℝ}
    (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀) (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    neumannToDirichletHalf Q E =
      (-((E - E₀ : ℝ) : ℂ)⁻¹) • neumannHalfBoundaryResidue Q E₀ +
        neumannHalfBoundaryRegular Q E₀ E := by
  apply ContinuousLinearMap.ext
  intro b
  change Q.operator (h1HelmholtzResolvent Ω E (ContinuousLinearMap.adjoint Q.operator b)) = _
  rw [h1HelmholtzResolvent_eq_pole_add_regular hb hL hE₀ hne hunit]
  simp only [neumannHalfBoundaryResidue, neumannHalfBoundaryRegular, halfBoundarySandwich,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_add, map_smul, smul_smul]
  have hs : -(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ)) =
      (-((E - E₀ : ℝ) : ℂ)⁻¹) * ((E₀ + 1 : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    ring
  rw [hs]

/-- The local statement uses only the constructed half-order trace. Every
interior invertibility and continuity assertion is already proved from
Rellich compactness and the genuine Fredholm alternative. -/
theorem exists_neumannHalfBoundary_pole_near {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    ∃ U ∈ 𝓝 E₀,
      ContinuousOn (neumannHalfBoundaryRegular Q E₀) U ∧
      FiniteDimensional ℂ (neumannHalfBoundaryResidue Q E₀).range ∧
      ∀ E ∈ U, E ≠ E₀ → neumannToDirichletHalf Q E =
        (-((E - E₀ : ℝ) : ℂ)⁻¹) • neumannHalfBoundaryResidue Q E₀ +
          neumannHalfBoundaryRegular Q E₀ E := by
  obtain ⟨U, hU, hunit, hi⟩ := h1ComplementForm_isUnit_near hb hL hE₀
  exact ⟨U, hU, continuousOn_neumannHalfBoundaryRegular Q hi,
    finiteDimensional_range_neumannHalfBoundaryResidue Q E₀,
    fun E hEU hne => neumannToDirichletHalf_eq_pole_add_regular Q hE₀ hne (hunit E hEU)⟩

end FractionalResolvent

end PolyaNeumann

end
